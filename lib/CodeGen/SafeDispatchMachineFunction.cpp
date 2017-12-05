#include <llvm/Support/FileSystem.h>
#include "llvm/CodeGen/SafeDispatchMachineFunction.h"

using namespace llvm;

static std::string findOutputFileName(const Module *M) {
  auto SDOutputMD = M->getNamedMetadata("sd_output");
  auto SDFilenameMD = M->getNamedMetadata("sd_filename");

  StringRef OutputPath;
  if (SDOutputMD != nullptr)
    OutputPath = dyn_cast_or_null<MDString>(SDOutputMD->getOperand(0)->getOperand(0))->getString();
  else if (SDFilenameMD != nullptr)
    OutputPath = ("./" + dyn_cast_or_null<MDString>(SDFilenameMD->getOperand(0)->getOperand(0))->getString()).str();

  std::string FileName = "./SDBackend";
  if (OutputPath != "") {
    FileName = (OutputPath + "-Backend").str();
  }

  std::string FileNameExtended = (Twine(FileName) + ".csv").str();
  if (sys::fs::exists(FileNameExtended)) {
    uint number = 1;
    while (sys::fs::exists(FileName + Twine(number) + ".csv")) {
      number++;
    }
    FileNameExtended = (FileName + Twine(number) + ".csv").str();
  }

  return FileNameExtended;
};


bool SDMachineFunction::runOnMachineFunction(MachineFunction &MF)  {
  // Enable SDMachineFunction pass?
  if (SkipPass)
    return false;

  if (M == nullptr) {
    M = MF.getMMI().getModule();

    int VirtualLoaded = loadVirtualCallSiteData();
    int StaticLoaded = loadStaticCallSiteData();

    if (VirtualLoaded == 0 && StaticLoaded == 0) {
      sdLog::stream() << "No CallSites loaded.\n";
      SkipPass = true;
      return false;
    }

    sdLog::stream() << "Loaded virtual CallSites: " << VirtualLoaded << "\n";
    sdLog::stream() << "Loaded static CallSites: " << StaticLoaded << "\n";
  }

  sdLog::log() << "Running SDMachineFunction pass: "<< MF.getName() << "\n";

  const TargetInstrInfo* TII = MF.getSubtarget().getInstrInfo();
  //We would get NamedMetadata like this:
  //const auto &M = MF.getMMI().getModule();
  //const auto &MD = M->getNamedMetadata("sd.class_info._ZTV1A");
  //MD->dump();

  for (auto &MBB: MF) {
    for (auto &MI : MBB) {
      if (MI.isCall()) {
        // Try to find our annotation.
        if (MI.getDebugLoc()) {
          std::string debugLocString = debugLocToString(MI.getDebugLoc());

          if (!processVirtualCallSite(debugLocString, MI, MBB, TII)) {
            if (!processStaticCallSite(debugLocString, MI, MBB, TII)) {
              processUnknownCallSite(debugLocString, MI, MBB, TII);
            }
          }
        } else {
          std::string NoDebugLoc = "N/A";
          processUnknownCallSite(NoDebugLoc, MI, MBB, TII);
        }
      }
    }
  }

  sdLog::log() << "Finished SDMachineFunction pass: "<< MF.getName() << "\n";
  return true;
}

bool SDMachineFunction::processVirtualCallSite(std::string &DebugLocString,
                                               MachineInstr &MI,
                                               MachineBasicBlock &MBB,
                                               const TargetInstrInfo *TII) {
  auto FunctionNameIt = CallSiteDebugLocVirtual.find(DebugLocString);
  if (FunctionNameIt == CallSiteDebugLocVirtual.end()) {
    return false;
  }

  auto FunctionName = FunctionNameIt->second;
  sdLog::log() << "Machine CallInst (@" << DebugLocString << ")"
               << " in " << MBB.getParent()->getName()
               << " is virtual Caller for " << FunctionName << "\n";

  auto range = CallSiteRange.find(DebugLocString);
  if (range == CallSiteRange.end()) {
    sdLog::errs() << DebugLocString << " has not Range!\n";
    return false;
  }
  uint64_t min = range->second.first;
  uint64_t width = range->second.second - min;


  RangeWidths.push_back(width);
  for (int64_t i = min; i <= range->second.second; ++i) {
    IDCount[i]++;
  }

  TII->insertNoop(MBB, MI.getNextNode());
  MI.getNextNode()->operands_begin()[3].setImm(width | 0x80000);
  TII->insertNoop(MBB, MI.getNextNode());
  MI.getNextNode()->operands_begin()[3].setImm(min | 0x80000);

  ++NumberOfVirtual;
  return true;
}

bool SDMachineFunction::processStaticCallSite(std::string &DebugLocString,
                                              MachineInstr &MI,
                                              MachineBasicBlock &MBB,
                                              const TargetInstrInfo *TII) {
  auto FunctionNameIt = CallSiteDebugLocStatic.find(DebugLocString);
  if (FunctionNameIt == CallSiteDebugLocStatic.end()) {
    return false;
  }

  auto FunctionName = FunctionNameIt->second;
  sdLog::log() << "Machine CallInst (@" << DebugLocString << ")"
               << " in " << MBB.getParent()->getName()
               << " is static Caller for " << FunctionName << "\n";

  if (StringRef(FunctionName).startswith("__INDIRECT__")) {
    uint64_t ID = CallSiteID[DebugLocString];
    TII->insertNoop(MBB, MI.getNextNode());
    MI.getNextNode()->operands_begin()[3].setImm(ID | 0x80000);
    IDCount[ID]++;
    ++NumberOfIndirect;
    return true;
  }

  if (FunctionName == "__TAIL__") {
    return true;
    TII->insertNoop(MBB, MI.getNextNode());
    MI.getNextNode()->operands_begin()[3].setImm(tailID);
    IDCount[tailID]++;
    ++NumberOfTail;
    return true;
  }

  uint64_t ID = CallSiteID[DebugLocString];
  TII->insertNoop(MBB, MI.getNextNode());
  MI.getNextNode()->operands_begin()[3].setImm(ID | 0x80000);
  IDCount[ID]++;
  ++NumberOfStaticDirect;
  return true;
}

bool SDMachineFunction::processUnknownCallSite(std::string &DebugLocString,
                                               MachineInstr &MI,
                                               MachineBasicBlock &MBB,
                                               const TargetInstrInfo *TII) {
  // Filter out std function and external function calls.
  if (MI.getNumOperands() > 0
      && !MI.getOperand(0).isGlobal()
      && !(MI.getOperand(0).getType() == MachineOperand::MO_ExternalSymbol)) {
    TII->insertNoop(MBB, MI.getNextNode());
    MI.getNextNode()->operands_begin()[3].setImm(unknownID);
    IDCount[unknownID]++;
    sdLog::warn() << "Machine CallInst (@" << DebugLocString << ") ";
    MI.print(sdLog::warn(), false);
    sdLog::warn() << " in " << MBB.getParent()->getName()
                  << " is an unknown Caller! \n";

    ++NumberOfUnknown;
    return true;
  }
  return false;
}

std::string SDMachineFunction::debugLocToString(const DebugLoc &Loc) {
  assert(Loc);

  std::stringstream Stream;
  auto *Scope = cast<MDScope>(Loc.getScope());
  Stream << Scope->getFilename().str() << ":" << Loc.getLine() << ":" << Loc.getCol();
  return Stream.str();
};

int SDMachineFunction::loadVirtualCallSiteData() {
  assert(M != nullptr && "Module not initialized!");
  auto MD = M->getNamedMetadata(SD_MD_RETUR_VIRTUAL);
  if (MD == nullptr)
    return 0;

  auto MetadataVector = dyn_cast<MDTuple>(MD->getOperand(0));

  std::string DebugLoc, ClassName, PreciseName, FunctionName;
  unsigned i = 0;
  while (i < MetadataVector->getNumOperands()) {
    StringRef Entry = dyn_cast<MDString>(MetadataVector->getOperand(i))->getString();
    SmallVector<StringRef, 6> Splits;
    Entry.split(Splits, ",");
    assert(Splits.size() >= 6);

    DebugLoc = Splits[0];
    ClassName = Splits[1];
    PreciseName = Splits[2];
    FunctionName = Splits[3];
    uint64_t min = std::stoul(Splits[4]);
    uint64_t max = std::stoul(Splits[5]);

    CallSiteDebugLocVirtual[DebugLoc] = FunctionName;
    CallSiteRange[DebugLoc] = {min, max};
    ++i;
  }

  MD->eraseFromParent();
  return i;
}

int SDMachineFunction::loadStaticCallSiteData() {
  assert(M != nullptr && "Module not initialized!");
  auto MD = M->getNamedMetadata(SD_MD_RETUR_NORMAL);
  if (MD == nullptr)
    return 0;

  auto MetadataVector = dyn_cast<MDTuple>(MD->getOperand(0));

  std::string DebugLoc, FunctionName, IDString;

  unsigned i = 0;
  while (i < MetadataVector->getNumOperands()) {
    StringRef Entry = dyn_cast<MDString>(MetadataVector->getOperand(i))->getString();
    SmallVector<StringRef, 3> Splits;
    Entry.split(Splits, ",");
    assert(Splits.size() >= 2);

    DebugLoc = Splits[0];
    FunctionName = Splits[1];
    if (Splits.size() > 2) {
      uint64_t ID = std::stoul(Splits[2]);
      CallSiteID[DebugLoc] = ID;
    }

    CallSiteDebugLocStatic[DebugLoc] = FunctionName;
    ++i;
  }

  MD->eraseFromParent();
  return i;
}

void SDMachineFunction::analyse(const Module *M) {
  uint64_t sum = 0;
  if (!RangeWidths.empty()) {
    for (uint64_t i : RangeWidths) {
      sum += i;
    }
    double avg = double(sum) / RangeWidths.size();
    sdLog::stream() << "AVG RANGE WIDTH: " << avg << "\n";
    sdLog::stream() << "TOTAL RANGES: " << RangeWidths.size() << "\n";
  }

  if (IDCount.empty())
    return;

  std::string outName = findOutputFileName(M);
  std::ofstream Outfile(outName);
  std::ostream_iterator <std::string> OutIterator(Outfile, "\n");
  for (auto &entry : IDCount) {
    Outfile << entry.first << "," << entry.second << "\n";
  }
  Outfile.close();
}

char SDMachineFunction::ID = 0;

INITIALIZE_PASS(SDMachineFunction, "sdMachinePass", "Get frontend infos.", false, true)

FunctionPass* llvm::createSDMachineFunctionPass() {
  return new SDMachineFunction();
}