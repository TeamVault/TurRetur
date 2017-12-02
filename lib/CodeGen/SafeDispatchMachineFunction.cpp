#include "llvm/CodeGen/SafeDispatchMachineFunction.h"

using namespace llvm;

bool SDMachineFunction::runOnMachineFunction(MachineFunction &MF)  {
  // Enable SDMachineFunction pass?
  if (MF.getMMI().getModule()->getNamedMetadata("SD_emit_return_labels") == nullptr)
    return false;

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
    TII->insertNoop(MBB, MI.getNextNode());
    uint64_t ID = CallSiteID[DebugLocString];
    MI.getNextNode()->operands_begin()[3].setImm(ID);
    ++IDCount[ID];
    ++NumberOfIndirect;
    return true;
  }

  if (FunctionName == "__TAIL__") {
    TII->insertNoop(MBB, MI.getNextNode());
    MI.getNextNode()->operands_begin()[3].setImm(tailID);
    ++IDCount[tailID];
    ++NumberOfTail;
    return true;
  }

  uint64_t ID = CallSiteID[DebugLocString];
  sdLog::log() << ID << "\n";
  //TII->insertNoop(MBB, MI.getNextNode());
  //MI.getNextNode()->operands_begin()[3].setImm(ID | 0x80000);
  ++IDCount[ID];
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

void SDMachineFunction::loadVirtualCallSiteData() {
  //TODO MATT: delete file
  std::ifstream InputFile("./SD_CallSitesVirtual");
  std::string InputLine;
  std::string DebugLoc, ClassName, PreciseName, FunctionName;
  std::string MinStr, MaxStr;

  int count = 0;
  while (std::getline(InputFile, InputLine)) {
    std::stringstream LineStream(InputLine);

    std::getline(LineStream, DebugLoc, ',');
    std::getline(LineStream, ClassName, ',');
    std::getline(LineStream, PreciseName, ',');
    std::getline(LineStream, FunctionName, ',');
    std::getline(LineStream, MinStr, ',');
    LineStream >> MaxStr;
    uint64_t min = std::stoul(MinStr);
    uint64_t max = std::stoul(MaxStr);
    CallSiteDebugLocVirtual[DebugLoc] = FunctionName;
    CallSiteRange[DebugLoc] = {min, max};
    ++count;
  }
  sdLog::stream() << "Loaded virtual CallSites: " << count << "\n";
}

void SDMachineFunction::loadStaticCallSiteData() {
  //TODO MATT: delete file
  std::ifstream InputFile("./SD_CallSitesStatic");
  std::string InputLine;
  std::string DebugLoc, FunctionName, IDString;

  int count = 0;
  while (std::getline(InputFile, InputLine)) {
    std::stringstream LineStream(InputLine);

    std::getline(LineStream, DebugLoc, ',');
    std::getline(LineStream, FunctionName, ',');
    LineStream >> IDString;
    if (IDString != "") {
      uint64_t ID = std::stoul(IDString);
      CallSiteID[DebugLoc] = ID;
    }
    CallSiteDebugLocStatic[DebugLoc] = FunctionName;
    ++count;
  }
  sdLog::stream() << "Loaded static CallSites: " << count << "\n";
}

void SDMachineFunction::analyse() {
  uint64_t sum = 0;
  if (!RangeWidths.empty()) {
    for (uint64_t i : RangeWidths) {
      sum += i;
    }
    double avg = double(sum) / RangeWidths.size();
    sdLog::stream() << "AVG RANGE WIDTH: " << avg << "\n";
    sdLog::stream() << "TOTAL RANGES: " << RangeWidths.size() << "\n";
  }

  int number = 0;
  std::string outName = ((Twine)("./SD_BackendStats" + std::to_string(number))).str();
  std::ifstream infile(outName);
  while(infile.good()) {
    number++;
    outName = ((Twine)("./SD_BackendStats" + std::to_string(number))).str();
    infile = std::ifstream(outName);
  }
  std::ofstream Outfile(outName);
  std::ostream_iterator <std::string> OutIterator(Outfile, "\n");
  for (auto &entry : IDCount) {
    Outfile << entry.first << "," << entry.second << "\n";
  }
}


char SDMachineFunction::ID = 0;

INITIALIZE_PASS(SDMachineFunction, "sdMachinePass", "Get frontend infos.", false, true)

FunctionPass* llvm::createSDMachineFunctionPass() {
  return new SDMachineFunction();
}