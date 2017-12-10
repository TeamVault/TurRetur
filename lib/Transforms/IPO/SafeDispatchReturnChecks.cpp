
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/MDBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Transforms/IPO.h"
#include "llvm/Transforms/IPO/SafeDispatchLogStream.h"
#include "llvm/Transforms/IPO/SafeDispatchMD.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include <fstream>
#include <set>
#include <map>

using namespace llvm;

namespace {

inline uint64_t sd_getNumberFromMDTuple(const MDOperand &op) {
  Metadata *md = op.get();
  assert(md);
  ConstantAsMetadata *cam = dyn_cast_or_null<ConstantAsMetadata>(md);
  assert(cam);
  ConstantInt *ci = dyn_cast<ConstantInt>(cam->getValue());
  assert(ci);

  return ci->getSExtValue();
}

std::string sd_getStringFromMDTuple(const MDOperand &op) {
  MDString *mds = dyn_cast_or_null<MDString>(op.get());
  assert(mds);

  return mds->getString().str();
}

Function *createPrintfPrototype(Module *module) {
  std::vector<llvm::Type *> argTypes;
  argTypes.push_back(Type::getInt8PtrTy(module->getContext()));

  llvm::FunctionType *printf_type = FunctionType::get(
          /* ret type: int32 */ llvm::Type::getInt32Ty(module->getContext()),
          /* args: int8* */ argTypes,
          /* var args */ true);

  return cast<Function>(module->getOrInsertFunction("printf", printf_type));
}

void createPrintCall(const std::string &FormatString,
                            std::vector<Value *> Args,
                            IRBuilder<> &builder,
                            Module *M) {
  GlobalVariable *formatStrGV = builder.CreateGlobalString(FormatString, "SafeDispatchFormatStr");
  ConstantInt *zero = builder.getInt32(0);
  ArrayRef<Value *> indices({zero, zero});
  Value *formatStringRef = builder.CreateGEP(nullptr, formatStrGV, indices);

  Args.insert(Args.begin(), formatStringRef);
  ArrayRef<Value *> ArgsRef = ArrayRef<Value *>(Args);

  Function *PrintProto = createPrintfPrototype(M);
  builder.CreateCall(PrintProto, ArgsRef);
}

std::string findOutputFileName(const Module *M) {
  auto SDOutputMD = M->getNamedMetadata("sd_output");
  auto SDFilenameMD = M->getNamedMetadata("sd_filename");

  StringRef OutputPath;
  if (SDOutputMD != nullptr)
    OutputPath = dyn_cast_or_null<MDString>(SDOutputMD->getOperand(0)->getOperand(0))->getString();
  else if (SDFilenameMD != nullptr)
    OutputPath = ("./" + dyn_cast_or_null<MDString>(SDFilenameMD->getOperand(0)->getOperand(0))->getString()).str();

  std::string FileName = "./SDStats";
  if (OutputPath != "") {
    FileName = (OutputPath + "-SDStats").str();
  }

  if (sys::fs::exists(FileName)) {
    uint number = 1;
    while (sys::fs::exists(FileName + Twine(number))) {
      number++;
    }
    FileName = (FileName + Twine(number)).str();
  }
  llvm::SmallString<256> AbsoluteFileName = {FileName};
  sys::fs::make_absolute(AbsoluteFileName);

  return AbsoluteFileName.str().str();
}

/**
 * Pass for generating the return address checks
 */
class SDReturnChecks : public ModulePass {
public:
  static char ID;

private:
  enum ProcessingInfoFlags {
    NoCaller, NoReturn, External
  };

  enum ProcessingInfoType {
    Static, Virtual, BlackListed, None
  };

  struct FunctionInfo {
    FunctionInfo() {
      Type = None;
    }

    std::string Name;
    std::set<ProcessingInfoFlags> Flags{};
    ProcessingInfoType Type;

    std::vector<uint64_t> IDs{};
    int64_t TypeID = -1;
    std::set<uint64_t> ExtraIDs{};

    unsigned NumberOfChecks = 0;
  };

  struct StaticFunctionInfo : FunctionInfo {
    StaticFunctionInfo() {
      Type = Static;
    }
  };

  struct BlackListedInfo : FunctionInfo {
    BlackListedInfo() {
      Type = BlackListed;
    }
  };

  struct VirtualFunctionInfo : FunctionInfo {
    VirtualFunctionInfo() {
      Type = Virtual;
    }
  };

  std::map<std::string, VirtualFunctionInfo> VirtualFunctions{};
  std::map<std::string, StaticFunctionInfo> StaticFunctions{};
  std::map<std::string, BlackListedInfo> BlackListedFunctions{};

public:
  SDReturnChecks() : ModulePass(ID) {
    sdLog::stream() << "initializing SDReturnChecks pass ...\n";
    initializeSDReturnChecksPass(*PassRegistry::getPassRegistry());
  }

  virtual ~SDReturnChecks() {
    sdLog::stream() << "deleting SDReturnChecks pass\n";
  }

  bool runOnModule(Module &M) override {
    sdLog::stream() << "P7b. Started the SDReturnChecks pass ..." << sdLog::newLine << "\n";

    loadFunctionData(M);

    sdLog::stream() << "Finished loading data.\n";

    // init statistics
    std::vector<FunctionInfo> FunctionsMarkedStatic;
    std::vector<FunctionInfo> FunctionsMarkedVirtual;
    std::vector<FunctionInfo> FunctionsMarkedExternal;
    std::vector<FunctionInfo> FunctionsMarkedNoReturn;
    std::vector<FunctionInfo> FunctionsMarkedBlackListed;

    int NumberOfTotalChecks = 0;
    int NumberOfFunctions = 0;
    for (auto &F : M) {

      // do processing
      FunctionInfo Info = processFunction(F);

      bool InfoValidatesNoChecks = false;
      switch (Info.Type) {
        case Static:
          FunctionsMarkedStatic.push_back(Info);
          break;
        case Virtual:
          FunctionsMarkedVirtual.push_back(Info);
          break;
        case BlackListed:
          FunctionsMarkedBlackListed.push_back(Info);
          InfoValidatesNoChecks = true;
          break;
        case None:
          llvm_unreachable("Function without Type");
      }

      for (auto &Entry : Info.Flags) {
        switch (Entry) {
          case External:
            FunctionsMarkedExternal.push_back(Info);
            InfoValidatesNoChecks = true;
            break;
          case NoReturn:
            FunctionsMarkedNoReturn.push_back(Info);
            InfoValidatesNoChecks = true;
            break;
          case NoCaller:
            break;
        }
      }

      if (Info.NumberOfChecks == 0 && !InfoValidatesNoChecks)
        sdLog::errs() << "Function: " << Info.Name << "has no checks but is not NoReturn, Blacklisted or External!\n";

      NumberOfTotalChecks += Info.NumberOfChecks;
      NumberOfFunctions++;
    }

    // print and store statistics
    sdLog::stream() << sdLog::newLine << "P7b. SDReturnAddress statistics:" << "\n";
    sdLog::stream() << "Total number of checks: " << NumberOfTotalChecks << "\n";
    sdLog::stream() << "\n";
    sdLog::stream() << "Total number of functions: " << NumberOfFunctions << "\n";
    sdLog::stream() << "Total number of static functions: " << FunctionsMarkedStatic.size() << "\n";
    sdLog::stream() << "Total number of virtual functions: " << FunctionsMarkedVirtual.size() << "\n";
    sdLog::stream() << "Total number of blacklisted functions: " << FunctionsMarkedBlackListed.size() << "\n";
    sdLog::stream() << "\n";
    sdLog::stream() << "Total number of external functions: " << FunctionsMarkedExternal.size() << "\n";
    sdLog::stream() << "Total number of functions without return: " << FunctionsMarkedNoReturn.size() << "\n";

    storeStatistics(M, NumberOfTotalChecks,
                    FunctionsMarkedStatic,
                    FunctionsMarkedVirtual,
                    FunctionsMarkedExternal,
                    FunctionsMarkedNoReturn,
                    FunctionsMarkedBlackListed);

    sdLog::stream() << sdLog::newLine << "P7b. Finished running the SDReturnAddress pass ..." << "\n";
    sdLog::blankLine();

    return NumberOfTotalChecks > 0;
  }

  FunctionInfo processFunction(Function &F) {
    auto BLPtr = BlackListedFunctions.find(F.getName());
    if (BLPtr != BlackListedFunctions.end()) {
      auto Info = BLPtr->second;
      Info.Type = BlackListed;
      return Info;
    }

    auto VirtualPtr = VirtualFunctions.find(F.getName());
    if (VirtualPtr != VirtualFunctions.end()) {
      auto Info = VirtualPtr->second;
      Info.NumberOfChecks = generateRangeChecks(F, Info);

      Info.Type = Virtual;
      if (Info.NumberOfChecks == 0) {
        Info.Flags.insert(NoReturn);
      }
      if (F.isDeclaration() || F.hasExternalLinkage() || F.hasExternalWeakLinkage()) {
        Info.Flags.insert(External);
      }
      return Info;
    }

    auto StaticPtr = StaticFunctions.find(F.getName());
    if (StaticPtr != StaticFunctions.end()) {
      StaticFunctionInfo Info = StaticPtr->second;
      Info.NumberOfChecks = generateCompareChecks(F, Info);

      Info.Type = Static;
      if (Info.NumberOfChecks == 0) {
        Info.Flags.insert(NoReturn);
      }
      if (F.isDeclaration() || F.hasExternalLinkage() || F.hasExternalWeakLinkage()) {
        Info.Flags.insert(External);
      }
      return Info;
    }

    BlackListedInfo NewInfo;
    NewInfo.Name = F.getName();
    NewInfo.Type = BlackListed;
    if (!F.getName().startswith("llvm")) {
      sdLog::warn() << F.getName() << " unknown function...\n";
    }
    return NewInfo;
  }

private:
  void loadFunctionData(const Module &M) {
    std::vector<MDNode*> StaticTuple, VirtualTuple, BlackListedTuple;

    for(auto &MD : M.named_metadata()) {
      if (MD.getName().startswith(SD_MD_FUNCINFO_NORMAL)) {
        StaticTuple.push_back(dyn_cast<MDNode>(MD.getOperand(0)));
      } else if (MD.getName().startswith(SD_MD_FUNCINFO_VIRTUAL)) {
        VirtualTuple.push_back(dyn_cast<MDNode>(MD.getOperand(0)));
      } else if (MD.getName().startswith(SD_MD_FUNCINFO_BLACKLIST)) {
        BlackListedTuple.push_back(dyn_cast<MDNode>(MD.getOperand(0)));
      }
    }

    for (auto &Entry : StaticTuple) {
      auto NumOfOperands = Entry->getNumOperands();

      StaticFunctionInfo Info;
      Info.Name = sd_getStringFromMDTuple(Entry->getOperand(0));

      if (NumOfOperands > 2) {
        Info.IDs.push_back(sd_getNumberFromMDTuple(Entry->getOperand(1)));
      }
      if (NumOfOperands > 3) {
        Info.TypeID = sd_getNumberFromMDTuple(Entry->getOperand(2));
      }
      StaticFunctions[Info.Name] =  Info;
    }

    for (auto &Entry : VirtualTuple) {
      auto NumOfOperands = Entry->getNumOperands();

      VirtualFunctionInfo Info;
      Info.Name = sd_getStringFromMDTuple(Entry->getOperand(0));

      if (NumOfOperands > 2) {
        uint64_t NumOfIDs = sd_getNumberFromMDTuple(Entry->getOperand(1));
        for (uint i = 1; i <= NumOfIDs; i++) {
          Info.IDs.push_back(sd_getNumberFromMDTuple(Entry->getOperand(1 + i)));
        }

        if (NumOfIDs + 2 < NumOfOperands) {
          Info.TypeID = sd_getNumberFromMDTuple(Entry->getOperand(2 + NumOfIDs));
        }
      }
      VirtualFunctions[Info.Name] =  Info;
    }

    for (auto &Entry : BlackListedTuple) {
      BlackListedInfo Info;
      Info.Name = sd_getStringFromMDTuple(Entry->getOperand(0));
      BlackListedFunctions[Info.Name] = Info;
    }
  }

  unsigned generateRangeChecks(Function &F, VirtualFunctionInfo &FunctionInfo) {
    if (FunctionInfo.IDs.size() == 0)
      return 0;

    if (FunctionInfo.IDs.size() > 1) {
      // Diamond detected
      sdLog::stream() << F.getName() << " has " << FunctionInfo.IDs.size() << " IDs!\n";
    }

    // Collect all return statements (usually just a single one) first.
    // We need to do this first, because inserting checks invalidates the Instruction-Iterator.
    std::vector<Instruction *> Returns;
    for (auto &B : F) {
      for (auto &I : B) {
        if (isa<ReturnInst>(I)) {
          Returns.push_back(&I);
        }
      }
    }

    Module *M = F.getParent();
    unsigned count = 0;
    for (auto RI : Returns) {
      // Inserting check before RI is executed.
      IRBuilder<> builder(RI);

      //Create 'returnaddress'-intrinsic call
      Function *ReturnAddressFunc = Intrinsic::getDeclaration(
              F.getParent(), Intrinsic::returnaddress);

      // Some constants we need
      ConstantInt *zero = builder.getInt32(0);
      ConstantInt *offsetFirstNOP = builder.getInt32(3);
      ConstantInt *offsetSecondNOP = builder.getInt32(3 + 7);
      auto int64Ty = Type::getInt64Ty(M->getContext());
      auto int32PtrTy = Type::getInt32PtrTy(M->getContext());

      // Get return address
      auto ReturnAddress = builder.CreateCall(ReturnAddressFunc, zero);

      // Load minID from first NOP (extract actual value using the bit mask)
      auto minPtr = builder.CreateGEP(ReturnAddress, offsetFirstNOP);
      auto min32Ptr = builder.CreatePointerCast(minPtr, int32PtrTy);
      auto minID = builder.CreateLoad(min32Ptr);

      // Load width from second NOP (extract actual value using the bit mask)
      auto widthPtr = builder.CreateGEP(ReturnAddress, offsetSecondNOP);
      auto width32Ptr = builder.CreatePointerCast(widthPtr, int32PtrTy);
      auto width = builder.CreateLoad(width32Ptr);

      // Build first check
      ConstantInt *IDValue = builder.getInt32(uint32_t(FunctionInfo.IDs[0]| 0x80000));
      auto diff = builder.CreateSub(IDValue, minID);
      auto check = builder.CreateICmpUGT(diff, width);

      // Branch to CheckFailed if the first range check fails
      MDBuilder MDB(F.getContext());
      TerminatorInst *CheckFailed = SplitBlockAndInsertIfThen(check, RI, true);
      BasicBlock *SuccessBlock = RI->getParent();

      // Prepare for additional checks
      BasicBlock *CurrentBlock = CheckFailed->getParent();
      CheckFailed->eraseFromParent();
      assert(CurrentBlock->empty() && "Current Block still contains Instructions!");

      // Create additional ID checks
      for (unsigned i = 1; i < FunctionInfo.IDs.size(); ++i) {
        // Build check
        builder.SetInsertPoint(CurrentBlock);
        CurrentBlock->setName("sd.range");
        IDValue = builder.getInt32(uint32_t(FunctionInfo.IDs[i] | 0x80000));
        diff = builder.CreateSub(IDValue, minID);
        check = builder.CreateICmpULE(diff, width);
        CurrentBlock = BasicBlock::Create(F.getContext(), "", CurrentBlock->getParent());
        builder.CreateCondBr(check, SuccessBlock, CurrentBlock);
      }

      if (F.hasAddressTaken() && FunctionInfo.TypeID != -1) {
        // Handle external call case
        //TODO MATT: fix constant for external call
        builder.SetInsertPoint(CurrentBlock);
        CurrentBlock->setName("sd.external");
        ConstantInt *memRange = builder.getInt64(0x2000000);
        auto returnAddressAsInt = builder.CreatePtrToInt(ReturnAddress, int64Ty);
        auto checkExternal = builder.CreateICmpUGT(returnAddressAsInt, memRange);
        CurrentBlock = BasicBlock::Create(F.getContext(), "", CurrentBlock->getParent());
        builder.CreateCondBr(checkExternal, SuccessBlock, CurrentBlock);

        // Handle indirect call case
        builder.SetInsertPoint(CurrentBlock);
        CurrentBlock->setName("sd.indirect");
        FunctionInfo.ExtraIDs.insert(FunctionInfo.TypeID);
        ConstantInt *indirectMagicNumber = builder.getInt32(FunctionInfo.TypeID);
        auto checkIndirectCall = builder.CreateICmpEQ(minID, indirectMagicNumber);
        CurrentBlock = BasicBlock::Create(F.getContext(), "", CurrentBlock->getParent());
        builder.CreateCondBr(checkIndirectCall, SuccessBlock, CurrentBlock);

        builder.SetInsertPoint(CurrentBlock);
        CurrentBlock->setName("sd.indirect2");
        FunctionInfo.ExtraIDs.insert(0x7FFFF);
        ConstantInt *unknownMagicNumber = builder.getInt32(0x7FFFF);
        auto checkUnknownCall = builder.CreateICmpEQ(minID, unknownMagicNumber);
        CurrentBlock = BasicBlock::Create(F.getContext(), "", CurrentBlock->getParent());
        builder.CreateCondBr(checkUnknownCall, SuccessBlock, CurrentBlock);
      }

      // Build the fail block (CurrentBlock is the block after the last check failed)
      builder.SetInsertPoint(CurrentBlock);
      CurrentBlock->setName("sd.fail");
      std::string formatString = ".\n";
      std::vector<Value *> args;
      //createPrintCall(formatString, args, builder, M);

      // Build the fail case TerminatorInst (quit program or continue after backward-edge violation?)
      //builder.CreateCall(Intrinsic::getDeclaration(M, Intrinsic::trap));
      //builder.CreateUnreachable();

      builder.CreateCall(Intrinsic::getDeclaration(M, Intrinsic::donothing));
      builder.CreateBr(SuccessBlock);

      count++;
    }
    return count;
  }

  unsigned generateCompareChecks(Function &F, StaticFunctionInfo &FunctionInfo) {
    if (FunctionInfo.IDs.size() == 0)
      return 0;

    if (FunctionInfo.IDs.size() > 1) {
      // Diamond detected
      sdLog::warn() << "Static Function " << F.getName() << " has " << FunctionInfo.IDs.size() << " IDs!\n";
    }

    // Collect all return statements (usually just a single one) first.
    // We need to do this first, because inserting checks invalidates the Instruction-Iterator.
    std::vector<Instruction *> Returns;
    for (auto &B : F) {
      for (auto &I : B) {
        if (isa<ReturnInst>(I)) {
          Returns.push_back(&I);
        }
      }
    }

    Module *M = F.getParent();
    unsigned count = 0;
    for (auto RI : Returns) {
      // Inserting check before RI is executed.
      IRBuilder<> builder(RI);

      //Create 'returnaddress'-intrinsic call
      Function *ReturnAddressFunc = Intrinsic::getDeclaration(
              F.getParent(), Intrinsic::returnaddress);

      // Some constants we need
      ConstantInt *zero = builder.getInt32(0);
      ConstantInt *offsetFirstNOP = builder.getInt32(3);
      auto int64Ty = Type::getInt64Ty(M->getContext());
      auto int32PtrTy = Type::getInt32PtrTy(M->getContext());

      // Get return address
      auto ReturnAddress = builder.CreateCall(ReturnAddressFunc, zero);

      // Load minID from first NOP (extract actual value using the bit mask)
      auto minPtr = builder.CreateGEP(ReturnAddress, offsetFirstNOP);
      auto min32Ptr = builder.CreatePointerCast(minPtr, int32PtrTy);
      auto minID = builder.CreateLoad(min32Ptr);

      // Build ID compare check
      ConstantInt *IDValue = builder.getInt32(uint32_t(FunctionInfo.IDs[0] | 0x80000));
      auto check = builder.CreateICmpEQ(IDValue, minID);

      // Branch to CheckFailed if the ID check fails
      MDBuilder MDB(F.getContext());
      TerminatorInst *CheckFailed = SplitBlockAndInsertIfThen(check, RI, true);
      BasicBlock *SuccessBlock = RI->getParent();

      // Prepare for additional checks
      BasicBlock *CurrentBlock = CheckFailed->getParent();
      CheckFailed->eraseFromParent();
      assert(CurrentBlock->empty() && "Current Block still contains Instructions!");

      // Build the fail block
      builder.SetInsertPoint(CurrentBlock);

      if (F.hasAddressTaken() && FunctionInfo.TypeID != -1) {
        // Handle external call case
        //TODO MATT: fix constant for external call
        builder.SetInsertPoint(CurrentBlock);
        CurrentBlock->setName("sd.external");
        ConstantInt *memRange = builder.getInt64(0x2000000);
        auto returnAddressAsInt = builder.CreatePtrToInt(ReturnAddress, int64Ty);
        auto checkExternal = builder.CreateICmpUGT(returnAddressAsInt, memRange);
        CurrentBlock = BasicBlock::Create(F.getContext(), "", CurrentBlock->getParent());
        builder.CreateCondBr(checkExternal, SuccessBlock, CurrentBlock);

        // Handle indirect call case
        builder.SetInsertPoint(CurrentBlock);
        CurrentBlock->setName("sd.indirect");
        FunctionInfo.ExtraIDs.insert(FunctionInfo.TypeID);
        ConstantInt *indirectMagicNumber = builder.getInt32(FunctionInfo.TypeID);
        auto checkIndirectCall = builder.CreateICmpEQ(minID, indirectMagicNumber);
        CurrentBlock = BasicBlock::Create(F.getContext(), "", CurrentBlock->getParent());
        builder.CreateCondBr(checkIndirectCall, SuccessBlock, CurrentBlock);

        builder.SetInsertPoint(CurrentBlock);
        CurrentBlock->setName("sd.indirect2");
        FunctionInfo.ExtraIDs.insert(0x7FFFF);
        ConstantInt *unknownMagicNumber = builder.getInt32(0x7FFFF);
        auto checkUnknownCall = builder.CreateICmpEQ(minID, unknownMagicNumber);
        CurrentBlock = BasicBlock::Create(F.getContext(), "", CurrentBlock->getParent());
        builder.CreateCondBr(checkUnknownCall, SuccessBlock, CurrentBlock);
      }

      // Build the fail block (CurrentBlock is the block after the last check failed)
      builder.SetInsertPoint(CurrentBlock);
      CurrentBlock->setName("sd.fail");

      std::string formatString = ".\n";
      std::vector<Value *> args;
      //createPrintCall(formatString, args, builder, M);

      // Build the fail case TerminatorInst (quit program or continue after backward-edge violation?)
      //builder.CreateCall(Intrinsic::getDeclaration(M, Intrinsic::trap));
      //builder.CreateUnreachable();

      builder.CreateCall(Intrinsic::getDeclaration(M, Intrinsic::donothing));
      builder.CreateBr(SuccessBlock);

      count++;
    }
    return count;
  }

  void storeStatistics(Module &M, int NumberOfTotalChecks,
                       std::vector<FunctionInfo> &FunctionsMarkedStatic,
                       std::vector<FunctionInfo> &FunctionsMarkedVirtual,
                       std::vector<FunctionInfo> &FunctionsMarkedExternal,
                       std::vector<FunctionInfo> &FunctionsMarkedNoReturn,
                       std::vector<FunctionInfo> &FunctionsMarkedBlackListed) {

    std::string outName = findOutputFileName(&M);
    sdLog::stream() << "Store statistics to file: " << outName << "\n";
    std::ofstream Outfile(outName);

    std::ostream_iterator<std::string> OutIterator(Outfile, "\n");
    Outfile << "Total number of checks: " << NumberOfTotalChecks << "\n";
    Outfile << "\n";

    Outfile << "### Static function checks: " << FunctionsMarkedStatic.size() << "\n";
    for (auto &Entry : FunctionsMarkedStatic) {
      Outfile << Entry.Name;
      for (auto &ID : Entry.IDs) {
        Outfile << "," << std::to_string(ID);
      }
      for (auto &ID : Entry.ExtraIDs) {
        Outfile << "," << std::to_string(ID);
      }
      Outfile << "\n";
    }
    Outfile << "##\n";

    Outfile << "### Virtual function checks: " << FunctionsMarkedVirtual.size() << "\n";
    for (auto &Entry : FunctionsMarkedVirtual) {
      Outfile << Entry.Name;
      for (auto &ID : Entry.IDs) {
        Outfile << "," << std::to_string(ID);
      }
      for (auto &ID : Entry.ExtraIDs) {
        Outfile << "," << std::to_string(ID);
      }
      Outfile << "\n";
    }
    Outfile << "##\n";

    Outfile << "### External functions: " << FunctionsMarkedExternal.size() << "\n";
    for (auto &Entry : FunctionsMarkedExternal) {
      Outfile << Entry.Name;
      for (auto &ID : Entry.IDs) {
        Outfile << "," << std::to_string(ID);
      }
      for (auto &ID : Entry.ExtraIDs) {
        Outfile << "," << std::to_string(ID);
      }
      Outfile << "\n";
    }
    Outfile << "##\n";

    Outfile << "### Blacklisted functions: " << FunctionsMarkedBlackListed.size() << "\n";
    for (auto &Entry : FunctionsMarkedBlackListed) {
      Outfile << Entry.Name;
      for (auto &ID : Entry.IDs) {
        Outfile << "," << std::to_string(ID);
      }
      for (auto &ID : Entry.ExtraIDs) {
        Outfile << "," << std::to_string(ID);
      }
      Outfile << "\n";
    }
    Outfile << "##\n";

    Outfile << "### Without return: " << FunctionsMarkedNoReturn.size() << "\n";
    for (auto &Entry : FunctionsMarkedNoReturn) {
      Outfile << Entry.Name;
      for (auto &ID : Entry.IDs) {
        Outfile << "," << std::to_string(ID);
      }
      for (auto &ID : Entry.ExtraIDs) {
        Outfile << "," << std::to_string(ID);
      }
      Outfile << "\n";
    }
    Outfile << "##\n";
  }
};
}

char SDReturnChecks::ID = 0;

INITIALIZE_PASS(SDReturnChecks, "sdretchecks", "Inserts the return checks", false, false)

llvm::ModulePass *llvm::createSDReturnChecksPass() {
  return new SDReturnChecks();
}


