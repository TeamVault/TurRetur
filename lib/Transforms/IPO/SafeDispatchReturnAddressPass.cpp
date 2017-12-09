//===- SafeDispatchReturnAddress.cpp - SafeDispatch ReturnAddress code ----===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements the SDReturnAddress class.
//
//===----------------------------------------------------------------------===//

#include "llvm/IR/MDBuilder.h"
#include "llvm/Transforms/IPO/SDEncode.h"
#include "llvm/Transforms/IPO/SafeDispatchReturnAddress.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include <fstream>
#include <llvm/Support/FileSystem.h>

using namespace llvm;
/**
 * Pass for inserting the return address intrinsic
 */

//static const std::string itaniumDestructorTokens[] = {"D0Ev", "D1Ev", "D2Ev"};
static const std::string itaniumConstructorTokens[] = {"C0Ev", "C1Ev", "C2Ev"};

static Function *createPrintfPrototype(Module *module) {
  std::vector<llvm::Type *> argTypes;
  argTypes.push_back(Type::getInt8PtrTy(module->getContext()));

  llvm::FunctionType *printf_type = FunctionType::get(
          /* ret type: int32 */ llvm::Type::getInt32Ty(module->getContext()),
          /* args: int8* */ argTypes,
          /* var args */ true);

  return cast<Function>(module->getOrInsertFunction("printf", printf_type));
}

static void createPrintCall(const std::string &FormatString,
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

static std::string findOutputFileName(const Module *M) {
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
};

int SDReturnAddress::processFunction(Function &F, ProcessingInfo &Info) {
  if (isBlackListedFunction(F)) {
    Info.Type = BlackListed;
    return 0;
  }

  if (isVirtualFunction(F)) {
    return processVirtualFunction(F, Info);
  }

  if (isStaticFunction(F, Info)) {
    return processStaticFunction(F, Info);
  }

  llvm_unreachable("Function was not processed!");
}

bool SDReturnAddress::isBlackListedFunction(const Function &F) const {
  return F.getName().startswith("__")
         || F.getName().startswith("llvm.")
         || F.getName() == "_Znwm"
         || F.getName() == "main"
         || F.getName().startswith("_GLOBAL_");
}

bool SDReturnAddress::isStaticFunction(const Function &F, ProcessingInfo Info) const {
  return true;
}

bool SDReturnAddress::isVirtualFunction(const Function &F) const {
  if (!F.getName().startswith("_Z")) {
    return false;
  }

  for (auto &Token : itaniumConstructorTokens) {
    if (F.getName().endswith(Token)) {
      return false;
    }
  }

  if (F.getName().startswith("_ZTh")) {
    return true;
  }

  return !(CHA->getFunctionID(F.getName()).empty());
}

int SDReturnAddress::processStaticFunction(Function &F, ProcessingInfo &Info) {
  Info.Type = Static;
  if (F.isDeclaration() || F.hasExternalLinkage() || F.hasExternalWeakLinkage()) {
    Info.insert(External);
  }

  int NumberOfChecks = generateCompareChecks(F, functionID, Info);

  sdLog::log() << "Function (static): " << F.getName()
               << " gets ID: " << functionID
               << " (Checks: " << NumberOfChecks << ")\n";

  if (NumberOfChecks == 0) {
    Info.insert(NoReturn);
  } else {
    Info.IDs.insert(functionID);
    FunctionIDMap[F.getName()] = functionID;
    functionID++;
  }

  return NumberOfChecks;
}

int SDReturnAddress::processVirtualFunction(Function &F, ProcessingInfo &Info) {
  StringRef functionName = F.getName();

  Info.Type = Virtual;
  if (F.isDeclaration() || F.hasExternalLinkage() || F.hasExternalWeakLinkage()) {
    Info.insert(External);
  }

  std::vector<uint64_t> IDs = CHA->getFunctionID(functionName.str());
  if (IDs.empty()) {
    // check for thunk (sets functionNameString to the function the thunk is used for)
    if (functionName.startswith("_ZTh")) {
      // remove the "_ZTh" part from the name and replace it with "_Z"
      auto splits = functionName.drop_front(1).split("_");
      std::string functionNameString = ("_Z" + splits.second).str();

      IDs = CHA->getFunctionID(functionNameString);
      if (IDs.empty()) {
        sdLog::errs() << "Thunk conversion failed: " << functionName << "->" << functionNameString <<  "\n";
        return 0;
      }
    } else {
      sdLog::errs() << "Virtual Function without ID: " << functionName << "\n";
      return 0;
    }
  }

  assert(IDs.size() > 0);
  FunctionIDMap[F.getName()] = IDs[0];
  int NumberOfChecks = generateRangeChecks(F, IDs, Info);

  sdLog::log() << "Function (virtual): " << F.getName()
               << " (Checks: " << NumberOfChecks << ")\n";

  if (NumberOfChecks == 0) {
    Info.insert(NoReturn);
  } else {
    Info.IDs.insert(IDs.begin(), IDs.end());
  }
  return NumberOfChecks;
}

int SDReturnAddress::generateRangeChecks(Function &F, std::vector<uint64_t> IDs, ProcessingInfo &Info) {
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
  int count = 0;
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

    if (IDs.size() != 1) {
      // Diamond detected
      sdLog::stream() << F.getName() << "has " << IDs.size() << " IDs!\n";
    }

    // Build first check
    ConstantInt *IDValue = builder.getInt32(uint32_t(IDs[0] | 0x80000));
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
    for (int i = 1; i < IDs.size(); ++i) {
      // Build check
      builder.SetInsertPoint(CurrentBlock);
      CurrentBlock->setName("sd.range");
      IDValue = builder.getInt32(uint32_t(IDs[i] | 0x80000));
      diff = builder.CreateSub(IDValue, minID);
      check = builder.CreateICmpULE(diff, width);
      CurrentBlock = BasicBlock::Create(F.getContext(), "", CurrentBlock->getParent());
      builder.CreateCondBr(check, SuccessBlock, CurrentBlock);
    }

    if (F.hasAddressTaken()) {
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
      uint32_t FunctionTypeID = Encoder.getTypeID(F.getFunctionType());
      ConstantInt *indirectMagicNumber = builder.getInt32(FunctionTypeID);
      auto checkIndirectCall = builder.CreateICmpEQ(minID, indirectMagicNumber);
      CurrentBlock = BasicBlock::Create(F.getContext(), "", CurrentBlock->getParent());
      builder.CreateCondBr(checkIndirectCall, SuccessBlock, CurrentBlock);
      Info.ExtraIDs.insert(uint64_t(FunctionTypeID));

      builder.SetInsertPoint(CurrentBlock);
      CurrentBlock->setName("sd.indirect2");
      ConstantInt *unknownMagicNumber = builder.getInt32(0x7FFFF);
      auto checkUnknownCall = builder.CreateICmpEQ(minID, unknownMagicNumber);
      CurrentBlock = BasicBlock::Create(F.getContext(), "", CurrentBlock->getParent());
      builder.CreateCondBr(checkUnknownCall, SuccessBlock, CurrentBlock);
      Info.ExtraIDs.insert(0x7FFFF);
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

int SDReturnAddress::generateCompareChecks(Function &F, uint64_t ID, ProcessingInfo &Info) {
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
  int count = 0;
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
    ConstantInt *IDValue = builder.getInt32(uint32_t(ID | 0x80000));
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

    if (F.hasAddressTaken()) {
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
      uint32_t FunctionTypeID = Encoder.getTypeID(F.getFunctionType());
      ConstantInt *indirectMagicNumber = builder.getInt32(FunctionTypeID);
      auto checkIndirectCall = builder.CreateICmpEQ(minID, indirectMagicNumber);
      CurrentBlock = BasicBlock::Create(F.getContext(), "", CurrentBlock->getParent());
      builder.CreateCondBr(checkIndirectCall, SuccessBlock, CurrentBlock);
      Info.ExtraIDs.insert(uint64_t(FunctionTypeID));

      builder.SetInsertPoint(CurrentBlock);
      CurrentBlock->setName("sd.indirect2");
      ConstantInt *unknownMagicNumber = builder.getInt32(0x7FFFF);
      auto checkUnknownCall = builder.CreateICmpEQ(minID, unknownMagicNumber);
      CurrentBlock = BasicBlock::Create(F.getContext(), "", CurrentBlock->getParent());
      builder.CreateCondBr(checkUnknownCall, SuccessBlock, CurrentBlock);
      Info.ExtraIDs.insert(0x7FFFF);
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

void SDReturnAddress::storeStatistics(Module &M, int NumberOfTotalChecks,
                     std::vector<ProcessingInfo> &FunctionsMarkedStatic,
                     std::vector<ProcessingInfo> &FunctionsMarkedVirtual,
                     std::vector<ProcessingInfo> &FunctionsMarkedExternal,
                     std::vector<ProcessingInfo> &FunctionsMarkedNoReturn,
                     std::vector<ProcessingInfo> &FunctionsMarkedBlackListed) {



  int number = 0;
  std::string outName = findOutputFileName(&M);
  sdLog::stream() << "Store statistics to file: " << outName << "\n";
  std::ofstream Outfile(outName);

  std::ostream_iterator <std::string> OutIterator(Outfile, "\n");
  Outfile << "Total number of checks: " << NumberOfTotalChecks << "\n";
  Outfile << "\n";

  Outfile << "### Static function checks: " << FunctionsMarkedStatic.size() << "\n";
  for (auto &Entry : FunctionsMarkedStatic) {
    Outfile << Entry.RangeName.str();
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
    Outfile << Entry.RangeName.str();
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
    Outfile << Entry.RangeName.str();
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
    Outfile << Entry.RangeName.str();
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
    Outfile << Entry.RangeName.str();
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

void SDReturnAddress::storeFunctionIDMap(Module &M) {
  sdLog::stream() << "Store all function IDs for module: " << M.getName() << "\n";
  std::ofstream Outfile("./SD_FunctionIDMap");

  for (auto &mapEntry : FunctionIDMap) {
    Outfile << mapEntry.first << "," << mapEntry.second << "\n";
  }
  sdLog::stream() << "Stored Function IDs: " << FunctionIDMap.size() << "\n";
  Outfile.close();

  int number = 0;
  std::string outName = ((Twine) ("./SD_FunctionIDMap-backup" + std::to_string(number))).str();

  std::ifstream infile(outName);
  while (infile.good()) {
    number++;
    outName = "./SD_FunctionIDMap-backup" + std::to_string(number);
    infile = std::ifstream(outName);
  }

  std::ifstream src("./SD_FunctionIDMap", std::ios::binary);
  std::ofstream dst(outName, std::ios::binary);
  dst << src.rdbuf();
}

char SDReturnAddress::ID = 0;

INITIALIZE_PASS_BEGIN(SDReturnAddress, "sdRetAdd", "Insert return intrinsic.", false, false)
  INITIALIZE_PASS_DEPENDENCY(SDBuildCHA)
  INITIALIZE_PASS_DEPENDENCY(SDReturnRange)
INITIALIZE_PASS_END(SDReturnAddress, "sdRetAdd", "Insert return intrinsic.", false, false)

ModulePass *llvm::createSDReturnAddressPass() {
  return new SDReturnAddress();
}