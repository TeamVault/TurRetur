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
#include "llvm/Transforms/IPO/SafeDispatchGVMd.h"
#include <fstream>
#include <llvm/Support/FileSystem.h>

using namespace llvm;
/**
 * Pass for inserting the return address intrinsic
 */

//static const std::string itaniumDestructorTokens[] = {"D0Ev", "D1Ev", "D2Ev"};
static const std::string itaniumConstructorTokens[] = {"C0Ev", "C1Ev", "C2Ev"};

void SDReturnAddress::processFunction(Function &F) {
  auto &C = F.getParent()->getContext();
  if (isBlackListedFunction(F)) {
    std::vector<llvm::Metadata *> MDVector;
    MDVector.push_back(sd_getMDString(C, F.getName()));
    F.getParent()->getOrInsertNamedMetadata(SD_MD_FUNCINFO_BLACKLIST + F.getName().str())->addOperand(MDNode::get(C, MDVector));
    return;
  }

  if (isVirtualFunction(F)) {
    auto *MDNode = processVirtualFunction(F);
    F.getParent()->getOrInsertNamedMetadata(SD_MD_FUNCINFO_VIRTUAL + F.getName().str())->addOperand(MDNode);
    return;
  }

  if (isStaticFunction(F)) {
    auto *MDNode = processStaticFunction(F);
    F.getParent()->getOrInsertNamedMetadata(SD_MD_FUNCINFO_NORMAL + F.getName().str())->addOperand(MDNode);
    return;
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

bool SDReturnAddress::isStaticFunction(const Function &F) const {
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

MDNode *SDReturnAddress::processStaticFunction(Function &F) {
  auto &C = F.getParent()->getContext();
  std::vector<llvm::Metadata *> MDVector;
  MDVector.push_back(sd_getMDString(C, F.getName()));

  sdLog::log() << "Function (static): " << F.getName()
               << " gets ID: " << functionID << "\n";

  FunctionIDMap[F.getName()] = functionID;

  MDVector.push_back(sd_getMDNumber(C, functionID));
  if (F.hasAddressTaken()) {
    uint32_t FunctionTypeID = Encoder.getTypeID(F.getFunctionType());
    MDVector.push_back(sd_getMDNumber(C, FunctionTypeID));
  }
  functionID++;

  return MDNode::get(C, MDVector);
}

MDNode *SDReturnAddress::processVirtualFunction(Function &F) {
  auto &C = F.getParent()->getContext();
  std::vector<llvm::Metadata *> MDVector;
  MDVector.push_back(sd_getMDString(C, F.getName()));

  StringRef functionName = F.getName();
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
        return MDNode::get(C, MDVector);
      }
    } else {
      sdLog::errs() << "Virtual Function without ID: " << functionName << "\n";
      return MDNode::get(C, MDVector);
    }
  }

  assert(IDs.size() > 0);
  FunctionIDMap[F.getName()] = IDs[0];

  MDVector.push_back(sd_getMDNumber(C, IDs.size()));
  for (auto &ID : IDs) {
    MDVector.push_back(sd_getMDNumber(C, ID));
  }
  if (F.hasAddressTaken()) {
    uint32_t FunctionTypeID = Encoder.getTypeID(F.getFunctionType());
    MDVector.push_back(sd_getMDNumber(C, FunctionTypeID));
  }

  return MDNode::get(C, MDVector);
}

char SDReturnAddress::ID = 0;

INITIALIZE_PASS_BEGIN(SDReturnAddress, "sdRetAdd", "Insert return intrinsic.", false, false)
INITIALIZE_PASS_DEPENDENCY(SDBuildCHA)
INITIALIZE_PASS_END(SDReturnAddress, "sdRetAdd", "Insert return intrinsic.", false, false)

ModulePass *llvm::createSDReturnAddressPass() {
  return new SDReturnAddress();
}