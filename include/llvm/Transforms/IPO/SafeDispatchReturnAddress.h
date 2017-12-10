//===-- llvm/Transforms/IPO/SafeDispatchReturnAddress.h --------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file contains a ModulePass for the SafeDispatch backward edge protection.
// It is used to to generate IDs for each function
// and then insert the return checks into the callees.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_SAFEDISPATCHRETURNADDRESS_H
#define LLVM_SAFEDISPATCHRETURNADDRESS_H

#include "llvm/Transforms/IPO/SafeDispatchLogStream.h"
#include "llvm/Transforms/IPO/SafeDispatchCHA.h"

namespace llvm {

/**
 * Pass for generating the return address checks
 */
class SDReturnAddress : public ModulePass {
public:
  static char ID;

  SDReturnAddress() : ModulePass(ID), Encoder(0x7FFFE) {
    sdLog::stream() << "initializing SDReturnAddress pass ...\n";
    initializeSDReturnAddressPass(*PassRegistry::getPassRegistry());
  }

  virtual ~SDReturnAddress() {
    sdLog::stream() << "deleting SDReturnAddress pass\n";
  }

  bool runOnModule(Module &M) override {
    sdLog::blankLine();
    sdLog::stream() << "P7b. Started running the SDReturnAddress pass ..." << sdLog::newLine << "\n";

    // get analysis results
    CHA = &getAnalysis<SDBuildCHA>();
    // Build the virtual ID ranges.
    CHA->buildFunctionInfo();

    functionID = CHA->getMaxID() + 1;

    sdLog::stream() << "Start ID for static functions: " << functionID << "\n";

    for (auto &F : M) {
      processFunction(F);
    }

    sdLog::stream() << sdLog::newLine << "P7b. Finished running the SDReturnAddress pass ..." << "\n";
    sdLog::blankLine();

    return false;
  }

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<SDBuildCHA>(); // depends on SDBuildCHA pass (max virtual FunctionID)
    AU.setPreservesAll();
  }

  SDEncoder *getEncoder() {
    return &Encoder;
  }

  const std::map<std::string, uint64_t> getFunctionIDMap() const {
    return FunctionIDMap;
  }

private:
  SDBuildCHA *CHA = nullptr;
  SDEncoder Encoder;
  std::map<std::string, uint64_t> FunctionIDMap{};

  uint64_t functionID{};

  bool isBlackListedFunction(const Function &F) const;

  bool isStaticFunction(const Function &F) const;

  bool isVirtualFunction(const Function &F) const;

  void processFunction(Function &F);

  MDNode *processStaticFunction(Function &F);

  MDNode *processVirtualFunction(Function &F);
};

} // End llvm namespace

#endif //LLVM_SAFEDISPATCHRETURNADDRESS_H
