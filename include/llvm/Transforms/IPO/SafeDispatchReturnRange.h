//===-- llvm/Transforms/IPO/SafeDispatchReturnRange.h --------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file contains a ModulePass for the SafeDispatch backward edge protection.
// It is used to analyse all call sites and generate all the information
// about them that is needed by the backend to insert the return range checks.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_SAFEDISPATCHRETURNRANGE_H
#define LLVM_SAFEDISPATCHRETURNRANGE_H

#include "llvm/ADT/StringSet.h"
#include "llvm/Transforms/IPO/SDEncode.h"
#include "llvm/Transforms/IPO/SafeDispatchLogStream.h"
#include "llvm/Transforms/IPO/SafeDispatchReturnAddress.h"

namespace llvm {

struct SDReturnRange : public ModulePass {
public:
  static char ID;

  SDReturnRange() : ModulePass(ID) {
    sdLog::stream() << "initializing SDReturnRange pass\n";
    initializeSDReturnRangePass(*PassRegistry::getPassRegistry());
    pseudoDebugLoc = 1;
  }

  virtual ~SDReturnRange() {
    sdLog::stream() << "deleting SDReturnRange pass\n";
  }

  bool runOnModule(Module &M) override;

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<SDBuildCHA>();
    AU.addRequired<SDReturnAddress>();
    AU.addPreserved<SDBuildCHA>();
  }

private:
  SDBuildCHA *CHA = nullptr;
  SDEncoder *Encoder = nullptr;
  std::map<std::string, uint64_t> FunctionIDMap{};

  /// Information about the virtual CallSites that are being found by this pass.
  std::vector<std::string> CallSiteDebugLocsVirtual;

  /// Information about the static CallSites that are being found by this pass.
  std::vector<std::string> CallSiteDebugLocsStatic;

  /// Set of all virtual CallSites.
  std::set<CallSite> VirtualCallSites {};

  /// Current ID for the DebugLoc hack.
  uint64_t pseudoDebugLoc;

  /// Find and process all virtual CallSites.
  void processVirtualCallSites(Module &M);

  /// Find and process all static callSites.
  void processStaticCallSites(Module &M);

  /// Extract the CallSite information from @param CheckedVptrCall and add the CallSite to CallSiteDebugLocsVirtual.
  bool addVirtualCallSite(const CallInst *CheckedVptrCall, CallSite CallSite, Module &M);

  /// Add the CallSite to CallSiteDebugLocsStatic.
  bool addStaticCallSite(CallSite CallSite, Module &M);

  /// Store all callSite information (later retrieved by the backend).
  void storeCallSites(Module &M);

  /// Get or create a DebugLoc for CallSite (created by using pseudoDebugLoc).
  const DebugLoc* getOrCreateDebugLoc(CallSite CallSite, Module &M);
};

} // End llvm namespace

#endif //LLVM_SAFEDISPATCHRETURNRANGE_H
