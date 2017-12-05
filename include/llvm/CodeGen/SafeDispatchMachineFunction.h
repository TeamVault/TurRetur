#ifndef LLVM_SAFEDISPATCHMACHINEFUNCION_H
#define LLVM_SAFEDISPATCHMACHINEFUNCION_H

#include "llvm/Transforms/IPO/SafeDispatchReturnRange.h"
#include "llvm/Transforms/IPO/SafeDispatchLog.h"
#include "llvm/Transforms/IPO/SafeDispatchTools.h"
#include "llvm/Transforms/IPO/SafeDispatchLogStream.h"

#include "llvm/MC/MCContext.h"
#include "llvm/CodeGen/MachineFunctionPass.h"
#include "llvm/CodeGen/MachineInstrBuilder.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"
#include "llvm/CodeGen/MachineModuleInfo.h"
#include "llvm/CodeGen/Passes.h"
#include "llvm/Target/TargetInstrInfo.h"
#include "llvm/MC/MCSymbol.h"


#include <string>
#include <fstream>
#include <sstream>
#include <iostream>

namespace llvm {
/**
 * This pass receives information generated in the SafeDispatch LTO passes
 * (SafeDispatchReturnRange) for use in the X86 backend.
 * */

struct SDMachineFunction : public MachineFunctionPass {
public:
  static char ID; // Pass identification, replacement for typeid

  SDMachineFunction() : MachineFunctionPass(ID) {
    sdLog::stream() << "initializing SDMachineFunction pass\n";
    initializeSDMachineFunctionPass(*PassRegistry::getPassRegistry());

    //TODO MATT: STOPPER FOR DEBUG
    //std::string stopper;
    //std::cin >> stopper;
    //errs() << stopper;
  }

  virtual ~SDMachineFunction() {
    analyse(M);
    sdLog::stream() << "deleting SDMachineFunction pass\n";
  }

  bool runOnMachineFunction(MachineFunction &MF) override;

private:
  // Constants
  const uint64_t unknownID = 0xFFFFF;
  const uint64_t indirectID = 0xFFFFF;
  const uint64_t tailID = 0xFFFFE;
  const Module* M = nullptr;
  bool SkipPass = false;

  // Data
  std::map <std::string, std::string> CallSiteDebugLocVirtual;
  std::map <std::string, std::string> CallSiteDebugLocStatic;

  std::map <std::string, std::pair<uint64_t , uint64_t>> CallSiteRange;
  std::map <std::string, uint64_t> CallSiteID;

  // Functions
  int loadVirtualCallSiteData();
  int loadStaticCallSiteData();

  bool processVirtualCallSite(std::string &DebugLocString,
                              MachineInstr &MI,
                              MachineBasicBlock &MBB,
                              const TargetInstrInfo *TII);

  bool processStaticCallSite(std::string &DebugLocString,
                             MachineInstr &MI,
                             MachineBasicBlock &MBB,
                             const TargetInstrInfo *TII);

  bool processUnknownCallSite(std::string &DebugLocString,
                              MachineInstr &MI,
                              MachineBasicBlock &MBB,
                              const TargetInstrInfo *TII);

  std::string debugLocToString(const DebugLoc &Log);

  // Analysis
  std::vector<uint64_t> RangeWidths;
  std::map <uint64_t, int> IDCount;

  int NumberOfVirtual;
  int NumberOfStaticDirect;
  int NumberOfIndirect;
  int NumberOfTail;
  int NumberOfUnknown;

  void analyse(const Module *M);
};
}

#endif //LLVM_SAFEDISPATCHMACHINEFUNCION_H