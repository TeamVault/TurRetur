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
#include "llvm/Transforms/IPO/SafeDispatchReturnRange.h"

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
    StaticFunctions = getAnalysis<SDReturnRange>().getStaticCallees();

    functionID = CHA->getMaxID() + 1;

    sdLog::stream() << "Start ID for static functions: " << functionID << "\n";

    // init statistics
    std::vector<ProcessingInfo> FunctionsMarkedStatic;
    std::vector<ProcessingInfo> FunctionsMarkedVirtual;
    std::vector<ProcessingInfo> FunctionsMarkedNoCaller;
    std::vector<ProcessingInfo> FunctionsMarkedNoReturn;
    std::vector<ProcessingInfo> FunctionsMarkedBlackListed;

    int NumberOfTotalChecks = 0;

    for (auto &F : M) {
      ProcessingInfo Info;
      Info.RangeName = F.getName();

      // do processing
      int NumberOfChecks = processFunction(F, Info);

      bool InfoValidatesNoChecks = false;
      for (auto &Entry : Info.Flags) {
        switch (Entry) {
          case Static:
            FunctionsMarkedStatic.push_back(Info);
            break;
          case Virtual:
            FunctionsMarkedVirtual.push_back(Info);
            break;
          case NoCaller:
            FunctionsMarkedNoCaller.push_back(Info);
            break;
          case NoReturn:
            FunctionsMarkedNoReturn.push_back(Info);
            InfoValidatesNoChecks = true;
            break;
          case BlackListed:
            FunctionsMarkedBlackListed.push_back(Info);
            InfoValidatesNoChecks = true;
            break;
        }
      }

      if (NumberOfChecks == 0 && !InfoValidatesNoChecks)
        sdLog::errs() << "Function: " << Info.RangeName << "has no checks but is not NoReturn or blacklisted!\n";

      NumberOfTotalChecks += NumberOfChecks;
    }

    // enables the backend pass
    if (NumberOfTotalChecks > 0) {
      M.getOrInsertNamedMetadata("SD_emit_return_labels");

      // store function IDs for backend
      storeFunctionIDMap(M);
    }

    // print and store statistics
    sdLog::stream() << sdLog::newLine << "P7b. SDReturnAddress statistics:" << "\n";
    sdLog::stream() << "Total number of checks: " << NumberOfTotalChecks << "\n";
    sdLog::stream() << "Total number of static functions: " << FunctionsMarkedStatic.size() << "\n";
    sdLog::stream() << "Total number of virtual functions: " << FunctionsMarkedVirtual.size() << "\n";
    sdLog::stream() << "Total number of blacklisted functions: " << FunctionsMarkedBlackListed.size() << "\n";
    sdLog::stream() << "Total number of functions without return: " << FunctionsMarkedNoReturn.size() << "\n";

    storeStatistics(M, NumberOfTotalChecks,
                    FunctionsMarkedStatic,
                    FunctionsMarkedVirtual,
                    FunctionsMarkedNoCaller,
                    FunctionsMarkedNoReturn,
                    FunctionsMarkedBlackListed);

    sdLog::stream() << sdLog::newLine << "P7b. Finished running the SDReturnAddress pass ..." << "\n";
    sdLog::blankLine();

    return NumberOfTotalChecks > 0;
  }

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<SDBuildCHA>(); // depends on SDBuildCHA pass (max virtual FunctionID)
    AU.addRequired<SDReturnRange>(); // depends on ReturnRange pass  (StaticFunctions with Caller)
    AU.setPreservesAll();
  }

  SDEncoder getEncoder() {
    return Encoder;
  }

private:
  enum ProcessingInfoFlags {
    Static, Virtual, NoCaller, NoReturn, BlackListed
  };

  struct ProcessingInfo {
    std::set<ProcessingInfoFlags> Flags{};
    std::set<uint64_t> IDs{};
    StringRef RangeName;

    void insert(ProcessingInfoFlags Flag){
      Flags.insert(Flag);
    }

    bool hasFlag(ProcessingInfoFlags Flag) {
      return Flags.find(Flag) != Flags.end();
    }
  };

  SDBuildCHA *CHA = nullptr;
  SDEncoder Encoder;

  const StringSet<> *StaticFunctions{};

  std::map<std::string, uint64_t> FunctionIDMap{};
  uint64_t functionID{};

  bool isBlackListedFunction(const Function &F) const;

  bool isStaticFunction(const Function &F, ProcessingInfo Info) const;

  bool isVirtualFunction(const Function &F) const;

  int processFunction(Function &F, ProcessingInfo &Info);

  int processStaticFunction(Function &F, ProcessingInfo &Info);

  int processVirtualFunction(Function &F, ProcessingInfo &Info);

  int generateRangeChecks(Function &F, std::vector<uint64_t> IDs, ProcessingInfo &Info);

  int generateCompareChecks(Function &F, uint64_t ID, ProcessingInfo &Info);

  void storeFunctionIDMap(Module &M);

  void storeStatistics(Module &M, int NumberOfTotalChecks,
                       std::vector<ProcessingInfo> &FunctionsMarkedStatic,
                       std::vector<ProcessingInfo> &FunctionsMarkedVirtual,
                       std::vector<ProcessingInfo> &FunctionsMarkedNoCaller,
                       std::vector<ProcessingInfo> &FunctionsMarkedNoReturn,
                       std::vector<ProcessingInfo> &FunctionsMarkedBlackListed);
};

} // End llvm namespace

#endif //LLVM_SAFEDISPATCHRETURNADDRESS_H
