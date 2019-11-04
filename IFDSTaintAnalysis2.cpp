/******************************************************************************
 * Copyright (c) 2017 Philipp Schubert.
 * All rights reserved. This program and the accompanying materials are made
 * available under the terms of LICENSE.txt.
 *
 * Contributors:
 *     Philipp Schubert and others
 *****************************************************************************/

#include <llvm/IR/CallSite.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Value.h>
#include <llvm/IR/Operator.h>
#include <llvm/Support/raw_ostream.h>

#include <phasar/PhasarLLVM/ControlFlow/LLVMBasedICFG.h>
#include <phasar/PhasarLLVM/IfdsIde/FlowFunction.h>
#include <phasar/PhasarLLVM/IfdsIde/FlowFunctions/GenAll.h>
#include <phasar/PhasarLLVM/IfdsIde/FlowFunctions/GenIf.h>
#include <phasar/PhasarLLVM/IfdsIde/FlowFunctions/Gen.h>
#include <phasar/PhasarLLVM/IfdsIde/FlowFunctions/Identity.h>
#include <phasar/PhasarLLVM/IfdsIde/FlowFunctions/KillAll.h>
#include <phasar/PhasarLLVM/IfdsIde/LLVMFlowFunctions/MapFactsToCallee.h>
#include <phasar/PhasarLLVM/IfdsIde/LLVMFlowFunctions/MapFactsToCaller.h>
#include <phasar/PhasarLLVM/IfdsIde/LLVMZeroValue.h>
#include <phasar/PhasarLLVM/IfdsIde/Problems/IFDSTaintAnalysis.h>
#include <phasar/PhasarLLVM/IfdsIde/SpecialSummaries.h>

#include <phasar/Utils/LLVMIRToSrc.h>
#include <phasar/Utils/LLVMShorthands.h>
#include <phasar/Utils/Logger.h>

using namespace std;
using namespace psr;

namespace psr {

IFDSTaintAnalysis::IFDSTaintAnalysis(i_t icfg, const LLVMTypeHierarchy &th,
                                     const ProjectIRDB &irdb,
                                     TaintSensitiveFunctions TSF,
                                     vector<string> EntryPoints)
    : LLVMDefaultIFDSTabulationProblem(icfg, th, irdb),
      SourceSinkFunctions(TSF), EntryPoints(EntryPoints) {
  IFDSTaintAnalysis::zerovalue = createZeroValue();
}

shared_ptr<FlowFunction<IFDSTaintAnalysis::d_t>>
IFDSTaintAnalysis::getNormalFlowFunction(IFDSTaintAnalysis::n_t curr,
                                         IFDSTaintAnalysis::n_t succ) {
  auto &lg = lg::get();
  LOG_IF_ENABLE(BOOST_LOG_SEV(lg, DEBUG)
                << "IFDSTaintAnalysis::getNormalFlowFunction()");
  ////// jinseob //////
  LOG_IF_ENABLE(BOOST_LOG_SEV(lg, DEBUG)
                << "@@@@@@@@@@ getNormalFlowFunction() @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@");
  ////////////////////
  // If a tainted value is stored, the store location must be tainted too
  if (auto Store = llvm::dyn_cast<llvm::StoreInst>(curr)) {
    ////// jinseob //////
    LOG_IF_ENABLE(BOOST_LOG_SEV(lg, DEBUG)
                  << "@@@@@@@@@@ Store @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@");
    ////////////////////
    struct TAFF : FlowFunction<IFDSTaintAnalysis::d_t> {
      const llvm::StoreInst *store;
      TAFF(const llvm::StoreInst *s) : store(s){};
      set<IFDSTaintAnalysis::d_t>
      computeTargets(IFDSTaintAnalysis::d_t source) override {
        if (store->getValueOperand() == source) {
          return set<IFDSTaintAnalysis::d_t>{store->getPointerOperand(),
                                             source};
        } else if (store->getValueOperand() != source &&
                   store->getPointerOperand() == source) {
          return {};
        } else {
          return {source};
        }
      }
    };
    return make_shared<TAFF>(Store);
  }

  // If a tainted value is loaded, the loaded value is of course tainted
  if (auto Load = llvm::dyn_cast<llvm::LoadInst>(curr)) {
    ////// jinseob //////
    LOG_IF_ENABLE(BOOST_LOG_SEV(lg, DEBUG)
                  << "@@@@@@@@@@ Load @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@");
    ////////////////////
    return make_shared<GenIf<IFDSTaintAnalysis::d_t>>(
        Load, zeroValue(), [Load](IFDSTaintAnalysis::d_t source) {
          return source == Load->getPointerOperand();
        });
  }

  // Check if an address is computed from a tainted base pointer of an
  // aggregated object
  if (auto GEP = llvm::dyn_cast<llvm::GetElementPtrInst>(curr)) {
    ////// jinseob //////
    LOG_IF_ENABLE(BOOST_LOG_SEV(lg, DEBUG)
                  << "@@@@@@@@@@ GEP @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@");
    ////////////////////
    return make_shared<GenIf<IFDSTaintAnalysis::d_t>>(
        GEP, zeroValue(), [GEP](IFDSTaintAnalysis::d_t source) {
          return source == GEP->getPointerOperand();
        });
  }



  ////// jinseob ////// If a tainted value is Truncated, the Truncated value is of course tainted
  if (auto Trunc = llvm::dyn_cast<llvm::TruncInst>(curr)) {
    LOG_IF_ENABLE(BOOST_LOG_SEV(lg, DEBUG)
                  << "@@@@@@@@@@ Trunc @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@");
    LOG_IF_ENABLE(BOOST_LOG_SEV(lg, DEBUG) << "@@@@@@@@@@ " << llvmIRToString(Trunc->getOperand(0)) << " @@@@@@@@@@@@@@");

    return make_shared<GenIf<IFDSTaintAnalysis::d_t>>(
        Trunc, zeroValue(), [Trunc](IFDSTaintAnalysis::d_t source) {
          return source == Trunc->getOperand(0);
        });
  }
  ////////////////////

  ////// jinseob ////// If a tainted value is Binary operated, the operated value is of course tainted
  if (auto Binary = llvm::dyn_cast<llvm::BinaryOperator>(curr)) {
    LOG_IF_ENABLE(BOOST_LOG_SEV(lg, DEBUG)
                  << "@@@@@@@@@@ Binary @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@");
    LOG_IF_ENABLE(BOOST_LOG_SEV(lg, DEBUG) << "@@@@@@@@@@ " << llvmIRToString(Binary->getOperand(0)) << " @@@@@@@@@@@@@@");
    return make_shared<GenIf<IFDSTaintAnalysis::d_t>>(
        Binary, zeroValue(), [Binary](IFDSTaintAnalysis::d_t source) {
          return source == Binary->getOperand(0);
        });
  }
  ////////////////////

  ////// jinseob ////// 구현중 bitcast
  if (auto Bitcast = llvm::dyn_cast<llvm::BitCastOperator>(curr)) {
    LOG_IF_ENABLE(BOOST_LOG_SEV(lg, DEBUG)
                  << "@@@@@@@@@@ Bitcast @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@");
    LOG_IF_ENABLE(BOOST_LOG_SEV(lg, DEBUG) << "@@@@@@@@@@ " << llvmIRToString(Bitcast->getOperand(0)) << " @@@@@@@@@@@@@@");
    return make_shared<GenIf<IFDSTaintAnalysis::d_t>>(
        Bitcast, zeroValue(), [Bitcast](IFDSTaintAnalysis::d_t source) {
          return source == Bitcast->getOperand(0);
        });
  }
  ////////////////////

  ////// jinseob //////ptrtoint
  if (auto Ptrtoint = llvm::dyn_cast<llvm::PtrToIntOperator>(curr)) {
    LOG_IF_ENABLE(BOOST_LOG_SEV(lg, DEBUG)
                  << "@@@@@@@@@@ Ptrtoint @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@");
    LOG_IF_ENABLE(BOOST_LOG_SEV(lg, DEBUG) << "@@@@@@@@@@ " << llvmIRToString(Ptrtoint->getOperand(0)) << " @@@@@@@@@@@@@@");
    return make_shared<GenIf<IFDSTaintAnalysis::d_t>>(
        Ptrtoint, zeroValue(), [Ptrtoint](IFDSTaintAnalysis::d_t source) {
          return source == Ptrtoint->getOperand(0);
        });
  }
  ////////////////////
  ////// jinseob ////// IntToPtr
  if (auto IntToPtr = llvm::dyn_cast<llvm::IntToPtrInst>(curr)) {
    LOG_IF_ENABLE(BOOST_LOG_SEV(lg, DEBUG)
                  << "@@@@@@@@@@ IntToPtr @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@");
    LOG_IF_ENABLE(BOOST_LOG_SEV(lg, DEBUG) << "@@@@@@@@@@ " << llvmIRToString(IntToPtr->getOperand(0)) << " @@@@@@@@@@@@@@");
    return make_shared<GenIf<IFDSTaintAnalysis::d_t>>(
        IntToPtr, zeroValue(), [IntToPtr](IFDSTaintAnalysis::d_t source) {
          return source == IntToPtr->getOperand(0);
        });
  }
  ////////////////////
  ////// jinseob ////// GEPOper operator
  if (auto GEPOper = llvm::dyn_cast<llvm::GEPOperator>(curr)) {
    LOG_IF_ENABLE(BOOST_LOG_SEV(lg, DEBUG)
                  << "@@@@@@@@@@ GEPOper @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@");
    LOG_IF_ENABLE(BOOST_LOG_SEV(lg, DEBUG) << "@@@@@@@@@@ " << llvmIRToString(GEPOper->getOperand(0)) << " @@@@@@@@@@@@@@");

    return make_shared<GenIf<IFDSTaintAnalysis::d_t>>(
        GEPOper, zeroValue(), [GEPOper](IFDSTaintAnalysis::d_t source) {
          return source == GEPOper->getOperand(0);
        });
  }
  ////////////////////


  // Otherwise we do not care and leave everything as it is
  ////// jinseob //////
  LOG_IF_ENABLE(BOOST_LOG_SEV(lg, DEBUG)
                << "@@@@@@@@@@ otherwise @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@");
  ////////////////////
  return Identity<IFDSTaintAnalysis::d_t>::getInstance();
}

shared_ptr<FlowFunction<IFDSTaintAnalysis::d_t>>
IFDSTaintAnalysis::getCallFlowFunction(IFDSTaintAnalysis::n_t callStmt,
                                       IFDSTaintAnalysis::m_t destMthd) {
  auto &lg = lg::get();
  LOG_IF_ENABLE(BOOST_LOG_SEV(lg, DEBUG)
                << "IFDSTaintAnalysis::getCallFlowFunction()");
  ////// jinseob //////
  LOG_IF_ENABLE(BOOST_LOG_SEV(lg, DEBUG)
                << "@@@@@@@@@@ getCallFlowFunction() @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@");
  ////////////////////
  string FunctionName = cxx_demangle(destMthd->getName().str());
  // Check if a source or sink function is called:
  // We then can kill all data-flow facts not following the called function.
  // The respective taints or leaks are then generated in the corresponding
  // call to return flow function.
  if (SourceSinkFunctions.isSource(FunctionName) ||
      (SourceSinkFunctions.isSink(FunctionName))) {
    return KillAll<IFDSTaintAnalysis::d_t>::getInstance();
  }
  // Map the actual into the formal parameters
  if (llvm::isa<llvm::CallInst>(callStmt) ||
      llvm::isa<llvm::InvokeInst>(callStmt)) {
    return make_shared<MapFactsToCallee>(llvm::ImmutableCallSite(callStmt),
                                         destMthd);
  }
  // Pass everything else as identity
  return Identity<IFDSTaintAnalysis::d_t>::getInstance();
}

shared_ptr<FlowFunction<IFDSTaintAnalysis::d_t>>
IFDSTaintAnalysis::getRetFlowFunction(IFDSTaintAnalysis::n_t callSite,
                                      IFDSTaintAnalysis::m_t calleeMthd,
                                      IFDSTaintAnalysis::n_t exitStmt,
                                      IFDSTaintAnalysis::n_t retSite) {

  auto &lg = lg::get();
  LOG_IF_ENABLE(BOOST_LOG_SEV(lg, DEBUG)
                << "IFDSTaintAnalysis::getRetFlowFunction()");
  ////// jinseob //////
  LOG_IF_ENABLE(BOOST_LOG_SEV(lg, DEBUG)
                << "@@@@@@@@@@ getRetFlowFunction() @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@");
  ////////////////////
  // We must check if the return value and formal parameter are tainted, if so
  // we must taint all user's of the function call. We are only interested in
  // formal parameters of pointer/reference type.
  return make_shared<MapFactsToCaller>(
      llvm::ImmutableCallSite(callSite), calleeMthd, exitStmt,
      [](IFDSTaintAnalysis::d_t formal) {
        return formal->getType()->isPointerTy();
      });
  // All other stuff is killed at this point
}

shared_ptr<FlowFunction<IFDSTaintAnalysis::d_t>>
IFDSTaintAnalysis::getCallToRetFlowFunction(
    IFDSTaintAnalysis::n_t callSite, IFDSTaintAnalysis::n_t retSite,
    set<IFDSTaintAnalysis::m_t> callees) {
  auto &lg = lg::get();
  LOG_IF_ENABLE(BOOST_LOG_SEV(lg, DEBUG)
                << "IFDSTaintAnalysis::getCallToRetFlowFunction()");
  ////// jinseob //////
  LOG_IF_ENABLE(BOOST_LOG_SEV(lg, DEBUG)
                << "@@@@@@@@@@ getCallToRetFlowFunction() @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@");
  ////////////////////
  // Process the effects of source or sink functions that are called
  for (auto *Callee : icfg.getCalleesOfCallAt(callSite)) {
    string FunctionName = cxx_demangle(Callee->getName().str());
    LOG_IF_ENABLE(BOOST_LOG_SEV(lg, DEBUG) << "F:" << Callee->getName().str());
    LOG_IF_ENABLE(BOOST_LOG_SEV(lg, DEBUG) << "demangled F:" << FunctionName);
    if (SourceSinkFunctions.isSource(FunctionName)) {
      // process generated taints
      LOG_IF_ENABLE(BOOST_LOG_SEV(lg, DEBUG) << "Plugin SOURCE effects");
      auto Source = SourceSinkFunctions.getSource(FunctionName);
      set<IFDSTaintAnalysis::d_t> ToGenerate;
      llvm::ImmutableCallSite CallSite(callSite);
      for (auto FormalIndex : Source.TaintedArgs) {
        IFDSTaintAnalysis::d_t V = CallSite.getArgOperand(FormalIndex);
        // Insert the value V that gets tainted
        ToGenerate.insert(V);
        // We also have to collect all aliases of V and generate them
        auto PTS = icfg.getWholeModulePTG().getPointsToSet(V);
        ////// jinseob //////
        //printDataFlowFact(std::cout, V);
        ////////////////////
        for (auto Alias : PTS) {
          ToGenerate.insert(Alias);
        }
      }
      if (Source.TaintsReturn) {
        LOG_IF_ENABLE(BOOST_LOG_SEV(lg, DEBUG) << "demangled F:" << FunctionName);
        ToGenerate.insert(callSite);
      }
      return make_shared<GenAll<IFDSTaintAnalysis::d_t>>(ToGenerate,
                                                         zeroValue());
    }
    if (SourceSinkFunctions.isSink(FunctionName)) {
      // process leaks
      LOG_IF_ENABLE(BOOST_LOG_SEV(lg, DEBUG) << "Plugin SINK effects");
      struct TAFF : FlowFunction<IFDSTaintAnalysis::d_t> {
        llvm::ImmutableCallSite callSite;
        IFDSTaintAnalysis::m_t calledMthd;
        TaintSensitiveFunctions::SinkFunction Sink;
        map<IFDSTaintAnalysis::n_t, set<IFDSTaintAnalysis::d_t>> &Leaks;
        const IFDSTaintAnalysis *taintanalysis;
        TAFF(llvm::ImmutableCallSite cs, IFDSTaintAnalysis::m_t calledMthd,
             TaintSensitiveFunctions::SinkFunction s,
             map<IFDSTaintAnalysis::n_t, set<IFDSTaintAnalysis::d_t>> &leaks,
             const IFDSTaintAnalysis *ta)
            : callSite(cs), calledMthd(calledMthd), Sink(s), Leaks(leaks),
              taintanalysis(ta) {}
        set<IFDSTaintAnalysis::d_t>
        computeTargets(IFDSTaintAnalysis::d_t source) override {
          // check if a tainted value flows into a sink
          // if so, add to Leaks and return id
          if (!taintanalysis->isZeroValue(source)) {
            for (unsigned Idx = 0; Idx < callSite.getNumArgOperands(); ++Idx) {
              if (source == callSite.getArgOperand(Idx) &&
                  Sink.isLeakedArg(Idx)) {
                cout << "FOUND LEAK" << endl;
                Leaks[callSite.getInstruction()].insert(source);
              }
            }
          }
          return {source};
        }
      };
      return make_shared<TAFF>(llvm::ImmutableCallSite(callSite), Callee,
                               SourceSinkFunctions.getSink(FunctionName), Leaks,
                               this);
    }
  }
  // Otherwise pass everything as it is
  return Identity<IFDSTaintAnalysis::d_t>::getInstance();
}

shared_ptr<FlowFunction<IFDSTaintAnalysis::d_t>>
IFDSTaintAnalysis::getSummaryFlowFunction(IFDSTaintAnalysis::n_t callStmt,
                                          IFDSTaintAnalysis::m_t destMthd) {
  SpecialSummaries<IFDSTaintAnalysis::d_t> &specialSummaries =
      SpecialSummaries<IFDSTaintAnalysis::d_t>::getInstance();
  string FunctionName = cxx_demangle(destMthd->getName().str());
  // If we have a special summary, which is neither a source function, nor
  // a sink function, then we provide it to the solver.
  if (specialSummaries.containsSpecialSummary(FunctionName) &&
      !SourceSinkFunctions.isSource(FunctionName) &&
      !SourceSinkFunctions.isSink(FunctionName)) {
    return specialSummaries.getSpecialFlowFunctionSummary(FunctionName);
  } else {
    // Otherwise we indicate, that not special summary exists
    // and the solver thus calls the call flow function instead
    return nullptr;
  }
}

map<IFDSTaintAnalysis::n_t, set<IFDSTaintAnalysis::d_t>>
IFDSTaintAnalysis::initialSeeds() {
  auto &lg = lg::get();
  LOG_IF_ENABLE(BOOST_LOG_SEV(lg, DEBUG)
                << "IFDSTaintAnalysis::initialSeeds()");
  // If main function is the entry point, commandline arguments have to be
  // tainted. Otherwise we just use the zero value to initialize the analysis.
  map<IFDSTaintAnalysis::n_t, set<IFDSTaintAnalysis::d_t>> SeedMap;
  for (auto &EntryPoint : EntryPoints) {
    if (EntryPoint == "main") {
      set<IFDSTaintAnalysis::d_t> CmdArgs;
      for (auto &Arg : icfg.getMethod(EntryPoint)->args()) {
        CmdArgs.insert(&Arg);
      }
      CmdArgs.insert(zeroValue());
      SeedMap.insert(
          make_pair(&icfg.getMethod(EntryPoint)->front().front(), CmdArgs));
    } else {
      set<IFDSTaintAnalysis::d_t> EntryArgs;
      for (auto &Arg : icfg.getMethod(EntryPoint)->args()) {
        EntryArgs.insert(&Arg);
      }
      EntryArgs.insert(zeroValue());
      SeedMap.insert(make_pair(&icfg.getMethod(EntryPoint)->front().front(), EntryArgs));

    }
  }
  return SeedMap;
}

IFDSTaintAnalysis::d_t IFDSTaintAnalysis::createZeroValue() {
  auto &lg = lg::get();
  LOG_IF_ENABLE(BOOST_LOG_SEV(lg, DEBUG)
                << "IFDSTaintAnalysis::createZeroValue()");
  // create a special value to represent the zero value!
  return LLVMZeroValue::getInstance();
}

bool IFDSTaintAnalysis::isZeroValue(IFDSTaintAnalysis::d_t d) const {
  return isLLVMZeroValue(d);
}

void IFDSTaintAnalysis::printNode(ostream &os, IFDSTaintAnalysis::n_t n) const {
  os << llvmIRToString(n);
}

void IFDSTaintAnalysis::printDataFlowFact(ostream &os,
                                          IFDSTaintAnalysis::d_t d) const {
  os << llvmIRToString(d);
}

void IFDSTaintAnalysis::printMethod(ostream &os,
                                    IFDSTaintAnalysis::m_t m) const {
  os << m->getName().str();
}

void IFDSTaintAnalysis::printIFDSReport(
    std::ostream &os, SolverResults<n_t, d_t, BinaryDomain> &SR) {
  os << "\n----- Found the following leaks -----\n";
  if (Leaks.empty()) {
    os << "No leaks found!\n";
  } else {
    for (auto Leak : Leaks) {
      os << "At instruction\nIR  : " << llvmIRToString(Leak.first) << '\n';
      os << llvmValueToSrc(Leak.first);
      os << "\n\nLeak(s):\n";
      for (auto LeakedValue : Leak.second) {
        os << "IR  : ";
        // Get the actual leaked alloca instruction if possible
        if (auto Load = llvm::dyn_cast<llvm::LoadInst>(LeakedValue)) {
          os << llvmIRToString(Load->getPointerOperand()) << '\n'
             << llvmValueToSrc(Load->getPointerOperand()) << '\n';

        } else {
          os << llvmIRToString(LeakedValue) << '\n'
             << llvmValueToSrc(LeakedValue) << '\n';
        }
      }
      os << "-------------------\n";
    }
  }
}

} // namespace psr
