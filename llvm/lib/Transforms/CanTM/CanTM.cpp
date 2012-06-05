//===- CanTM.cpp - Example code from "Writing an LLVM Pass" ---------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements two versions of the LLVM "CanTM World" pass described
// in docs/WritingAnLLVMPass.html
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "CanTM"
#include "llvm/Pass.h"
#include "llvm/Module.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Instructions.h"
#include "llvm/Constants.h"
#include "llvm/Support/CFG.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/AliasSetTracker.h"
#include "llvm/LLVMContext.h"
#include <map>
#include <queue>
#include <vector>
#include <set>
#include <algorithm>

using namespace llvm;

#define DEBUG_INFO 1

STATISTIC(num_loads,    "Number of Loads (total)");
STATISTIC(num_loads_on_phi,    "Number of Loads on PHI values(total)");
STATISTIC(num_loads_on_phi_compressed,    "Number of Loads on PHI values compressed");
STATISTIC(num_loads_from_function_call, "Number of Loads from function calls");
STATISTIC(num_loads_skipped, "Number of Loads skipped (total)");
STATISTIC(num_loads_skipped_from_previous_store, "Number of Loads skipped from previous store");
STATISTIC(num_loads_unprocessed, "Number of Loads unprocessed");
STATISTIC(num_loads_compressed, "Number of Loads compressed");
STATISTIC(num_loads_compressed_from_previous_store, "Number of Loads compressed from previous store");
STATISTIC(num_stores,    "Number of Stores (total)");
STATISTIC(num_stores_on_phi,    "Number of Stores on PHI values(total)");
STATISTIC(num_stores_on_phi_compressed,    "Number of Stores on PHI values compressed");
STATISTIC(num_stores_skipped, "Number of Stores skipped (total)");
STATISTIC(num_stores_unprocessed, "Number of Stores unprocessed");
STATISTIC(num_stores_compressed, "Number of Stores compressed");
STATISTIC(aliased_total, "Number of Aliased values - Total");
STATISTIC(aliased_to_escape, "Number of Aliased values - Escaped");
STATISTIC(aliased_to_not_escape, "Number of Aliased values - Not escaped");

namespace {
    void printVal(Value *v); 
    void printInst(Instruction *I, bool var = false); 
    void printUser(User *u); 

    class LoadStore {
        private:
        std::set<Value*> loads;
        std::set<Value*> stores;
        std::set<Value*> orig_loads;
        std::set<Value*> orig_stores;
        std::set<PHINode*> phi_loads;
        std::set<PHINode*> phi_stores;
        std::set<Value*> prev_loads;
        std::set<Value*> prev_stores;


        public:

        bool empty() {
            return loads.empty() && stores.empty();
        }


        bool containsLoadTo(Value *v) {
            if (orig_loads.find(v) == orig_loads.end()) {
                return false;
            }

            return true;
        }

        bool containsStoreFrom(Value *v) {
            if (orig_stores.find(v) == orig_stores.end()) {
                return false;
            }

            return true;
        }

        bool canCompressLoadPhiNode(PHINode* phiNode, std::set<Value*> &prev_loads, std::set<Value*> &prev_stores) {
            for (unsigned int i = 0; i < phiNode->getNumIncomingValues(); ++i) {
                Value *v = phiNode->getIncomingValue(i);
                if (PHINode* childPhiNode = dyn_cast<PHINode>(v)) {
                    if (!canCompressLoadPhiNode(phiNode, prev_loads, prev_stores))
                        return false;
                } else if (prev_stores.find(v) != prev_stores.end()) {
                    continue;
                } else if (prev_loads.find(v) != prev_loads.end()) {
                    continue;
                } else if (stores.find(v) != stores.end()) {
                    continue;
                } else if (loads.find(v) != loads.end()) {
                    continue;
                } else {
                    return false;
                }
            }
            return true;
        }

        bool canCompressStorePhiNode(PHINode* phiNode, std::set<Value*> &prev_loads, std::set<Value*> &prev_stores) {
            for (unsigned int i = 0; i < phiNode->getNumIncomingValues(); ++i) {
                Value *v = phiNode->getIncomingValue(i);
                if (PHINode* childPhiNode = dyn_cast<PHINode>(v)) {
                    if (!canCompressStorePhiNode(phiNode, prev_loads, prev_stores))
                        return false;
                } else if (prev_stores.find(v) != prev_stores.end()) {
                    continue;
                } else if (stores.find(v) != stores.end()) {
                    continue;
                } else {
                    return false;
                }
            }
            return true;
        }

        void compressPhiNodes() {
            for (auto loads_it = phi_loads.begin(), loads_it_e = phi_loads.end(); loads_it != loads_it_e; ++loads_it) {
                PHINode* phiNode = *loads_it;
                if (canCompressLoadPhiNode(phiNode, prev_loads, prev_stores)) {
                    ++num_loads_on_phi_compressed;

                    auto phi_it = loads.find(phiNode);
                    if (phi_it != loads.end())
                        loads.erase(phi_it);
                }
            }

            for (auto stores_it = phi_stores.begin(), stores_it_e = phi_stores.end(); stores_it != stores_it_e; ++stores_it ) {
                PHINode* phiNode = *stores_it;
                if (canCompressStorePhiNode(phiNode, prev_loads, prev_stores)) {
                    ++num_stores_on_phi_compressed;

                    auto phi_it = stores.find(phiNode);
                    if (phi_it != stores.end())
                        stores.erase(phi_it);
                }
            }
        }

        bool insertLoad(Value *v) {
            if (PHINode* phiNode = dyn_cast<PHINode>(v)) {
                ++num_loads_on_phi;
                if (phi_stores.find(phiNode) == phi_stores.end()) {
                    phi_loads.insert(phiNode);
                }
            }

            if (stores.find(v) != stores.end()) {
                ++num_loads_skipped_from_previous_store;
                return false;
            }
            std::pair<std::set<Value*>::iterator,bool> ret = loads.insert(v);
            return ret.second;
        }

        bool insertStore(Value *v) {
            if (PHINode* phiNode = dyn_cast<PHINode>(v)) {
                ++num_stores_on_phi;
                phi_stores.insert(phiNode);
            }

            std::pair<std::set<Value*>::iterator,bool> ret = stores.insert(v);
            return ret.second;
        }

        void doneProcessing() {
            orig_loads = loads;
            orig_stores = stores;

            std::set<Value*> prev_loads;
            std::set<Value*> prev_stores;
        }
        bool compressWithPreviousLoad(Value* v);
        bool compressWithPreviousStore(Value* v);
        void compress(std::set<Value*> &prev_loads, std::set<Value*> &prev_stores);

        //TODO: use iterator
        void copyLoads(std::vector<Value *> &v) {
            v.insert(v.end(), loads.begin(), loads.end());
        }
        void copyStores(std::vector<Value *> &v) {
            v.insert(v.end(), stores.begin(), stores.end());
        }
        void copyLoads(std::set<Value *> &s) {
            for (auto loads_it = loads.begin(), loads_it_e = loads.end(); loads_it != loads_it_e; ++loads_it) {
                s.insert(*loads_it);
            }
        }
        void copyStores(std::set<Value *> &s) {
            for (auto stores_it = stores.begin(), stores_it_e = stores.end(); stores_it != stores_it_e; ++stores_it) {
                s.insert(*stores_it);
            }
        }

        unsigned numLoads() {
            return loads.size();
        }

        unsigned numStores() {
            return stores.size();
        }

        void debugPrint() {
            errs() << loads.size() << " loads and " << stores.size() << " stores." << "\n";
            errs() << "Load Set: ";
            for (auto loads_it = loads.begin(), loads_it_e = loads.end(); loads_it != loads_it_e; ++loads_it) {
                printVal(*loads_it);
                errs() << " ";
            }
            errs() << "\n";
            errs() << "Stores Set: ";
            for (auto stores_it = stores.begin(), stores_it_e = stores.end(); stores_it != stores_it_e; ++stores_it) {
                printVal(*stores_it);
                errs() << " ";
            }
            errs() << "\n";
        }
    };

    // CanTM - The first implementation, without getAnalysisUsage.
    struct CanTM : public ModulePass {
        static char ID; // Pass identification, replacement for typeid
        CanTM() : ModulePass(ID) {}

        void analyizeBB(BasicBlock *bb, AliasSetTracker* aliasTracker);
        void getLoadsStores(BasicBlock *bb, std::set<Value*> &loads, std::set<Value*> &stores);
        void compressFunction(Function *f, std::set<unsigned> &reservedLoads, std::set<unsigned> &reservedStores);
        bool canEscape(Value *v);
        bool computeEscape(Value *v);
        void updateEscapability(Value *v, bool escapable);
        bool insertAlias(Value *from, Value *to);
        std::map<BasicBlock *, LoadStore> bbMap;
        std::map<Function *, AliasSetTracker *> aliasMap;
        std::map<Value *, bool> fCanEscape;
        std::set<Function *> fAdded;
        std::set<BasicBlock *> fFunctionBlocks;
        std::queue<Function *> fQueue;

        virtual bool runOnModule(Module &M);
        virtual void getAnalysisUsage(AnalysisUsage &AU) const {
            //BasicBlockPass::getAnalysisUsage(AU);
            AU.addRequired<AliasAnalysis>();
            AU.addPreserved<AliasAnalysis>();
        }


        Function *stm_reserve;
        Function *tx;
        AliasAnalysis *AA;
    };
}

char CanTM::ID = 0;
#if 1
static RegisterPass<CanTM> X("CanTM", "CanTM World Pass");
#else
static const char CanTM_name[] = "CanTM World Pass";
INITIALIZE_PASS_BEGIN(CanTM, "CanTM", CanTM_name, false, false)
INITIALIZE_AG_DEPENDENCY(AliasAnalysis)
    INITIALIZE_PASS_END(CanTM, "CanTM", CanTM_name, false, false)
#endif

    namespace {
        void printVal(Value *v) {
            errs() << "Defining (";
            if (Instruction *I  = dyn_cast<Instruction>(v)) {
                printInst(I);
            } else {
                errs() << "NOPE";
            }
            errs() << ")";
            const Type* type = v->getType();
            if (type->isIntegerTy()) {
                errs() << "Integer" << type->getIntegerBitWidth() << "(";
                if (ConstantInt  *ci = dyn_cast<ConstantInt>(&*v)) {
                    errs() << ci->getZExtValue();
                }
            } else if (type->isPointerTy()) {
                errs() << "Pointer(";
                errs().write_escaped(v->getName());
            } else if (type->isFunctionTy()) {
                errs() << "Function(";
                errs().write_escaped(v->getName());
            } else {
                errs() << "Unknown(";
            }
            errs() << ")";
        }

        void printInst(Instruction *I, bool var) {
            if (LoadInst *li = dyn_cast<LoadInst>(I)) {
                errs() << "LoadInst";
                if (var) {
                    errs() << " ";
                    printVal(li->getPointerOperand());
                }
            } else if (isa<AllocaInst>(I)) {
                errs() << "AllocaInst";
            } else if (isa<ReturnInst>(I)) {
                errs() << "ReturnInst"; 
            } else if (StoreInst *si = dyn_cast<StoreInst>(I)) {
                errs() << "StoreInst";
                if (var) {
                    errs() << " ";
                    printVal(si->getValueOperand());
                    errs() << " ";
                    printVal(si->getPointerOperand());
                }
            } else  if (CallInst *ci = dyn_cast<CallInst>(I)) {
                errs() << "CallInst";
                if (var) {
                    errs() << " (" << ci->getNumArgOperands() << " args) ";
                    for (unsigned arg_num = 0; arg_num < ci->getNumArgOperands(); ++arg_num) {
                        errs() << arg_num << ": ";
                        printVal(ci->getArgOperand(arg_num));
                        errs() << " ";
                    }
                }
            } else if (isa<BinaryOperator>(I)) {
                errs() << "BinaryOperator";
            } else if (isa<UnaryInstruction>(I)) {
                errs() << "UnaryInstruction";
            } else if (isa<SelectInst>(I)) {
                errs() << "SelectInst";
            } else if (isa<TerminatorInst>(I)) {
                errs() << "TerminatorInst";
            } else if (isa<PHINode>(I)) {
                errs() << "PHINode";
            } else {
                errs() << "Unknown";
            }
        }

        void printUser(User *u) {
            if (Instruction *i = dyn_cast<Instruction>(u)) {
                printInst(i);
            } else {
                errs() << "Unknown User";
            }
        }
    }

bool CanTM::canEscape(Value *v) {
    auto it = fCanEscape.find(v);
    if (it != fCanEscape.end()) {
        return (*it).second;
    }

    return false;
}

void CanTM::updateEscapability(Value *v, bool escapable) {
    // Check if value has already been processed
    auto it = fCanEscape.find(v);
    if (it == fCanEscape.end()) {
        fCanEscape[v] = escapable;
    }
}

bool LoadStore::compressWithPreviousLoad(Value* v) {
    prev_loads.insert(v);
    auto loads_it = loads.find(v);
    if (loads_it != loads.end()) {
        ++num_loads_compressed;
        loads.erase(loads_it);
        return true;
    }
    return false;
}

bool LoadStore::compressWithPreviousStore(Value* v) {
    prev_stores.insert(v);
    bool retVal = false;

    if (compressWithPreviousLoad(v)) {
        ++num_loads_compressed_from_previous_store;
        retVal = true;
    }

    auto stores_it = stores.find(v);
    if (stores_it != stores.end()) {
        ++num_stores_compressed;
        stores.erase(stores_it);
        retVal = true;
    }

    return retVal;
}

void LoadStore::compress(std::set<Value*> &prev_loads, std::set<Value*> &prev_stores) {
    for (auto loads_it = prev_loads.begin(), loads_it_e = prev_loads.end(); loads_it != loads_it_e; ++loads_it)
        compressWithPreviousLoad(*loads_it);

    for (auto stores_it = prev_stores.begin(), stores_it_e = prev_stores.end(); stores_it != stores_it_e; ++stores_it )
        compressWithPreviousStore(*stores_it);
}

void CanTM::analyizeBB(BasicBlock *bb, AliasSetTracker* aliasTracker) {
    errs() << "BB: " << bb << "\n";
    LoadStore ls;
    for (auto instr_i = bb->begin(), instr_e = bb->end(); instr_i != instr_e; ++instr_i) {
        errs() << "Intr: ";
        printInst(&*instr_i, true);
        if (LoadInst *li = dyn_cast<LoadInst>(&*instr_i)) {
            //if (!computeEscape(li->getPointerOperand())) {
            //}
            ++num_loads;
            if (li->getPointerOperand()->hasName()) {
                if (!ls.insertLoad(li->getPointerOperand())) {
                    ++num_loads_skipped;
                }
            } else {
                ++num_loads_unprocessed;
            }

            AliasSet* as = aliasTracker->getAliasSetForPointerIfExists(li, AA->getTypeStoreSize(li->getType()), li->getMetadata(LLVMContext::MD_tbaa));
            if (as) {
                errs() << "Value: (";
                printVal(li);
                errs() << ") has alias set\n";
            } else {
                errs() << "Value: (";
                printVal(li);
                errs() << ") has NO alias set\n";
            }
        } else if (StoreInst *si = dyn_cast<StoreInst>(&*instr_i)) {
            ++num_stores;
            auto valueOp = si->getValueOperand();
            auto pointerOp = si->getPointerOperand();
            if (pointerOp->hasName()) {
                //if (!computeEscape(pointerOp)) {
                //}
                /*
                   if (valueOp->getType()->isPointerTy() && valueOp->hasName()) {
                   ls.insertAlias()
                   ++num_stores_aliased;
                   }*/
                if (!ls.insertStore(pointerOp)) {
                    ++num_stores_skipped;
                }
            } else {
                ++num_stores_unprocessed;
            }
        } else if (CallInst *ci = dyn_cast<CallInst>(&*instr_i)) {
            if (instr_i != bb->begin()) {
                analyizeBB(bb->splitBasicBlock(instr_i), aliasTracker);
            } else {
                for (unsigned arg_num = 0; arg_num < ci->getNumArgOperands(); ++arg_num) {
                    ++num_loads;
                    ++num_loads_from_function_call;
                    if (ci->getArgOperand(arg_num)->hasName()) {
                        if (!ls.insertLoad(ci->getArgOperand(arg_num))) {
                            ++num_loads_skipped;
                        }
                    } else {
                        ++num_loads_unprocessed;
                    }
                }
                fFunctionBlocks.insert(bb);
                Function* called = ci->getCalledFunction();
                auto it = fAdded.find(called);
                if (it == fAdded.end()) {
                    fQueue.push(called);
                    fAdded.insert(called);
                }
                ++instr_i;
                if (instr_i != instr_e)
                    analyizeBB(bb->splitBasicBlock(instr_i), aliasTracker);
            }
            break;
        } else if (AllocaInst *ai = dyn_cast<AllocaInst>(&*instr_i)) {
            AliasSet* as = aliasTracker->getAliasSetForPointerIfExists(ai, AA->getTypeStoreSize(ai->getType()), ai->getMetadata(LLVMContext::MD_tbaa));
            if (as) {
                errs() << "Value: (";
                printVal(ai);
                errs() << ") has alias set\n";
            } else {
                errs() << "Value: (";
                printVal(ai);
                errs() << ") has NO alias set\n";
            }
            ++instr_i;
            if (instr_i != instr_e)
                analyizeBB(bb->splitBasicBlock(instr_i), aliasTracker);
            break;
        }
        errs() << "\n";
    }
    if (!ls.empty()) {
        errs() << "Analyized BB: " << bb << " ";
        ls.debugPrint();
        ls.doneProcessing();
        bbMap[bb] = ls;
    }
}

void CanTM::getLoadsStores(BasicBlock *bb, std::set<Value*> &loads, std::set<Value*> &stores) {
    errs() << "Compressing BB (begin): " << bb << "\n";
    for (pred_iterator pi = pred_begin(bb), pi_e = pred_end(bb); pi != pi_e; ++pi) {
        BasicBlock *pred = *pi;
        //errs() << "Compressing pred: " << pred << "\n";
        if (pi == pred_begin(bb)) {
            getLoadsStores(pred, loads, stores);
        } else {
            std::set<Value*> cur_pred_loads;
            std::set<Value*> cur_pred_stores;
            getLoadsStores(pred, cur_pred_loads, cur_pred_stores);
            std::set<Value*> new_pred_loads;
            std::set<Value*> new_pred_stores;
            set_intersection (cur_pred_loads.begin(), cur_pred_loads.end(), loads.begin(), loads.end(), std::inserter( new_pred_loads, new_pred_loads.begin() ));
            set_intersection (cur_pred_loads.begin(), cur_pred_loads.end(), stores.begin(), stores.end(), std::inserter( new_pred_loads, new_pred_loads.begin() ));
            set_intersection (cur_pred_stores.begin(), cur_pred_stores.end(), loads.begin(), loads.end(), std::inserter( new_pred_loads, new_pred_loads.begin() ));
            set_intersection (cur_pred_stores.begin(), cur_pred_stores.end(), stores.begin(), stores.end(), std::inserter( new_pred_stores, new_pred_stores.begin()));
            loads = new_pred_loads;
            stores = new_pred_stores;
        }
    }

    errs() << "Compressing BB (middle): " << bb << "\n";
    LoadStore ls = bbMap[bb];
    ls.compress(loads, stores);
    ls.compressPhiNodes();
    bbMap[bb] = ls;

    if (fFunctionBlocks.find(bb) != fFunctionBlocks.end()) {
        auto instr_i = bb->begin();
        CallInst *ci = dyn_cast<CallInst>(&*instr_i);
        std::set<unsigned> reservedLoads;
        std::set<unsigned> reservedStores;
        errs() << "Call Inst has " << ci->getNumArgOperands() << " args) ";
        for (unsigned arg_num = 0; arg_num < ci->getNumArgOperands(); ++arg_num) {
            errs() << arg_num << ": ";
            printVal(ci->getArgOperand(arg_num));
            if (ls.containsLoadTo(ci->getArgOperand(arg_num))) {
                errs() << " LoadReserved ";
                reservedLoads.insert(arg_num);
            }
            if (ls.containsStoreFrom(ci->getArgOperand(arg_num))) {
                errs() << "StoreReserved ";
                reservedStores.insert(arg_num);
            }

            errs() << " ";
        }
        compressFunction(ci->getCalledFunction(), reservedLoads, reservedStores);
    }

    ls.copyLoads(loads);
    ls.copyStores(stores);
    errs() << "Compressed BB (end): " << bb << " ";
    ls.debugPrint();
    //loads.insert(ls.loads.begin(), ls.loads.end());
    //stores.insert(ls.stores.begin(), ls.stores.end());
}

void CanTM::compressFunction(Function *f, std::set<unsigned> &reservedLoads, std::set<unsigned> &reservedStores) {
    errs() << "=========================\n";
    errs() << "Compressing Func: ";
    errs().write_escaped(f->getName()) << '\n';
    errs() << "=========================\n";
    unsigned i = 0;
    for (auto arg_iter=f->arg_begin(), arg_iter_end = f->arg_end(); arg_iter != arg_iter_end; ++arg_iter) {
        errs() << "Arg " << i << " ";
        printVal(arg_iter);
        for (auto i_f = f->begin(), ie_f = f->end(); i_f != ie_f; i_f++) {
            BasicBlock *bb = i_f;
            LoadStore ls = bbMap[bb];
            // TODO: FIXME For now we'll assume all arguments are properly reserved
            if (ls.compressWithPreviousLoad(arg_iter)) {
                errs() << "Load compressed BB: (" << bb << ") ";
            }
            if (ls.compressWithPreviousStore(arg_iter)) {
                errs() << "Load compressed BB: (" << bb << ") ";
            }
            bbMap[bb] = ls;
        }
        errs() << "\n";
        ++i;
    }

    // TODO: There may be multiple ending blocks
    auto i_f = f->end();
    --i_f;
    BasicBlock *bb = i_f;
    std::set<Value*> loads;
    std::set<Value*> stores;
    getLoadsStores(bb, loads, stores);
}

bool CanTM::runOnModule(Module &M) {
    AA = &getAnalysis<AliasAnalysis>();
    errs() << "Processing Module: ";
    errs().write_escaped(M.getModuleIdentifier()) << '\n';

    //TODO: Link to library
    stm_reserve = M.begin();

    // Automatically add *foo*() and *tx*() functions to system
    // TODO: Use clang to insert LLVM instructions to start/end a transaction
    for (auto i = M.begin(), ie = M.end(); i != ie; ++i) {
        Function* f = i;
        if (f->getName().str().find("foo") != std::string::npos) {
            fQueue.push(f);
            fAdded.insert(f);
            tx = f;
        }
        if (f->getName().str().find("tx") != std::string::npos) {
            fQueue.push(f);
            fAdded.insert(f);
            tx = f;
            break;
        }
    }

    // Mark all globals as escapable, including all aliases
    // TODO: If a global is accessed by a single transaction it
    // doesn't need to be marked as so
    for (Module::global_iterator G = M.global_begin(), E = M.global_end();
        G != E; ++G) {
        updateEscapability(G, true);
    }

    // Process each function
    while (!fQueue.empty()) {
        Function* f = fQueue.front();
        fQueue.pop();

        errs() << "=========================\n";
        errs() << "Processing Func: ";
        errs().write_escaped(f->getName()) << '\n';
        errs() << "=========================\n";
        AliasSetTracker* aliasTracker = new AliasSetTracker(*AA);
        for (auto i_f = f->begin(), ie_f = f->end(); i_f != ie_f; i_f++) {
            //aliasTracker->add(*i_f);
        }
        for (auto i_f = f->begin(), ie_f = f->end(); i_f != ie_f; i_f++) {
            BasicBlock *bb = i_f;
            analyizeBB(bb, aliasTracker);
        }
        aliasMap[f] = aliasTracker;
    }

    // Start off by compressing the root tx function,
    // this should in turn compress the subsequent ones
    std::set<unsigned> reservedLoads;
    std::set<unsigned> reservedStores;
    compressFunction(tx, reservedLoads, reservedStores);

    //TODO: Merge basic blocks get rid on unconditional branches

    for (auto it = bbMap.begin(), it_end = bbMap.end(); it != it_end; ++it) {
        BasicBlock *bb = (*it).first;
        LoadStore ls = (*it).second;
        if (ls.empty())
            continue;
        errs() << "Instrumenting BB: " << bb << " ";
        ls.debugPrint();
        std::vector<Value*> args;
        ConstantInt* num_args = ConstantInt::get(IntegerType::get(M.getContext(), 32), 2 + ls.numLoads() + ls.numStores(), true);
        args.push_back(num_args);
        ConstantInt* num_loads = ConstantInt::get(IntegerType::get(M.getContext(), 32), ls.numLoads(), true);
        args.push_back(num_loads);
        ls.copyLoads(args);
        ConstantInt* num_stores = ConstantInt::get(IntegerType::get(M.getContext(), 32), ls.numStores(), true);
        args.push_back(num_stores);
        ls.copyStores(args);
        auto InsertPos = bb->begin();
        while (isa<PHINode>(InsertPos))
            ++InsertPos;

        CallInst::Create(stm_reserve, args, "", InsertPos);
    }


    // TODO: return false if no changes were made
    return true;
}
