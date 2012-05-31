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
#include <map>
#include <queue>
#include <vector>
#include <set>
#include <algorithm>

using namespace llvm;

#define DEBUG_INFO 1

STATISTIC(CanTMCounter, "Counts number of functions greeted");

namespace {
    unsigned num_loads;
    unsigned num_loads_from_function_call;
    unsigned num_loads_skipped;
    unsigned num_loads_skipped_from_previous_store;
    unsigned num_loads_unprocessed;
    unsigned num_loads_compressed;
    unsigned num_loads_compressed_from_previous_store;
    unsigned num_stores;
    unsigned num_stores_skipped;
    unsigned num_stores_unprocessed;
    unsigned num_stores_compressed;

    void printVal(Value *v);

    class LoadStore {
        std::set<Value*> loads;
        std::set<Value*> stores;
        std::set<Value*> pred_loads;
        std::set<Value*> pred_stores;
        
      public:

        bool empty() {
            return loads.empty() && stores.empty();
        }

        bool insertLoad(Value *v) {
            if (stores.find(v) != stores.end()) {
                ++num_loads_skipped_from_previous_store;
                return false;
            }
            std::pair<std::set<Value*>::iterator,bool> ret = loads.insert(v);
            return ret.second;
        }

        bool insertStore(Value *v) {
            std::pair<std::set<Value*>::iterator,bool> ret = stores.insert(v);
            return ret.second;
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

        void analyizeBB(BasicBlock *bb);
        void getLoadsStores(BasicBlock *bb, std::set<Value*> &loads, std::set<Value*> &stores);
        void compressFunction(Function *f);
        std::map<BasicBlock *, LoadStore> bbMap;
        std::set<Function *> fAdded;
        std::set<BasicBlock *> fFunctionBlocks;
        std::queue<Function *> fQueue;

        virtual bool runOnModule(Module &M);

        Function *stm_reserve;
        Function *tx;
    };
}

char CanTM::ID = 0;
static RegisterPass<CanTM> X("CanTM", "CanTM World Pass");


bool LoadStore::compressWithPreviousLoad(Value* v) {
    auto loads_it = loads.find(v);
    if (loads_it != loads.end()) {
#if DEBUG_INFO
        errs() << "Removed a load element (due to store): ";
        printVal(v);
        errs() << "\n";
#endif
        ++num_loads_compressed;
        loads.erase(loads_it);
    }
}

bool LoadStore::compressWithPreviousStore(Value* v) {
    if (compressWithPreviousLoad(v))
        ++num_loads_compressed_from_previous_store;

    auto stores_it = stores.find(v);
    if (stores_it != stores.end()) {
#if DEBUG_INFO
        errs() << "Removed a store element: ";
        printVal(v);
        errs() << "\n";
#endif
        ++num_stores_compressed;
        stores.erase(stores_it);
    }
}

void LoadStore::compress(std::set<Value*> &prev_loads, std::set<Value*> &prev_stores) {
    for (auto loads_it = prev_loads.begin(), loads_it_e = prev_loads.end(); loads_it != loads_it_e; ++loads_it)
        compressWithPreviousLoad(*loads_it);

    for (auto stores_it = prev_stores.begin(), stores_it_e = prev_stores.end(); stores_it != stores_it_e; ++stores_it )
        compressWithPreviousStore(*stores_it);
}

namespace {
void printVal(Value *v) {
    const Type* type = v->getType();
    if (type->isIntegerTy()) {
        errs() << "Integer" << type->getIntegerBitWidth() << "(";
        if (ConstantInt  *ci = dyn_cast<ConstantInt>(&*v)) {
            errs() << ci->getZExtValue();
        }
    } else if (type->isPointerTy()) {
        errs() << "Pointer(";
        errs().write_escaped(v->getName());
    } else {
        errs() << "Unknown(";
    }
    errs() << ")";
}
}

void CanTM::analyizeBB(BasicBlock *bb) {
    errs() << "BB: " << bb << "\n";
    LoadStore ls;
    for (auto instr_i = bb->begin(), instr_e = bb->end(); instr_i != instr_e; ++instr_i) {
        errs() << "Intr: ";
        if (LoadInst *li = dyn_cast<LoadInst>(&*instr_i)) {
            ++num_loads;
            errs() << "Load ";
            printVal(li->getPointerOperand());
            if (li->getPointerOperand()->hasName()) {
                if (!ls.insertLoad(li->getPointerOperand())) {
                    ++num_loads_skipped;
                }
            } else {
                ++num_loads_unprocessed;
            }
        } else if (StoreInst *si = dyn_cast<StoreInst>(&*instr_i)) {
            ++num_stores;
            errs() << "Store ";
            printVal(si->getValueOperand());
            errs() << " ";
            printVal(si->getPointerOperand());
            if (si->getPointerOperand()->hasName()) {
                if (!ls.insertStore(si->getPointerOperand())) {
                    ++num_stores_skipped;
                }
            } else {
                ++num_stores_unprocessed;
            }
        } else if (CallInst *ci = dyn_cast<CallInst>(&*instr_i)) {
            errs() << "Call (" << ci->getNumArgOperands() << " args) ";
            if (instr_i != bb->begin()) {
                analyizeBB(bb->splitBasicBlock(instr_i));
            } else {
                for (unsigned arg_num = 0; arg_num < ci->getNumArgOperands(); ++arg_num) {
                    errs() << arg_num << ": ";
                    printVal(ci->getArgOperand(arg_num));
                    errs() << " ";
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
                    analyizeBB(bb->splitBasicBlock(instr_i));
            }
            break;
        } else if (AllocaInst *ai = dyn_cast<AllocaInst>(&*instr_i)) {
            errs() << "Alloc";
            ++instr_i;
            if (instr_i != instr_e)
                analyizeBB(bb->splitBasicBlock(instr_i));
            break;
        } else {
            errs() << "Unknown";
        }
        errs() << "\n";
    }
    if (!ls.empty()) {
        errs() << "Analyized BB: " << bb << " ";
        ls.debugPrint();
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
    bbMap[bb] = ls;

    if (fFunctionBlocks.find(bb) != fFunctionBlocks.end()) {
        auto instr_i = bb->begin();
        CallInst *ci = dyn_cast<CallInst>(&*instr_i);
        compressFunction(ci->getCalledFunction());
    }

    ls.copyLoads(loads);
    ls.copyStores(stores);
   /* 
    for (auto loads_it = ls.loads.begin(), loads_it_e = ls.loads.end(); loads_it != loads_it_e; ++loads_it) {
        loads.insert(*loads_it);
    }
    for (auto stores_it = ls.stores.begin(), stores_it_e = ls.stores.end(); stores_it != stores_it_e; ++stores_it) {
        stores.insert(*stores_it);
    }*/
    errs() << "Compressed BB (end): " << bb << " ";
    ls.debugPrint();
    //loads.insert(ls.loads.begin(), ls.loads.end());
    //stores.insert(ls.stores.begin(), ls.stores.end());
}

void CanTM::compressFunction(Function *f) {
    for (auto arg_iter=f->arg_begin(), arg_iter_end = f->arg_end(); arg_iter != arg_iter_end; ++arg_iter) {
        for (auto i_f = f->begin(), ie_f = f->end(); i_f != ie_f; i_f++) {
            BasicBlock *bb = i_f;
            LoadStore ls = bbMap[bb];
            // TODO: FIXME For now we'll assume all arguments are properly reserved
            ls.compressWithPreviousLoad(arg_iter);
            ls.compressWithPreviousStore(arg_iter);
            bbMap[bb] = ls;
        }
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
    ++CanTMCounter;
    errs() << "CanTM: ";
    stm_reserve = M.begin();
    errs().write_escaped(M.getModuleIdentifier()) << '\n';
    for (auto i = M.begin(), ie = M.end(); i != ie; ++i) {
        Function* f = i;
        /*
           errs() << "=========================\n";
           errs() << "Func: ";
           errs().write_escaped(f->getName()) << '\n';
           errs() << "=========================\n";
           errs() << "onlyReadsMemory: " << f->onlyReadsMemory() << '\n';
           */
        if (f->getName().str().find("tx") != std::string::npos) {
            fQueue.push(f);
            fAdded.insert(f);
            tx = f;
            break;
        }
    }

    while (!fQueue.empty()) {
        Function* f = fQueue.front();
        fQueue.pop();


        errs() << "=========================\n";
        errs() << "Processing Func: ";
        errs().write_escaped(f->getName()) << '\n';
        errs() << "=========================\n";

        for (auto i_f = f->begin(), ie_f = f->end(); i_f != ie_f; i_f++) {
            BasicBlock *bb = i_f;
            analyizeBB(bb);
        }
        for (Value::use_iterator j = f->use_begin(), je = f->use_end(); j != je; ++j) {
            Value *v = *j;
            errs() << "Value: ";
            errs().write_escaped(v->getName()) << '\n';
        }
    }

    compressFunction(tx);

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

        CallInst::Create(stm_reserve, args, "", InsertPos);
    }

    errs() << "==========\n";
    errs() << "Statistics\n";
    errs() << "==========\n";
    errs() << "Num Loads: " << num_loads << "\n";
    errs() << "Num Loads from function calls: " << num_loads_from_function_call << "\n";
    errs() << "Num Loads skipped: " << num_loads_skipped << "\n";
    errs() << "          skipped from previous store: " << num_loads_skipped_from_previous_store << "\n";
    errs() << "Num Loads unprocessed: " << num_loads_unprocessed << "\n";
    errs() << "Num Loads compressed: " << num_loads_compressed << "\n";
    errs() << "          compressed from previous store: " << num_loads_compressed_from_previous_store << "\n";
    errs() << "Num Stores: " << num_stores << "\n";
    errs() << "Num Stores skipped: " << num_stores_skipped << "\n";
    errs() << "Num Stores unprocessed: " << num_stores_unprocessed << "\n";
    errs() << "Num Stores compressed: " << num_stores_compressed << "\n";

    return true;
}
