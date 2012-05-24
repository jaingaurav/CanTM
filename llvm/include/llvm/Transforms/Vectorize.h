//===-- Vectorize.h - Vectorization Transformations -------------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This header file defines prototypes for accessor functions that expose passes
// in the Vectorize transformations library.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_TRANSFORMS_VECTORIZE_H
#define LLVM_TRANSFORMS_VECTORIZE_H

namespace llvm {
class BasicBlock;
class BasicBlockPass;

//===----------------------------------------------------------------------===//
/// @brief Vectorize configuration.
struct VectorizeConfig {
  //===--------------------------------------------------------------------===//
  // Target architecture related parameters

  /// @brief The size of the native vector registers.
  unsigned VectorBits;

  /// @brief Vectorize integer values.
  bool VectorizeInts;

  /// @brief Vectorize floating-point values.
  bool VectorizeFloats;

  /// @brief Vectorize pointer values.
  bool VectorizePointers;

  /// @brief Vectorize casting (conversion) operations.
  bool VectorizeCasts;

  /// @brief Vectorize floating-point math intrinsics.
  bool VectorizeMath;

  /// @brief Vectorize the fused-multiply-add intrinsic.
  bool VectorizeFMA;

  /// @brief Vectorize select instructions.
  bool VectorizeSelect;

  /// @brief Vectorize getelementptr instructions.
  bool VectorizeGEP;

  /// @brief Vectorize loads and stores.
  bool VectorizeMemOps;

  /// @brief Only generate aligned loads and stores.
  bool AlignedOnly;

  //===--------------------------------------------------------------------===//
  // Misc parameters

  /// @brief The required chain depth for vectorization.
  unsigned ReqChainDepth;

  /// @brief The maximum search distance for instruction pairs.
  unsigned SearchLimit;

  /// @brief The maximum number of candidate pairs with which to use a full
  ///        cycle check.
  unsigned MaxCandPairsForCycleCheck;

  /// @brief Replicating one element to a pair breaks the chain.
  bool SplatBreaksChain;

  /// @brief The maximum number of pairable instructions per group.
  unsigned MaxInsts;

  /// @brief The maximum number of pairing iterations.
  unsigned MaxIter;

  /// @brief Don't boost the chain-depth contribution of loads and stores.
  bool NoMemOpBoost;

  /// @brief Use a fast instruction dependency analysis.
  bool FastDep;

  /// @brief Initialize the VectorizeConfig from command line options.
  VectorizeConfig();
};

//===----------------------------------------------------------------------===//
//
// BBVectorize - A basic-block vectorization pass.
//
BasicBlockPass *
createBBVectorizePass(const VectorizeConfig &C = VectorizeConfig());

//===----------------------------------------------------------------------===//
/// @brief Vectorize the BasicBlock.
///
/// @param BB The BasicBlock to be vectorized
/// @param P  The current running pass, should require AliasAnalysis and
///           ScalarEvolution. After the vectorization, AliasAnalysis,
///           ScalarEvolution and CFG are preserved.
///
/// @return True if the BB is changed, false otherwise.
///
bool vectorizeBasicBlock(Pass *P, BasicBlock &BB,
                         const VectorizeConfig &C = VectorizeConfig());

} // End llvm namespace

#endif
