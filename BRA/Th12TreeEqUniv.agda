{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Th12TreeEqUniv -- assembles ruleIndBT2 for Theorem 12 TreeEq.
--
-- Phase 5 of the Theorem-12-completion programme for TreeEq.  See
-- BRA/NEXT-SESSION-TREEEQ-CONT.md.
--
-- Universal Theorem 12 for TreeEq via the new diagonal 2D induction
-- primitive ruleIndBT2.  Parametric on the basePP_imp argument (the
-- heavy lift of the (Pair, Pair) case) so this assembly file can land
-- ahead of Phase 4.  The module body delivers Th12_F2_TreeEq : Deriv
-- P_Th12_TreeEq at concrete fresh-variable indices (v1=2, v2=3, v3=4,
-- v4=5).
--
-- No postulates, no holes.

module BRA.Th12TreeEqUniv where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor
open import BRA.Th12TreeEqNNFun using (D_TreeEq_NN_fun ; D_TreeEq_NN_closed)
open import BRA.Thm.ThmT using (thmT ; thClosed)

import BRA.Thm12.Parts.TreeEq
module CB = BRA.Thm12.Parts.TreeEq.ConstructionBase D_TreeEq_NN_fun D_TreeEq_NN_closed
open CB using (D_TreeEq ; D_TreeEq_closed ; D_correct2_TreeEq_LL)
open BRA.Thm12.Parts.TreeEq using (codeFTeq2_TreeEq)

open import BRA.Th12TreeEqBaseLN using (P_Th12_TreeEq ; v3Nat ; v4Nat ; baseLN_imp)
open import BRA.Th12TreeEqBaseNL using (v1Nat ; v2Nat ; baseNL_imp)

------------------------------------------------------------------------
-- baseLL_proof: aligned form of D_correct2_TreeEq_LL.

baseLL_proof : Deriv (substF (suc zero) O (substF zero O P_Th12_TreeEq))
baseLL_proof =
  eqSubst (\ DT -> Deriv (atomic (eqn
            (ap1 (substF1 (suc zero) O (substF1 zero O thmT))
                 (ap2 DT O O))
            (codeFTeq2_TreeEq O O))))
          (eqSym
             (eqTrans
                (eqCong (substF2 (suc zero) O) (D_TreeEq_closed zero O))
                (D_TreeEq_closed (suc zero) O)))
          (eqSubst (\ fT -> Deriv (atomic (eqn
                      (ap1 fT (ap2 D_TreeEq O O))
                      (codeFTeq2_TreeEq O O))))
                   (eqSym
                      (eqTrans
                         (eqCong (substF1 (suc zero) O) (thClosed zero O))
                         (thClosed (suc zero) O)))
                   D_correct2_TreeEq_LL)

------------------------------------------------------------------------
-- BasePP type: signature of the heavy-lift basePP_imp argument.

BasePPType : Set
BasePPType =
  Deriv ((substF (suc zero) (var v3Nat) (substF zero (var v1Nat) P_Th12_TreeEq)) imp
         ((substF (suc zero) (var v4Nat) (substF zero (var v2Nat) P_Th12_TreeEq)) imp
          (substF (suc zero) (ap2 Pair (var v3Nat) (var v4Nat))
                  (substF zero (ap2 Pair (var v1Nat) (var v2Nat)) P_Th12_TreeEq))))

------------------------------------------------------------------------
-- Th12_F2_TreeEq universal: parametric on basePP_imp.

Th12_F2_TreeEq_param : BasePPType -> Deriv P_Th12_TreeEq
Th12_F2_TreeEq_param basePP_imp =
  ruleIndBT2 P_Th12_TreeEq v1Nat v2Nat v3Nat v4Nat
             baseLL_proof
             baseLN_imp
             baseNL_imp
             basePP_imp
