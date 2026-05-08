{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Th12TreeEqBaseLN -- baseLN_imp slot of ruleIndBT2 for Th12 TreeEq.
--
-- Phase 3 of the schematic Theorem 12 for TreeEq programme.  See
-- BRA/NEXT-SESSION-TREEEQ-CONT.md.
--
-- Provides:
--   * P_Th12_TreeEq    -- the universal Theorem 12 statement (var 0 = x,
--                         var 1 = v).
--   * baseLN_imp v3 v4 -- the LN-base argument to ruleIndBT2: at x = O,
--                         v in {var v3, var v4, Pair v3 v4}.  No IHs
--                         used (axTreeEqLN is direct).
--
-- Builds on BRA2.Thm12.Parts.TreeEq.ConstructionBase (instantiated with
-- our concrete D_TreeEq_NN_fun) for D_TreeEq, D_TreeEq_closed, and the
-- pointwise correctness D_correct2_TreeEq_LN.
--
-- No postulates, no holes.

module BRA2.Th12TreeEqBaseLN where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Deriv
open import BRA2.Cor
open import BRA2.Th12TreeEqNNFun using (D_TreeEq_NN_fun ; D_TreeEq_NN_closed)
open import BRA2.Thm.ThmT using (thmT ; thClosed)

import BRA2.Thm12.Parts.TreeEq
module CB = BRA2.Thm12.Parts.TreeEq.ConstructionBase D_TreeEq_NN_fun D_TreeEq_NN_closed
open CB using (D_TreeEq ; D_TreeEq_closed ; D_correct2_TreeEq_LN)
open BRA2.Thm12.Parts.TreeEq using (codeFTeq2_TreeEq)

------------------------------------------------------------------------
-- Universal Theorem 12 statement for Df_F2_TreeEq.

P_Th12_TreeEq : Formula
P_Th12_TreeEq =
  atomic (eqn (ap1 thmT (ap2 D_TreeEq (var zero) (var (suc zero))))
              (codeFTeq2_TreeEq (var zero) (var (suc zero))))

------------------------------------------------------------------------
-- Concrete fresh-variable indices for ruleIndBT2 inner LN pair.
v3Nat : Nat
v3Nat = suc (suc (suc (suc zero)))

v4Nat : Nat
v4Nat = suc (suc (suc (suc (suc zero))))

------------------------------------------------------------------------
-- baseLN_imp: at x=O, v in {var v3Nat, var v4Nat, Pair v3Nat v4Nat}.
--
-- The LN axiom is a direct dispatch (no IHs needed).  We use
-- D_correct2_TreeEq_LN (var v3Nat) (var v4Nat) and lift to the
-- implication form via two mp/axK weakenings.  The two antecedent
-- IH slots are vacuous.

baseLN_imp :
  Deriv ((substF (suc zero) (var v3Nat) (substF zero O P_Th12_TreeEq)) imp
         ((substF (suc zero) (var v4Nat) (substF zero O P_Th12_TreeEq)) imp
          (substF (suc zero) (ap2 Pair (var v3Nat) (var v4Nat))
                             (substF zero O P_Th12_TreeEq))))
baseLN_imp =
  let
    pairT : Term
    pairT = ap2 Pair (var v3Nat) (var v4Nat)

    -- Concrete pointwise: D_correct2_TreeEq_LN at (var v3Nat, var v4Nat).
    concl_concrete : Deriv (atomic (eqn (ap1 thmT (ap2 D_TreeEq O pairT))
                                         (codeFTeq2_TreeEq O pairT)))
    concl_concrete = D_correct2_TreeEq_LN (var v3Nat) (var v4Nat)

    -- Align to substF form: substF (suc zero) pairT (substF zero O P_Th12_TreeEq).
    -- Agda's normalization on substF distributes through atomic/eqn/ap*; the
    -- D_TreeEq and thmT positions need explicit alignment via thClosed and
    -- D_TreeEq_closed (which both reduce to refl for our concrete data, but
    -- defensively we use eqSubst for clarity).

    concl_aligned :
      Deriv (substF (suc zero) pairT (substF zero O P_Th12_TreeEq))
    concl_aligned =
      eqSubst (\ DT -> Deriv (atomic (eqn
                (ap1 (substF1 (suc zero) pairT (substF1 zero O thmT))
                     (ap2 DT O pairT))
                (codeFTeq2_TreeEq O pairT))))
              (eqSym
                 (eqTrans
                    (eqCong (substF2 (suc zero) pairT) (D_TreeEq_closed zero O))
                    (D_TreeEq_closed (suc zero) pairT)))
              (eqSubst (\ fT -> Deriv (atomic (eqn
                          (ap1 fT (ap2 D_TreeEq O pairT))
                          (codeFTeq2_TreeEq O pairT))))
                       (eqSym
                          (eqTrans
                             (eqCong (substF1 (suc zero) pairT) (thClosed zero O))
                             (thClosed (suc zero) pairT)))
                       concl_concrete)

    Concl : Formula
    Concl = substF (suc zero) pairT (substF zero O P_Th12_TreeEq)

    A1 : Formula
    A1 = substF (suc zero) (var v3Nat) (substF zero O P_Th12_TreeEq)

    A2 : Formula
    A2 = substF (suc zero) (var v4Nat) (substF zero O P_Th12_TreeEq)

    -- Weaken concl by A2 then A1 (vacuous IH antecedents).
    step1 : Deriv (A2 imp Concl)
    step1 = mp (axK Concl A2) concl_aligned

    step2 : Deriv (A1 imp (A2 imp Concl))
    step2 = mp (axK (A2 imp Concl) A1) step1

  in step2
