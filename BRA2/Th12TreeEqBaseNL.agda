{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Th12TreeEqBaseNL -- baseNL_imp slot of ruleIndBT2 for Th12 TreeEq.
--
-- Mirror of BRA2.Th12TreeEqBaseLN: at x in {var v1Nat, var v2Nat,
-- Pair v1Nat v2Nat}, v = O.  No IHs needed (axTreeEqNL is direct).
--
-- See BRA/NEXT-SESSION-TREEEQ-CONT.md.
--
-- Concrete fresh-variable indices for ruleIndBT2 (matching the ones used
-- in Th12TreeEqUniv).  Using v1Nat=2, v2Nat=3 (so subst (suc zero) O is
-- a no-op on var v1Nat / var v2Nat by definitional reduction of natEq).

module BRA2.Th12TreeEqBaseNL where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.DerivThreshold
open import BRA2.Cor
open import BRA2.Th12TreeEqNNFun using (D_TreeEq_NN_fun ; D_TreeEq_NN_closed)
open import BRA2.Thm.ThmT using (thmT ; thClosed)

import BRA2.Thm12.Parts.TreeEq
module CB = BRA2.Thm12.Parts.TreeEq.ConstructionBase D_TreeEq_NN_fun D_TreeEq_NN_closed
open CB using (D_TreeEq ; D_TreeEq_closed ; D_correct2_TreeEq_NL)
open BRA2.Thm12.Parts.TreeEq using (codeFTeq2_TreeEq)

open import BRA2.Th12TreeEqBaseLN using (P_Th12_TreeEq)

------------------------------------------------------------------------
-- Concrete fresh variables for ruleIndBT2 outer NL pair.
v1Nat : Nat
v1Nat = suc (suc zero)

v2Nat : Nat
v2Nat = suc (suc (suc zero))

------------------------------------------------------------------------
-- baseNL_imp: at x in {var v1Nat, var v2Nat, Pair v1Nat v2Nat}, v=O.

baseNL_imp :
  Deriv ((substF (suc zero) O (substF zero (var v1Nat) P_Th12_TreeEq)) imp
         ((substF (suc zero) O (substF zero (var v2Nat) P_Th12_TreeEq)) imp
          (substF (suc zero) O
                  (substF zero (ap2 Pair (var v1Nat) (var v2Nat)) P_Th12_TreeEq))))
baseNL_imp =
  let
    pairT : Term
    pairT = ap2 Pair (var v1Nat) (var v2Nat)

    -- Concrete pointwise: D_correct2_TreeEq_NL at (var v1Nat, var v2Nat).
    concl_concrete : Deriv (atomic (eqn (ap1 thmT (ap2 D_TreeEq pairT O))
                                         (codeFTeq2_TreeEq pairT O)))
    concl_concrete = D_correct2_TreeEq_NL (var v1Nat) (var v2Nat)

    -- Align to substF form: substF (suc zero) O (substF zero pairT P_Th12_TreeEq).
    -- Since v1Nat = 2, v2Nat = 3, subst (suc zero) O leaves var v1Nat / var v2Nat
    -- untouched definitionally.

    concl_aligned :
      Deriv (substF (suc zero) O (substF zero pairT P_Th12_TreeEq))
    concl_aligned =
      eqSubst (\ DT -> Deriv (atomic (eqn
                (ap1 (substF1 (suc zero) O (substF1 zero pairT thmT))
                     (ap2 DT pairT O))
                (codeFTeq2_TreeEq pairT O))))
              (eqSym
                 (eqTrans
                    (eqCong (substF2 (suc zero) O) (D_TreeEq_closed zero pairT))
                    (D_TreeEq_closed (suc zero) O)))
              (eqSubst (\ fT -> Deriv (atomic (eqn
                          (ap1 fT (ap2 D_TreeEq pairT O))
                          (codeFTeq2_TreeEq pairT O))))
                       (eqSym
                          (eqTrans
                             (eqCong (substF1 (suc zero) O) (thClosed zero pairT))
                             (thClosed (suc zero) O)))
                       concl_concrete)

    Concl : Formula
    Concl = substF (suc zero) O (substF zero pairT P_Th12_TreeEq)

    A1 : Formula
    A1 = substF (suc zero) O (substF zero (var v1Nat) P_Th12_TreeEq)

    A2 : Formula
    A2 = substF (suc zero) O (substF zero (var v2Nat) P_Th12_TreeEq)

    step1 : Deriv (A2 imp Concl)
    step1 = mp (axK Concl A2) concl_aligned

    step2 : Deriv (A1 imp (A2 imp Concl))
    step2 = mp (axK (A2 imp Concl) A1) step1

  in step2
