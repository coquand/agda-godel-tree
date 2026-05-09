{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Th12TreeEqClose -- closes Theorem 12 for TreeEq.
--
-- Combines:
--   * basePP_concrete (BRA2.Th12TreeEqBasePP) -- pointwise NN proof.
--   * Bridge via D_TreeEq_reduce_NN from ConstructionBase (lifting
--     basePP_concrete from D_TreeEq_NN_fun to D_TreeEq).
--   * Two axK weakenings to absorb the vacuous cross-IH antecedents
--     of ruleIndBT2.
--   * Substitution-form alignment via eqSubst over thClosed +
--     D_TreeEq_closed.
--   * Th12TreeEqUniv.Th12_F2_TreeEq_param to discharge basePP_imp.
--
-- Output: Th12_F2_TreeEq : Deriv P_Th12_TreeEq.  No postulates, no holes.

module BRA2.Th12TreeEqClose where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.DerivThreshold
open import BRA2.Cor
open import BRA2.Thm.ThmT using (thmT ; thClosed)

open import BRA2.Th12TreeEqNNFun using (D_TreeEq_NN_fun ; D_TreeEq_NN_closed ; pairOO)

import BRA2.Thm12.Parts.TreeEq
module CB = BRA2.Thm12.Parts.TreeEq.ConstructionBase D_TreeEq_NN_fun D_TreeEq_NN_closed
open CB public using (D_TreeEq ; D_TreeEq_closed ; D_TreeEq_reduce_NN)
open BRA2.Thm12.Parts.TreeEq public using (codeFTeq2_TreeEq)

open import BRA2.Th12TreeEqBaseLN using (P_Th12_TreeEq ; v3Nat ; v4Nat)
open import BRA2.Th12TreeEqBaseNL using (v1Nat ; v2Nat)
open import BRA2.Th12TreeEqUniv using (BasePPType ; Th12_F2_TreeEq_param)
open import BRA2.Th12TreeEqBasePP using (Th12_F2_TreeEq_NN_pt)
open import BRA2.MaxVar
  using (pickFresh ; subst_pickFresh ; pickFresh_natEq_one' ; natEq_refl)

------------------------------------------------------------------------
-- Convenience aliases for the four BRA fresh-variable indices.
-- v1Nat=2, v2Nat=3, v3Nat=4, v4Nat=5.

private
  v1T : Term
  v1T = var v1Nat
  v2T : Term
  v2T = var v2Nat
  v3T : Term
  v3T = var v3Nat
  v4T : Term
  v4T = var v4Nat

------------------------------------------------------------------------
-- basePP_concrete at the four var indices: combines basePP_NN_pt with
-- the D_TreeEq_reduce_NN bridge.

private
  pairV12 : Term
  pairV12 = ap2 Pair v1T v2T

  pairV34 : Term
  pairV34 = ap2 Pair v3T v4T

basePP_concrete :
  Deriv (atomic (eqn (ap1 thmT (ap2 D_TreeEq pairV12 pairV34))
                     (codeFTeq2_TreeEq pairV12 pairV34)))
basePP_concrete =
  let
    -- Pointwise NN proof.
    nn_pt : Deriv (atomic (eqn (ap1 thmT (ap2 D_TreeEq_NN_fun pairV12 pairV34))
                                (codeFTeq2_TreeEq pairV12 pairV34)))
    nn_pt = Th12_F2_TreeEq_NN_pt v1T v2T v3T v4T

    -- Bridge: D_TreeEq dispatches at NN to D_TreeEq_NN_fun.
    s_reduce : Deriv (atomic (eqn (ap2 D_TreeEq pairV12 pairV34)
                                   (ap2 D_TreeEq_NN_fun pairV12 pairV34)))
    s_reduce = D_TreeEq_reduce_NN v1T v2T v3T v4T

    s_thmT_reduce : Deriv (atomic (eqn (ap1 thmT (ap2 D_TreeEq pairV12 pairV34))
                                        (ap1 thmT (ap2 D_TreeEq_NN_fun pairV12 pairV34))))
    s_thmT_reduce = cong1 thmT s_reduce

  in ruleTrans s_thmT_reduce nn_pt

------------------------------------------------------------------------
-- basePP_imp: align basePP_concrete to the substF form and absorb the
-- two vacuous IH antecedents.

basePP_aligned : Deriv (substF (suc zero) pairV34 (substF zero pairV12 P_Th12_TreeEq))
basePP_aligned =
  -- Goal type after substF reduction:
  --   atomic (eqn (ap1 (substF1 (suc zero) pairV34 (substF1 zero pairV12 thmT))
  --                    (ap2 (substF2 (suc zero) pairV34
  --                          (substF2 zero pairV12 D_TreeEq))
  --                         pairV12 pairV34))
  --               (codeFTeq2_TreeEq pairV12 pairV34))
  -- Use thClosed and D_TreeEq_closed twice to align.
  eqSubst (\ DT -> Deriv (atomic (eqn
            (ap1 (substF1 (suc zero) pairV34 (substF1 zero pairV12 thmT))
                 (ap2 DT pairV12 pairV34))
            (codeFTeq2_TreeEq pairV12 pairV34))))
          (eqSym
             (eqTrans
                (eqCong (substF2 (suc zero) pairV34) (D_TreeEq_closed zero pairV12))
                (D_TreeEq_closed (suc zero) pairV34)))
          (eqSubst (\ fT -> Deriv (atomic (eqn
                      (ap1 fT (ap2 D_TreeEq pairV12 pairV34))
                      (codeFTeq2_TreeEq pairV12 pairV34))))
                   (eqSym
                      (eqTrans
                         (eqCong (substF1 (suc zero) pairV34) (thClosed zero pairV12))
                         (thClosed (suc zero) pairV34)))
                   basePP_concrete)

basePP_imp : BasePPType
basePP_imp =
  let
    Concl : Formula
    Concl = substF (suc zero) pairV34 (substF zero pairV12 P_Th12_TreeEq)

    A1 : Formula
    A1 = substF (suc zero) v3T (substF zero v1T P_Th12_TreeEq)

    A2 : Formula
    A2 = substF (suc zero) v4T (substF zero v2T P_Th12_TreeEq)

    step1 : Deriv (A2 imp Concl)
    step1 = mp (axK Concl A2) basePP_aligned

    step2 : Deriv (A1 imp (A2 imp Concl))
    step2 = mp (axK (A2 imp Concl) A1) step1

  in step2

------------------------------------------------------------------------
-- Th12_F2_TreeEq: top-level export.

Th12_F2_TreeEq : Deriv P_Th12_TreeEq
Th12_F2_TreeEq = Th12_F2_TreeEq_param basePP_imp

------------------------------------------------------------------------
-- Universal (x v : Term) -> Deriv ...  wrapper -- closure-free (mirrors
-- BRA2.Thm12.Parts.IfLf.D_correct2_IfLf).
--
-- Strategy: pickFresh v gives k >= 2 fresh in v.  Three ruleInst's:
--   (1) ruleInst zero (var k)   -- rename var 0 to fresh var k
--   (2) ruleInst (suc zero) v   -- substitute v in the v slot
--   (3) ruleInst k x            -- substitute x in the var-k slot
--
-- Step (3)'s recursion through v is harmless because v has no var k.

D_correct2_TreeEq : (x v : Term) ->
  Deriv (atomic (eqn (ap1 thmT (ap2 D_TreeEq x v)) (codeFTeq2_TreeEq x v)))
D_correct2_TreeEq x v =
  let k : Nat
      k = pickFresh v

      -- ===== Step 1: rename var 0 (= x slot) to var k. =====

      stage1 : Deriv (substF zero (var k) P_Th12_TreeEq)
      stage1 = ruleInst zero (var k) Th12_F2_TreeEq

      stage1_thmT :
        Deriv (atomic (eqn
          (ap1 thmT (ap2 (substF2 zero (var k) D_TreeEq) (var k) (var (suc zero))))
          (codeFTeq2_TreeEq (var k) (var (suc zero)))))
      stage1_thmT =
        eqSubst (\ tT -> Deriv (atomic (eqn
                  (ap1 tT (ap2 (substF2 zero (var k) D_TreeEq) (var k) (var (suc zero))))
                  (codeFTeq2_TreeEq (var k) (var (suc zero))))))
                (thClosed zero (var k))
                stage1

      stage1_clean :
        Deriv (atomic (eqn
          (ap1 thmT (ap2 D_TreeEq (var k) (var (suc zero))))
          (codeFTeq2_TreeEq (var k) (var (suc zero)))))
      stage1_clean =
        eqSubst (\ DT -> Deriv (atomic (eqn
                  (ap1 thmT (ap2 DT (var k) (var (suc zero))))
                  (codeFTeq2_TreeEq (var k) (var (suc zero))))))
                (D_TreeEq_closed zero (var k))
                stage1_thmT

      -- ===== Step 2: substitute v in the v slot. =====

      stage2 :
        Deriv (substF (suc zero) v (atomic (eqn
          (ap1 thmT (ap2 D_TreeEq (var k) (var (suc zero))))
          (codeFTeq2_TreeEq (var k) (var (suc zero))))))
      stage2 = ruleInst (suc zero) v stage1_clean

      stage2_thmT :
        Deriv (atomic (eqn
          (ap1 thmT (ap2 (substF2 (suc zero) v D_TreeEq) (subst (suc zero) v (var k)) v))
          (codeFTeq2_TreeEq (subst (suc zero) v (var k)) v)))
      stage2_thmT =
        eqSubst (\ tT -> Deriv (atomic (eqn
                  (ap1 tT (ap2 (substF2 (suc zero) v D_TreeEq) (subst (suc zero) v (var k)) v))
                  (codeFTeq2_TreeEq (subst (suc zero) v (var k)) v))))
                (thClosed (suc zero) v)
                stage2

      stage2_D :
        Deriv (atomic (eqn
          (ap1 thmT (ap2 D_TreeEq (subst (suc zero) v (var k)) v))
          (codeFTeq2_TreeEq (subst (suc zero) v (var k)) v)))
      stage2_D =
        eqSubst (\ DT -> Deriv (atomic (eqn
                  (ap1 thmT (ap2 DT (subst (suc zero) v (var k)) v))
                  (codeFTeq2_TreeEq (subst (suc zero) v (var k)) v))))
                (D_TreeEq_closed (suc zero) v)
                stage2_thmT

      -- subst (suc zero) v (var k) = var k  because k >= 2, k != 1.
      eq_kSlot1 : Eq (subst (suc zero) v (var k)) (var k)
      eq_kSlot1 =
        eqCong (\ b -> boolCase b v (var k)) (pickFresh_natEq_one' v)

      stage2_clean :
        Deriv (atomic (eqn
          (ap1 thmT (ap2 D_TreeEq (var k) v))
          (codeFTeq2_TreeEq (var k) v)))
      stage2_clean =
        eqSubst (\ Y -> Deriv (atomic (eqn
                  (ap1 thmT (ap2 D_TreeEq Y v))
                  (codeFTeq2_TreeEq Y v))))
                eq_kSlot1
                stage2_D

      -- ===== Step 3: substitute x in the var-k slot. =====

      stage3 :
        Deriv (substF k x (atomic (eqn
          (ap1 thmT (ap2 D_TreeEq (var k) v))
          (codeFTeq2_TreeEq (var k) v))))
      stage3 = ruleInst k x stage2_clean

      stage3_thmT :
        Deriv (atomic (eqn
          (ap1 thmT (ap2 (substF2 k x D_TreeEq) (subst k x (var k)) (subst k x v)))
          (codeFTeq2_TreeEq (subst k x (var k)) (subst k x v))))
      stage3_thmT =
        eqSubst (\ tT -> Deriv (atomic (eqn
                  (ap1 tT (ap2 (substF2 k x D_TreeEq) (subst k x (var k)) (subst k x v)))
                  (codeFTeq2_TreeEq (subst k x (var k)) (subst k x v)))))
                (thClosed k x)
                stage3

      stage3_D :
        Deriv (atomic (eqn
          (ap1 thmT (ap2 D_TreeEq (subst k x (var k)) (subst k x v)))
          (codeFTeq2_TreeEq (subst k x (var k)) (subst k x v))))
      stage3_D =
        eqSubst (\ DT -> Deriv (atomic (eqn
                  (ap1 thmT (ap2 DT (subst k x (var k)) (subst k x v)))
                  (codeFTeq2_TreeEq (subst k x (var k)) (subst k x v)))))
                (D_TreeEq_closed k x)
                stage3_thmT

      -- subst k x (var k) = x  because natEq k k = true.
      eq_kk_x : Eq (subst k x (var k)) x
      eq_kk_x =
        eqCong (\ b -> boolCase b x (var k)) (natEq_refl k)

      -- subst k x v = v  because k = pickFresh v is fresh in v.
      eq_kv_v : Eq (subst k x v) v
      eq_kv_v = subst_pickFresh x v

      stage3_x :
        Deriv (atomic (eqn
          (ap1 thmT (ap2 D_TreeEq x (subst k x v)))
          (codeFTeq2_TreeEq x (subst k x v))))
      stage3_x =
        eqSubst (\ Y -> Deriv (atomic (eqn
                  (ap1 thmT (ap2 D_TreeEq Y (subst k x v)))
                  (codeFTeq2_TreeEq Y (subst k x v)))))
                eq_kk_x
                stage3_D

      stage3_xv :
        Deriv (atomic (eqn
          (ap1 thmT (ap2 D_TreeEq x v))
          (codeFTeq2_TreeEq x v)))
      stage3_xv =
        eqSubst (\ V -> Deriv (atomic (eqn
                  (ap1 thmT (ap2 D_TreeEq x V))
                  (codeFTeq2_TreeEq x V))))
                eq_kv_v
                stage3_x
  in stage3_xv
