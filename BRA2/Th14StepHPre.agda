{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Th14StepHPre
--
-- Phase C step H of the Theorem 14 closure (NEXT-SESSION-PHASE-C-CONTINUE-V2.md (C3)):
-- two sb-applications on the closed ex-falso numeral  t'_term ,
-- producing  thmT (h_part_skel x) = (2-deep subT chain on
-- reify (codeFormula t'_formula))  closed (no hypothesis on x).
--
-- After the 2 sb-steps, two outer mp-dispatches with r12_th(x) and
-- r12_sub(i,i) (h_part_thxLayer / h_part) produce the encoded
-- "(th(cor x) = sub(i,i)) imp ((not th(cor x) = sub(i,i)) imp bot)" .
--
-- This file delivers the 2-sb-step prefix only:
--
--   h_part_pre : (x : Term) ->
--     Deriv (atomic (eqn
--       (ap1 thmT (ap1 h_part_skel x))
--       (ap2 subT (ap2 Pair varCode1T sub_ii_subst)
--             (ap2 subT (ap2 Pair varCode0T (ap1 cor x))
--                        (reify (codeFormula t'_formula))))))
--
-- Closed (no hypothesis), via two thmTSubLemma applications threaded
-- through cong1 thmT bridges of  h_part_inner1 / h_part_skel 's Comp2
-- Pair structure.  The hypothesis  PrAtX x  enters only at the outer
-- mp-dispatch layer (Phase C continuation).
--
-- ASCII only.  No postulates, no holes.

module BRA2.Th14StepHPre where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Deriv
open import BRA2.Cor      using (cor)
open import BRA2.Sub      using (sub)
open import BRA2.SubT     using (subT)

open import BRA2.Thm.ThmT using (thmT)
open import BRA2.Thm.TagCodes using (tagCode_ruleInst)

open import BRA2.Thm14SubLemma using
  (thmTSubLemma ; subTOfCodeFormulaImp_isPair)
open import BRA2.SoundRuleInstVProof using (codeFormulaPairShape)

open import BRA2.Thm12 using (Thm12_F1_Result ; Thm12_F2_Result)

open import BRA2.Thm14Constr5Final using (module Th14Constr5Final)

open import BRA2.Thm14Numerals using
  ( t'_term ; t'_formula ; t'_witness ; eq01 )
open import BRA2.GoedelII using (bot ; i)

import BRA2.Th14HUnfolds

----------------------------------------------------------------------
-- Convenience.

private
  varCode0T : Term
  varCode0T = reify (code (var zero))

  varCode1T : Term
  varCode1T = reify (code (var (suc zero)))

----------------------------------------------------------------------
-- The Th14StepHPre module proper, parametric in r12_th, r12_sub.

module Th14StepHPre
  (r12_th  : Thm12_F1_Result thmT)
  (r12_sub : Thm12_F2_Result sub)
  where

  open Th14Constr5Final r12_th r12_sub
    using ( h_part_inner1 ; h_part_skel ; sub_ii_subst ; encoded_sub_ii ; encoded_th_x )

  open BRA2.Th14HUnfolds.Th14HUnfolds r12_th r12_sub
    using ( h_part_inner1_unfold ; h_part_skel_unfold ; encoded_th_x_at )

  --------------------------------------------------------------------
  -- The 2-sb-step prefix.
  --
  -- After Approach A (2026-05-02): substituents are encoded mixed-form
  -- Pairs.  Chronologically subT (vc1, encoded_sub_ii) first on closed
  -- codeFormula t'_formula, then subT (vc0, encoded_th_x_at x) LAST.

  h_part_pre : (x : Term) ->
    Deriv (atomic (eqn
      (ap1 thmT (ap1 h_part_skel x))
      (ap2 subT (ap2 Pair varCode0T (encoded_th_x_at x))
            (ap2 subT (ap2 Pair varCode1T encoded_sub_ii)
                       (reify (codeFormula t'_formula))))))
  h_part_pre x =
    let
        ----------------------------------------------------------------
        -- Layer 0 (innermost): codeP = reify(codeFormula t'_formula).
        -- Pair-shape via codeFormulaPairShape t'_formula.

        layer0_shape = codeFormulaPairShape t'_formula
        layer0_fp : Term
        layer0_fp = fst layer0_shape
        layer0_sp : Term
        layer0_sp = fst (snd layer0_shape)
        layer0_dh : Deriv (atomic (eqn (reify (codeFormula t'_formula))
                                        (ap2 Pair layer0_fp layer0_sp)))
        layer0_dh = snd (snd layer0_shape)

        layer0_dispatch :
          Deriv (atomic (eqn
            (ap1 thmT (ap2 Pair tagCode_ruleInst
                        (ap2 Pair (ap2 Pair varCode1T encoded_sub_ii)
                                  (reify t'_term))))
            (ap2 subT (ap2 Pair varCode1T encoded_sub_ii)
                       (reify (codeFormula t'_formula)))))
        layer0_dispatch = thmTSubLemma (suc zero) encoded_sub_ii (reify t'_term)
                            (reify (codeFormula t'_formula))
                            layer0_fp layer0_sp t'_witness layer0_dh

        layer0_bridge : Deriv (atomic (eqn (ap1 thmT (ap1 h_part_inner1 x))
                                            (ap1 thmT (ap2 Pair tagCode_ruleInst
                                              (ap2 Pair (ap2 Pair varCode1T encoded_sub_ii)
                                                        (reify t'_term))))))
        layer0_bridge = cong1 thmT (h_part_inner1_unfold x)

        layer0 :
          Deriv (atomic (eqn (ap1 thmT (ap1 h_part_inner1 x))
            (ap2 subT (ap2 Pair varCode1T encoded_sub_ii)
                       (reify (codeFormula t'_formula)))))
        layer0 = ruleTrans layer0_bridge layer0_dispatch

        ----------------------------------------------------------------
        -- Layer 1 (outermost): codeP1 = subT-form on reify(codeFormula
        -- t'_formula).  Pair-shape via subTOfCodeFormulaImp_isPair
        -- (t'_formula = eq01 imp ((not eq01) imp bot) is imp).

        codeP1 : Term
        codeP1 = ap2 subT (ap2 Pair varCode1T encoded_sub_ii)
                          (reify (codeFormula t'_formula))

        layer1_shape = subTOfCodeFormulaImp_isPair (suc zero)
                         (code (ap2 sub i i)) (code_isValue (ap2 sub i i))
                         eq01 ((not eq01) imp bot)
        layer1_fp : Term
        layer1_fp = fst layer1_shape
        layer1_sp : Term
        layer1_sp = fst (snd layer1_shape)
        layer1_dh : Deriv (atomic (eqn codeP1 (ap2 Pair layer1_fp layer1_sp)))
        layer1_dh = snd (snd layer1_shape)

        layer1_dispatch :
          Deriv (atomic (eqn
            (ap1 thmT (ap2 Pair tagCode_ruleInst
                        (ap2 Pair (ap2 Pair varCode0T (encoded_th_x_at x))
                                  (ap1 h_part_inner1 x))))
            (ap2 subT (ap2 Pair varCode0T (encoded_th_x_at x)) codeP1)))
        layer1_dispatch = thmTSubLemma zero (encoded_th_x_at x)
                            (ap1 h_part_inner1 x) codeP1
                            layer1_fp layer1_sp layer0 layer1_dh

        layer1_bridge : Deriv (atomic (eqn (ap1 thmT (ap1 h_part_skel x))
                                            (ap1 thmT (ap2 Pair tagCode_ruleInst
                                              (ap2 Pair (ap2 Pair varCode0T (encoded_th_x_at x))
                                                        (ap1 h_part_inner1 x))))))
        layer1_bridge = cong1 thmT (h_part_skel_unfold x)

    in ruleTrans layer1_bridge layer1_dispatch
