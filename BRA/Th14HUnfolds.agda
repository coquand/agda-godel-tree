{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Th14HUnfolds
--
-- Pair-of-Comp2 unfold lemmas for the h_part tower in
-- BRA.Thm14Constr5Final .  Mirrors  Th14Step3 's f_part_inner2_unfold /
-- f_part_inner1_unfold / f_part_unfold  for the t' / h_part chain.
--
-- These deliver, parametric in x : Term :
--
--   h_part_inner1_unfold :
--     ap1 h_part_inner1 x
--       = ap2 Pair tagCode_ruleInst
--           (ap2 Pair (ap2 Pair varCode0T (cor x))
--                     (reify t'_term))
--
--   h_part_skel_unfold :
--     ap1 h_part_skel x
--       = ap2 Pair tagCode_ruleInst
--           (ap2 Pair (ap2 Pair varCode1T sub_ii_subst)
--                     (ap1 h_part_inner1 x))
--
--   h_part_thxLayer_unfold :
--     ap1 h_part_thxLayer x
--       = ap2 Pair tagCode_mp
--           (ap2 Pair (ap1 h_part_skel x) (ap1 D_thmT x))
--
--   h_part_unfold :
--     ap1 h_part x
--       = ap2 Pair tagCode_mp
--           (ap2 Pair (ap1 h_part_thxLayer x) (ap1 D_sub_at_ii x))
--
-- ASCII only.  No postulates, no holes.

module BRA.Th14HUnfolds where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor      using (cor)
open import BRA.Sub      using (sub)
open import BRA.StepReduce using (ktRed)
open import BRA.Thm.Tag  using (tagRuleInst ; tagMp)

open import BRA.Thm.ThmT using (thmT)
open import BRA.Thm.TagCodes using (tagCode_ruleInst ; tagCode_mp)

open import BRA.Thm12 using (Thm12_F1_Result ; Thm12_F2_Result)

open import BRA.Thm14Constr5Final using (module Th14Constr5Final)

open import BRA.GoedelII using (i ; G)
open import BRA.Thm14Numerals using (t'_term)

----------------------------------------------------------------------
-- Convenience.

private
  varCode0T : Term
  varCode0T = reify (code (var zero))

  varCode1T : Term
  varCode1T = reify (code (var (suc zero)))

----------------------------------------------------------------------
-- The Th14HUnfolds module proper.

module Th14HUnfolds
  (r12_th  : Thm12_F1_Result thmT)
  (r12_sub : Thm12_F2_Result sub)
  where

  open Th14Constr5Final r12_th r12_sub
    using ( h_part_inner1 ; h_part_skel ; h_part_thxLayer ; h_part
          ; D_thmT ; D_sub_at_ii ; sub_ii_subst ; encoded_sub_ii ; encoded_th_x )

  --------------------------------------------------------------------
  -- encoded_th_x_at and encoded_th_x_unfold (re-exported from Th14Step3
  -- pattern; inlined here to avoid a circular import).

  encoded_th_x_at : Term -> Term
  encoded_th_x_at x = ap2 Pair (reify tagAp1)
                              (ap2 Pair (reify (codeF1 thmT)) (ap1 cor x))

  encoded_th_x_unfold : (x : Term) ->
    Deriv (atomic (eqn (ap1 encoded_th_x x) (encoded_th_x_at x)))
  encoded_th_x_unfold x =
    let
        inner : Fun1
        inner = Comp2 Pair (KT (reify (codeF1 thmT))) cor

        inner_step : Deriv (atomic (eqn (ap1 inner x)
                                         (ap2 Pair (ap1 (KT (reify (codeF1 thmT))) x)
                                                   (ap1 cor x))))
        inner_step = axComp2 Pair (KT (reify (codeF1 thmT))) cor x

        kt_codef1 : Deriv (atomic (eqn (ap1 (KT (reify (codeF1 thmT))) x)
                                        (reify (codeF1 thmT))))
        kt_codef1 = ktRed (codeF1 thmT) x

        inner_simp : Deriv (atomic (eqn (ap1 inner x)
                                         (ap2 Pair (reify (codeF1 thmT)) (ap1 cor x))))
        inner_simp = ruleTrans inner_step (congL Pair (ap1 cor x) kt_codef1)

        outer_step : Deriv (atomic (eqn (ap1 encoded_th_x x)
                                         (ap2 Pair (ap1 (KT (reify tagAp1)) x)
                                                   (ap1 inner x))))
        outer_step = axComp2 Pair (KT (reify tagAp1)) inner x

        kt_tagap1 : Deriv (atomic (eqn (ap1 (KT (reify tagAp1)) x) (reify tagAp1)))
        kt_tagap1 = ktRed tagAp1 x

        outer_simp1 : Deriv (atomic (eqn (ap1 encoded_th_x x)
                                          (ap2 Pair (reify tagAp1) (ap1 inner x))))
        outer_simp1 = ruleTrans outer_step (congL Pair (ap1 inner x) kt_tagap1)

    in ruleTrans outer_simp1 (congR Pair (reify tagAp1) inner_simp)

  --------------------------------------------------------------------
  -- h_part_inner1_unfold .
  --
  -- After Approach A (2026-05-02): innermost sb substituent at var 1
  -- is encoded_sub_ii (= reify (code (sub i i))) instead of sub_ii_subst.

  h_part_inner1_unfold : (x : Term) ->
    Deriv (atomic (eqn (ap1 h_part_inner1 x)
                       (ap2 Pair tagCode_ruleInst
                          (ap2 Pair (ap2 Pair varCode1T encoded_sub_ii)
                                    (reify t'_term)))))
  h_part_inner1_unfold x =
    let
        argsInner : Fun1
        argsInner = Comp2 Pair (KT varCode1T) (KT encoded_sub_ii)

        argsInner_step : Deriv (atomic (eqn (ap1 argsInner x)
                                             (ap2 Pair (ap1 (KT varCode1T) x)
                                                       (ap1 (KT encoded_sub_ii) x))))
        argsInner_step = axComp2 Pair (KT varCode1T) (KT encoded_sub_ii) x

        kt_v1 : Deriv (atomic (eqn (ap1 (KT varCode1T) x) varCode1T))
        kt_v1 = ktRed (code (var (suc zero))) x

        kt_sub : Deriv (atomic (eqn (ap1 (KT encoded_sub_ii) x) encoded_sub_ii))
        kt_sub = ktRed (code (ap2 sub i i)) x

        argsInner_simp1 : Deriv (atomic (eqn (ap1 argsInner x)
                                              (ap2 Pair (ap1 (KT varCode1T) x)
                                                        encoded_sub_ii)))
        argsInner_simp1 = ruleTrans argsInner_step
                            (congR Pair (ap1 (KT varCode1T) x) kt_sub)

        argsInner_simp : Deriv (atomic (eqn (ap1 argsInner x)
                                             (ap2 Pair varCode1T encoded_sub_ii)))
        argsInner_simp = ruleTrans argsInner_simp1 (congL Pair encoded_sub_ii kt_v1)

        mid : Fun1
        mid = Comp2 Pair argsInner (KT (reify t'_term))

        mid_step : Deriv (atomic (eqn (ap1 mid x)
                                       (ap2 Pair (ap1 argsInner x)
                                                 (ap1 (KT (reify t'_term)) x))))
        mid_step = axComp2 Pair argsInner (KT (reify t'_term)) x

        kt_t : Deriv (atomic (eqn (ap1 (KT (reify t'_term)) x) (reify t'_term)))
        kt_t = ktRed t'_term x

        mid_simp1 : Deriv (atomic (eqn (ap1 mid x)
                                        (ap2 Pair (ap1 argsInner x)
                                                  (reify t'_term))))
        mid_simp1 = ruleTrans mid_step (congR Pair (ap1 argsInner x) kt_t)

        mid_simp : Deriv (atomic (eqn (ap1 mid x)
                                       (ap2 Pair (ap2 Pair varCode1T encoded_sub_ii)
                                                 (reify t'_term))))
        mid_simp = ruleTrans mid_simp1 (congL Pair (reify t'_term) argsInner_simp)

        outer_step : Deriv (atomic (eqn (ap1 h_part_inner1 x)
                                         (ap2 Pair (ap1 (KT tagCode_ruleInst) x)
                                                   (ap1 mid x))))
        outer_step = axComp2 Pair (KT tagCode_ruleInst) mid x

        kt_tag : Deriv (atomic (eqn (ap1 (KT tagCode_ruleInst) x) tagCode_ruleInst))
        kt_tag = ktRed (natCode tagRuleInst) x

        outer_simp1 : Deriv (atomic (eqn (ap1 h_part_inner1 x)
                                          (ap2 Pair tagCode_ruleInst (ap1 mid x))))
        outer_simp1 = ruleTrans outer_step (congL Pair (ap1 mid x) kt_tag)
    in
        ruleTrans outer_simp1 (congR Pair tagCode_ruleInst mid_simp)

  --------------------------------------------------------------------
  -- h_part_skel_unfold .

  h_part_skel_unfold : (x : Term) ->
    Deriv (atomic (eqn (ap1 h_part_skel x)
                       (ap2 Pair tagCode_ruleInst
                          (ap2 Pair (ap2 Pair varCode0T (encoded_th_x_at x))
                                    (ap1 h_part_inner1 x)))))
  h_part_skel_unfold x =
    let
        argsInner : Fun1
        argsInner = Comp2 Pair (KT varCode0T) encoded_th_x

        argsInner_step : Deriv (atomic (eqn (ap1 argsInner x)
                                             (ap2 Pair (ap1 (KT varCode0T) x)
                                                       (ap1 encoded_th_x x))))
        argsInner_step = axComp2 Pair (KT varCode0T) encoded_th_x x

        kt_v0 : Deriv (atomic (eqn (ap1 (KT varCode0T) x) varCode0T))
        kt_v0 = ktRed (code (var zero)) x

        et_unfold : Deriv (atomic (eqn (ap1 encoded_th_x x) (encoded_th_x_at x)))
        et_unfold = encoded_th_x_unfold x

        argsInner_simp1 : Deriv (atomic (eqn (ap1 argsInner x)
                                              (ap2 Pair (ap1 (KT varCode0T) x)
                                                        (encoded_th_x_at x))))
        argsInner_simp1 = ruleTrans argsInner_step
                            (congR Pair (ap1 (KT varCode0T) x) et_unfold)

        argsInner_simp : Deriv (atomic (eqn (ap1 argsInner x)
                                             (ap2 Pair varCode0T (encoded_th_x_at x))))
        argsInner_simp =
          ruleTrans argsInner_simp1 (congL Pair (encoded_th_x_at x) kt_v0)

        mid : Fun1
        mid = Comp2 Pair argsInner h_part_inner1

        mid_step : Deriv (atomic (eqn (ap1 mid x)
                                       (ap2 Pair (ap1 argsInner x)
                                                 (ap1 h_part_inner1 x))))
        mid_step = axComp2 Pair argsInner h_part_inner1 x

        mid_simp : Deriv (atomic (eqn (ap1 mid x)
                                       (ap2 Pair (ap2 Pair varCode0T (encoded_th_x_at x))
                                                 (ap1 h_part_inner1 x))))
        mid_simp = ruleTrans mid_step
                     (congL Pair (ap1 h_part_inner1 x) argsInner_simp)

        outer_step : Deriv (atomic (eqn (ap1 h_part_skel x)
                                         (ap2 Pair (ap1 (KT tagCode_ruleInst) x)
                                                   (ap1 mid x))))
        outer_step = axComp2 Pair (KT tagCode_ruleInst) mid x

        kt_tag : Deriv (atomic (eqn (ap1 (KT tagCode_ruleInst) x) tagCode_ruleInst))
        kt_tag = ktRed (natCode tagRuleInst) x

        outer_simp1 : Deriv (atomic (eqn (ap1 h_part_skel x)
                                          (ap2 Pair tagCode_ruleInst (ap1 mid x))))
        outer_simp1 = ruleTrans outer_step (congL Pair (ap1 mid x) kt_tag)
    in
        ruleTrans outer_simp1 (congR Pair tagCode_ruleInst mid_simp)

  --------------------------------------------------------------------
  -- h_part_thxLayer_unfold .

  h_part_thxLayer_unfold : (x : Term) ->
    Deriv (atomic (eqn (ap1 h_part_thxLayer x)
                       (ap2 Pair tagCode_mp
                          (ap2 Pair (ap1 h_part_skel x) (ap1 D_thmT x)))))
  h_part_thxLayer_unfold x =
    let
        mid : Fun1
        mid = Comp2 Pair h_part_skel D_thmT

        mid_step : Deriv (atomic (eqn (ap1 mid x)
                                       (ap2 Pair (ap1 h_part_skel x)
                                                 (ap1 D_thmT x))))
        mid_step = axComp2 Pair h_part_skel D_thmT x

        outer_step : Deriv (atomic (eqn (ap1 h_part_thxLayer x)
                                         (ap2 Pair (ap1 (KT tagCode_mp) x)
                                                   (ap1 mid x))))
        outer_step = axComp2 Pair (KT tagCode_mp) mid x

        kt_tag : Deriv (atomic (eqn (ap1 (KT tagCode_mp) x) tagCode_mp))
        kt_tag = ktRed (natCode tagMp) x

        outer_simp1 : Deriv (atomic (eqn (ap1 h_part_thxLayer x)
                                          (ap2 Pair tagCode_mp (ap1 mid x))))
        outer_simp1 = ruleTrans outer_step (congL Pair (ap1 mid x) kt_tag)
    in
        ruleTrans outer_simp1 (congR Pair tagCode_mp mid_step)

  --------------------------------------------------------------------
  -- h_part_unfold .

  h_part_unfold : (x : Term) ->
    Deriv (atomic (eqn (ap1 h_part x)
                       (ap2 Pair tagCode_mp
                          (ap2 Pair (ap1 h_part_thxLayer x) (ap1 D_sub_at_ii x)))))
  h_part_unfold x =
    let
        mid : Fun1
        mid = Comp2 Pair h_part_thxLayer D_sub_at_ii

        mid_step : Deriv (atomic (eqn (ap1 mid x)
                                       (ap2 Pair (ap1 h_part_thxLayer x)
                                                 (ap1 D_sub_at_ii x))))
        mid_step = axComp2 Pair h_part_thxLayer D_sub_at_ii x

        outer_step : Deriv (atomic (eqn (ap1 h_part x)
                                         (ap2 Pair (ap1 (KT tagCode_mp) x)
                                                   (ap1 mid x))))
        outer_step = axComp2 Pair (KT tagCode_mp) mid x

        kt_tag : Deriv (atomic (eqn (ap1 (KT tagCode_mp) x) tagCode_mp))
        kt_tag = ktRed (natCode tagMp) x

        outer_simp1 : Deriv (atomic (eqn (ap1 h_part x)
                                          (ap2 Pair tagCode_mp (ap1 mid x))))
        outer_simp1 = ruleTrans outer_step (congL Pair (ap1 mid x) kt_tag)
    in
        ruleTrans outer_simp1 (congR Pair tagCode_mp mid_step)
