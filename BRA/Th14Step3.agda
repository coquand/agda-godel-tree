{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Th14Step3
--
-- Phase C step 3 of the Theorem 14 closure (NEXT-SESSION-PHASE-C.md):
-- three sb-applications on the closed transitivity numeral  t_term ,
-- producing  thmT (f_part x) = (3-deep subT chain on reify (codeFormula
-- t_formula))  closed (no hypothesis on x).
--
-- After the 3 sb-steps, two mp-dispatches with r12_th(x) and r12_sub(i,i)
-- (DEFERRED to a future session — they require subT-canonicalization
-- bridges to the encoded "Pair tagImp (Pair pT qT)" shape that
-- thmTDispMp_param expects) would chain into the encoded
-- "th(cor x) = sub(i,i)" .
--
-- This file delivers the 3-sb-step prefix:
--
--   step3_pre : (x : Term) ->
--     Deriv (atomic (eqn
--       (ap1 thmT (ap1 f_part x))
--       (ap2 subT (ap2 Pair varCode2T i)
--             (ap2 subT (ap2 Pair varCode1T sub_ii_subst)
--                   (ap2 subT (ap2 Pair varCode0T (ap1 cor x))
--                              (reify (codeFormula t_formula)))))))
--
-- Closed (no hypothesis), via three thmTSubLemma applications threaded
-- through cong1 thmT bridges of  f_part_inner2 / f_part_inner1 / f_part
-- 's Comp2 Pair structure.  The hypothesis  PrAtX x  enters only at the
-- mp-dispatch layer (Phase C continuation).
--
-- ASCII only.  No postulates, no holes.

module BRA.Th14Step3 where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor      using (cor)
open import BRA.Sub      using (sub)
open import BRA.SubT     using (subT)
open import BRA.StepReduce using (ktRed)
open import BRA.Thm.Tag  using (tagRuleInst)

open import BRA.Thm.ThmT using
  ( thmT
  ; tagCode_ruleInst
  )

open import BRA.Thm14SubLemma using
  (thmTSubLemma ; subTOfCodeFormulaImp_isPair ; subToFormulaBridge)
open import BRA.SoundRuleInstVProof using (codeFormulaPairShape)

open import BRA.Thm12 using (Thm12_F1_Result ; Thm12_F2_Result)

open import BRA.Thm14Constr5Final using (module Th14Constr5Final)

open import BRA.Thm14Numerals using
  ( t_term ; t_formula ; t_witness ; eq01 ; eq02 ; eq12 )

open import BRA.GoedelII using (i ; cG ; G ; j)

----------------------------------------------------------------------
-- Convenience.

private
  varCode0T : Term
  varCode0T = reify (code (var zero))

  varCode1T : Term
  varCode1T = reify (code (var (suc zero)))

  varCode2T : Term
  varCode2T = reify (code (var (suc (suc zero))))

----------------------------------------------------------------------
-- Generic helper: given a Fun1 of the form
--   pairF tag (innerF) ,  i.e.  Comp2 Pair (KT tagT) innerF
-- evaluated at x, the result is  Pair tagT (ap1 innerF x) .

private
  pair_unfold_kt : (tagV : Tree) (innerF : Fun1) (x : Term) ->
    Deriv (atomic (eqn
      (ap1 (Comp2 Pair (KT (reify tagV)) innerF) x)
      (ap2 Pair (reify tagV) (ap1 innerF x))))
  pair_unfold_kt tagV innerF x =
    let
        s1 = axComp2 Pair (KT (reify tagV)) innerF x
        s2_kt = ktRed tagV x
    in ruleTrans s1 (congL Pair (ap1 innerF x) s2_kt)

----------------------------------------------------------------------
-- The Th14Step3 module proper, parametric in r12_th, r12_sub.

module Th14Step3
  (r12_th  : Thm12_F1_Result thmT)
  (r12_sub : Thm12_F2_Result sub)
  where

  open Th14Constr5Final r12_th r12_sub
    using ( f_part ; f_part_inner1 ; f_part_inner2
          ; sub_ii_subst ; encoded_sub_ii ; encoded_th_x )

  --------------------------------------------------------------------
  -- f_part_inner2_unfold : ap1 f_part_inner2 x = Pair tagCode_ruleInst
  --                           (Pair (Pair varCode2T sub_ii_subst)
  --                                 (reify t_term))
  --
  -- After Approach A (2026-05-02): innermost sb substituent at var 2
  -- is sub_ii_subst (= encoded "j" = num j) instead of i.

  f_part_inner2_unfold : (x : Term) ->
    Deriv (atomic (eqn (ap1 f_part_inner2 x)
                       (ap2 Pair tagCode_ruleInst
                          (ap2 Pair (ap2 Pair varCode2T sub_ii_subst)
                                    (reify t_term)))))
  f_part_inner2_unfold x =
    let
        argsInner : Fun1
        argsInner = Comp2 Pair (KT varCode2T) (KT sub_ii_subst)

        argsInner_step : Deriv (atomic (eqn (ap1 argsInner x)
                                             (ap2 Pair (ap1 (KT varCode2T) x)
                                                       (ap1 (KT sub_ii_subst) x))))
        argsInner_step = axComp2 Pair (KT varCode2T) (KT sub_ii_subst) x

        kt_v2 : Deriv (atomic (eqn (ap1 (KT varCode2T) x) varCode2T))
        kt_v2 = ktRed (code (var (suc (suc zero)))) x

        kt_sub : Deriv (atomic (eqn (ap1 (KT sub_ii_subst) x) sub_ii_subst))
        kt_sub = ktRed (code (reify (codeFormula G))) x

        argsInner_simp1 : Deriv (atomic (eqn (ap1 argsInner x)
                                              (ap2 Pair (ap1 (KT varCode2T) x) sub_ii_subst)))
        argsInner_simp1 = ruleTrans argsInner_step
                            (congR Pair (ap1 (KT varCode2T) x) kt_sub)

        argsInner_simp : Deriv (atomic (eqn (ap1 argsInner x)
                                             (ap2 Pair varCode2T sub_ii_subst)))
        argsInner_simp = ruleTrans argsInner_simp1 (congL Pair sub_ii_subst kt_v2)

        -- Mid: Comp2 Pair argsInner (KT (reify t_term)) at x.
        mid : Fun1
        mid = Comp2 Pair argsInner (KT (reify t_term))

        mid_step : Deriv (atomic (eqn (ap1 mid x)
                                       (ap2 Pair (ap1 argsInner x)
                                                 (ap1 (KT (reify t_term)) x))))
        mid_step = axComp2 Pair argsInner (KT (reify t_term)) x

        kt_t : Deriv (atomic (eqn (ap1 (KT (reify t_term)) x) (reify t_term)))
        kt_t = ktRed t_term x

        mid_simp1 : Deriv (atomic (eqn (ap1 mid x)
                                        (ap2 Pair (ap1 argsInner x)
                                                  (reify t_term))))
        mid_simp1 = ruleTrans mid_step (congR Pair (ap1 argsInner x) kt_t)

        mid_simp : Deriv (atomic (eqn (ap1 mid x)
                                       (ap2 Pair (ap2 Pair varCode2T sub_ii_subst)
                                                 (reify t_term))))
        mid_simp = ruleTrans mid_simp1 (congL Pair (reify t_term) argsInner_simp)

        -- Outer: Comp2 Pair (KT tagCode_ruleInst) mid at x.
        outer_step : Deriv (atomic (eqn (ap1 f_part_inner2 x)
                                         (ap2 Pair (ap1 (KT tagCode_ruleInst) x)
                                                   (ap1 mid x))))
        outer_step = axComp2 Pair (KT tagCode_ruleInst) mid x

        kt_tag : Deriv (atomic (eqn (ap1 (KT tagCode_ruleInst) x) tagCode_ruleInst))
        kt_tag = ktRed (natCode tagRuleInst) x

        outer_simp1 : Deriv (atomic (eqn (ap1 f_part_inner2 x)
                                          (ap2 Pair tagCode_ruleInst (ap1 mid x))))
        outer_simp1 = ruleTrans outer_step (congL Pair (ap1 mid x) kt_tag)
    in
        ruleTrans outer_simp1 (congR Pair tagCode_ruleInst mid_simp)

  --------------------------------------------------------------------
  -- f_part_inner1_unfold : ap1 f_part_inner1 x = Pair tagCode_ruleInst
  --                           (Pair (Pair varCode1T encoded_sub_ii)
  --                                 (ap1 f_part_inner2 x))
  --
  -- After Approach A (2026-05-02): substituent at var 1 is encoded_sub_ii
  -- (= reify (code (sub i i))) instead of sub_ii_subst.

  f_part_inner1_unfold : (x : Term) ->
    Deriv (atomic (eqn (ap1 f_part_inner1 x)
                       (ap2 Pair tagCode_ruleInst
                          (ap2 Pair (ap2 Pair varCode1T encoded_sub_ii)
                                    (ap1 f_part_inner2 x)))))
  f_part_inner1_unfold x =
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

        -- Mid: Comp2 Pair argsInner f_part_inner2 at x.
        mid : Fun1
        mid = Comp2 Pair argsInner f_part_inner2

        mid_step : Deriv (atomic (eqn (ap1 mid x)
                                       (ap2 Pair (ap1 argsInner x)
                                                 (ap1 f_part_inner2 x))))
        mid_step = axComp2 Pair argsInner f_part_inner2 x

        mid_simp : Deriv (atomic (eqn (ap1 mid x)
                                       (ap2 Pair (ap2 Pair varCode1T encoded_sub_ii)
                                                 (ap1 f_part_inner2 x))))
        mid_simp = ruleTrans mid_step
                     (congL Pair (ap1 f_part_inner2 x) argsInner_simp)

        -- Outer: Comp2 Pair (KT tagCode_ruleInst) mid at x.
        outer_step : Deriv (atomic (eqn (ap1 f_part_inner1 x)
                                         (ap2 Pair (ap1 (KT tagCode_ruleInst) x)
                                                   (ap1 mid x))))
        outer_step = axComp2 Pair (KT tagCode_ruleInst) mid x

        kt_tag : Deriv (atomic (eqn (ap1 (KT tagCode_ruleInst) x) tagCode_ruleInst))
        kt_tag = ktRed (natCode tagRuleInst) x

        outer_simp1 : Deriv (atomic (eqn (ap1 f_part_inner1 x)
                                          (ap2 Pair tagCode_ruleInst (ap1 mid x))))
        outer_simp1 = ruleTrans outer_step (congL Pair (ap1 mid x) kt_tag)
    in
        ruleTrans outer_simp1 (congR Pair tagCode_ruleInst mid_simp)

  --------------------------------------------------------------------
  -- encoded_th_x_unfold : ap1 encoded_th_x x =
  --   Pair (reify tagAp1) (Pair (reify (codeF1 thmT)) (cor x))

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
        inner_simp = ruleTrans inner_step
                       (congL Pair (ap1 cor x) kt_codef1)

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
  -- f_part_unfold : ap1 f_part x = Pair tagCode_ruleInst
  --                    (Pair (Pair varCode0T (encoded_th_x_at x))
  --                          (ap1 f_part_inner1 x))
  --
  -- After Approach A (2026-05-02): outermost sb substituent at var 0
  -- is encoded_th_x x (= encoded "th(x_)" Pair).

  f_part_unfold : (x : Term) ->
    Deriv (atomic (eqn (ap1 f_part x)
                       (ap2 Pair tagCode_ruleInst
                          (ap2 Pair (ap2 Pair varCode0T (encoded_th_x_at x))
                                    (ap1 f_part_inner1 x)))))
  f_part_unfold x =
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
        argsInner_simp = ruleTrans argsInner_simp1 (congL Pair (encoded_th_x_at x) kt_v0)

        mid : Fun1
        mid = Comp2 Pair argsInner f_part_inner1

        mid_step : Deriv (atomic (eqn (ap1 mid x)
                                       (ap2 Pair (ap1 argsInner x)
                                                 (ap1 f_part_inner1 x))))
        mid_step = axComp2 Pair argsInner f_part_inner1 x

        mid_simp : Deriv (atomic (eqn (ap1 mid x)
                                       (ap2 Pair (ap2 Pair varCode0T (encoded_th_x_at x))
                                                 (ap1 f_part_inner1 x))))
        mid_simp = ruleTrans mid_step
                     (congL Pair (ap1 f_part_inner1 x) argsInner_simp)

        outer_step : Deriv (atomic (eqn (ap1 f_part x)
                                         (ap2 Pair (ap1 (KT tagCode_ruleInst) x)
                                                   (ap1 mid x))))
        outer_step = axComp2 Pair (KT tagCode_ruleInst) mid x

        kt_tag : Deriv (atomic (eqn (ap1 (KT tagCode_ruleInst) x) tagCode_ruleInst))
        kt_tag = ktRed (natCode tagRuleInst) x

        outer_simp1 : Deriv (atomic (eqn (ap1 f_part x)
                                          (ap2 Pair tagCode_ruleInst (ap1 mid x))))
        outer_simp1 = ruleTrans outer_step (congL Pair (ap1 mid x) kt_tag)
    in
        ruleTrans outer_simp1 (congR Pair tagCode_ruleInst mid_simp)

  --------------------------------------------------------------------
  -- The 3-sb-step prefix.
  --
  -- After Approach A (2026-05-02): substituents are encoded mixed-form
  -- Pairs matching Guard's f(x).  Chronologically subT (vc2, sub_ii_subst)
  -- applied first to closed codeFormula t_formula, then
  -- subT (vc1, encoded_sub_ii) on closed result, then
  -- subT (vc0, encoded_th_x_at x) LAST.

  step3_pre : (x : Term) ->
    Deriv (atomic (eqn
      (ap1 thmT (ap1 f_part x))
      (ap2 subT (ap2 Pair varCode0T (encoded_th_x_at x))
            (ap2 subT (ap2 Pair varCode1T encoded_sub_ii)
                  (ap2 subT (ap2 Pair varCode2T sub_ii_subst)
                             (reify (codeFormula t_formula)))))))
  step3_pre x =
    let
        ----------------------------------------------------------------
        -- Layer 0 (innermost): apply thmTSubLemma at n=2, substituent
        -- sub_ii_subst, proof-index reify t_term.  codeP =
        -- reify(codeFormula t_formula).  Pair-shape via codeFormulaPairShape.

        layer0_shape = codeFormulaPairShape t_formula
        layer0_fp : Term
        layer0_fp = fst layer0_shape
        layer0_sp : Term
        layer0_sp = fst (snd layer0_shape)
        layer0_dh : Deriv (atomic (eqn (reify (codeFormula t_formula))
                                        (ap2 Pair layer0_fp layer0_sp)))
        layer0_dh = snd (snd layer0_shape)

        layer0_dispatch :
          Deriv (atomic (eqn
            (ap1 thmT (ap2 Pair tagCode_ruleInst
                        (ap2 Pair (ap2 Pair varCode2T sub_ii_subst)
                                  (reify t_term))))
            (ap2 subT (ap2 Pair varCode2T sub_ii_subst)
                       (reify (codeFormula t_formula)))))
        layer0_dispatch = thmTSubLemma (suc (suc zero)) sub_ii_subst (reify t_term)
                            (reify (codeFormula t_formula))
                            layer0_fp layer0_sp t_witness layer0_dh

        layer0_bridge : Deriv (atomic (eqn (ap1 thmT (ap1 f_part_inner2 x))
                                            (ap1 thmT (ap2 Pair tagCode_ruleInst
                                              (ap2 Pair (ap2 Pair varCode2T sub_ii_subst)
                                                        (reify t_term))))))
        layer0_bridge = cong1 thmT (f_part_inner2_unfold x)

        layer0 :
          Deriv (atomic (eqn (ap1 thmT (ap1 f_part_inner2 x))
            (ap2 subT (ap2 Pair varCode2T sub_ii_subst)
                       (reify (codeFormula t_formula)))))
        layer0 = ruleTrans layer0_bridge layer0_dispatch

        ----------------------------------------------------------------
        -- Layer 1: apply thmTSubLemma at n=1, substituent encoded_sub_ii,
        -- proof-index (ap1 f_part_inner2 x), codeP1 = layer0's RHS
        -- (= subT-form on reify(codeFormula t_formula)).
        -- Pair-shape via subTOfCodeFormulaImp_isPair (t_formula is imp).

        codeP1 : Term
        codeP1 = ap2 subT (ap2 Pair varCode2T sub_ii_subst)
                          (reify (codeFormula t_formula))

        layer1_shape = subTOfCodeFormulaImp_isPair (suc (suc zero))
                         (code (reify (codeFormula G)))
                         eq02 (eq12 imp eq01)
        layer1_fp : Term
        layer1_fp = fst layer1_shape
        layer1_sp : Term
        layer1_sp = fst (snd layer1_shape)
        layer1_dh : Deriv (atomic (eqn codeP1 (ap2 Pair layer1_fp layer1_sp)))
        layer1_dh = snd (snd layer1_shape)

        layer1_dispatch :
          Deriv (atomic (eqn
            (ap1 thmT (ap2 Pair tagCode_ruleInst
                        (ap2 Pair (ap2 Pair varCode1T encoded_sub_ii)
                                  (ap1 f_part_inner2 x))))
            (ap2 subT (ap2 Pair varCode1T encoded_sub_ii) codeP1)))
        layer1_dispatch = thmTSubLemma (suc zero) encoded_sub_ii
                            (ap1 f_part_inner2 x) codeP1
                            layer1_fp layer1_sp layer0 layer1_dh

        layer1_bridge : Deriv (atomic (eqn (ap1 thmT (ap1 f_part_inner1 x))
                                            (ap1 thmT (ap2 Pair tagCode_ruleInst
                                              (ap2 Pair (ap2 Pair varCode1T encoded_sub_ii)
                                                        (ap1 f_part_inner2 x))))))
        layer1_bridge = cong1 thmT (f_part_inner1_unfold x)

        layer1 :
          Deriv (atomic (eqn (ap1 thmT (ap1 f_part_inner1 x))
            (ap2 subT (ap2 Pair varCode1T encoded_sub_ii) codeP1)))
        layer1 = ruleTrans layer1_bridge layer1_dispatch

        ----------------------------------------------------------------
        -- Layer 2 (outermost): apply thmTSubLemma at n=0, substituent
        -- (encoded_th_x_at x), proof-index (ap1 f_part_inner1 x),
        -- codeP2 = layer1's RHS (= subT-form on codeP1 = nested
        -- subT-form on reify(codeFormula t_formula)).
        --
        -- Pair-shape: bridge codeP1 to reify(codeFormula F1) via
        -- subToFormulaBridge (where F1 = substF 2 (reify (codeFormula G))
        -- t_formula is imp), then apply subTOfCodeFormulaImp_isPair on F1.

        codeP2 : Term
        codeP2 = ap2 subT (ap2 Pair varCode1T encoded_sub_ii) codeP1

        F1Q : Formula
        F1Q = substF (suc (suc zero)) (reify (codeFormula G)) eq02
        F1R : Formula
        F1R = substF (suc (suc zero)) (reify (codeFormula G)) (eq12 imp eq01)

        codeP1_to_F1 : Deriv (atomic (eqn codeP1
                                          (reify (codeFormula (F1Q imp F1R)))))
        codeP1_to_F1 = subToFormulaBridge (suc (suc zero))
                         (reify (codeFormula G)) t_formula

        codeP2_via_bridge : Deriv (atomic (eqn codeP2
                                                (ap2 subT (ap2 Pair varCode1T encoded_sub_ii)
                                                          (reify (codeFormula (F1Q imp F1R))))))
        codeP2_via_bridge = congR subT (ap2 Pair varCode1T encoded_sub_ii) codeP1_to_F1

        layer2_shape = subTOfCodeFormulaImp_isPair (suc zero)
                         (code (ap2 sub i i)) F1Q F1R
        layer2_fp : Term
        layer2_fp = fst layer2_shape
        layer2_sp : Term
        layer2_sp = fst (snd layer2_shape)
        layer2_pairProof :
          Deriv (atomic (eqn (ap2 subT (ap2 Pair varCode1T encoded_sub_ii)
                                        (reify (codeFormula (F1Q imp F1R))))
                              (ap2 Pair layer2_fp layer2_sp)))
        layer2_pairProof = snd (snd layer2_shape)

        layer2_dh : Deriv (atomic (eqn codeP2 (ap2 Pair layer2_fp layer2_sp)))
        layer2_dh = ruleTrans codeP2_via_bridge layer2_pairProof

        layer2_dispatch :
          Deriv (atomic (eqn
            (ap1 thmT (ap2 Pair tagCode_ruleInst
                        (ap2 Pair (ap2 Pair varCode0T (encoded_th_x_at x))
                                  (ap1 f_part_inner1 x))))
            (ap2 subT (ap2 Pair varCode0T (encoded_th_x_at x)) codeP2)))
        layer2_dispatch = thmTSubLemma zero (encoded_th_x_at x)
                            (ap1 f_part_inner1 x) codeP2
                            layer2_fp layer2_sp layer1 layer2_dh

        layer2_bridge : Deriv (atomic (eqn (ap1 thmT (ap1 f_part x))
                                            (ap1 thmT (ap2 Pair tagCode_ruleInst
                                              (ap2 Pair (ap2 Pair varCode0T (encoded_th_x_at x))
                                                        (ap1 f_part_inner1 x))))))
        layer2_bridge = cong1 thmT (f_part_unfold x)

    in ruleTrans layer2_bridge layer2_dispatch

  --------------------------------------------------------------------
  -- step3_l : the canonicalized step 3 of Guard's Theorem 14.
  --
  -- Combines step3_pre (the 3 sb-applications) with the canonicalization
  -- (Stage A + B + C from BRA.Th14Step3Canon, plumbed via Comp2/KT bridges)
  -- and two mp-dispatches (thmTDispMp_param at g_part_inner / g_part).
  --
  -- The result is unconditionally lifted under the antecedent  PrAtX x
  -- (which is not used in the proof body — step3 only requires the
  -- structural canonicalization, not the diagonalization hypothesis).

  open import BRA.Cor      using (corOfReify)
  open import BRA.Thm.ThmT using
    ( thmTDispMp_param ; thmTDispMp_param_l ; tagCode_mp )
  open import BRA.Thm14Constr5Final using ()
  open Th14Constr5Final r12_th r12_sub
    using (g_part_inner ; g_part ; D_thmT ; D_sub_at_ii ; D_sub)
  open import BRA.Th14GPartUnfolds using (module Th14GPartUnfolds)
  open Th14GPartUnfolds r12_th r12_sub
    using (g_part_inner_unfold ; g_part_unfold)

  open import BRA.Th14Step3Canon
    using (F_a ; F_b ; step3_canon ; target_c)

  open import BRA.Thm.EvalHelpers using
    ( liftAxiom ; liftedRuleTrans ; liftedCong1 ; liftedCongR )
  open import BRA.GoedelII using (PrAtX)
  open import BRA.CorCGBridge using (corCGBridge)
  open import BRA.Th14Constr5
  open Th14Constr5 r12_th r12_sub using (step1_l ; step2_l)

  -- Helper bridges (placed outside let-bindings since `where` not allowed there).
  -- tagCode_ruleInst = reify (natCode tagRuleInst) = reify (nd lf (natCode tagMp))
  --                  = ap2 Pair O (reify (natCode tagMp))   (definitionally)
  -- So Snd tagCode_ruleInst = reify (natCode tagMp) via axSnd.

  open import BRA.Thm.Tag using (tagMp ; tagAxContrapos)

  shape_inner_pair_bridge :
    Deriv (atomic (eqn tagCode_ruleInst
                        (ap2 Pair O (ap1 Snd tagCode_ruleInst))))
  shape_inner_pair_bridge =
    congR Pair O (ruleSym (axSnd O (reify (natCode tagMp))))

  -- tagCode_mp = reify (natCode tagMp) = reify (nd lf (natCode tagAxContrapos))
  --            = ap2 Pair O (reify (natCode tagAxContrapos))   (definitionally)

  shape_outer_pair_bridge :
    Deriv (atomic (eqn tagCode_mp (ap2 Pair O (ap1 Snd tagCode_mp))))
  shape_outer_pair_bridge =
    congR Pair O (ruleSym (axSnd O (reify (natCode tagAxContrapos))))

  step3_l : (x : Term) ->
    Deriv (PrAtX x imp
            atomic (eqn (ap1 thmT (ap1 g_part x))
                        (ap2 Pair (encoded_th_x_at x) encoded_sub_ii)))
  step3_l x =
    let
        Pf : Formula
        Pf = PrAtX x

        ----------------------------------------------------------------
        -- Step 1: Combine step3_pre + step3_canon to get
        --   thmT (ap1 f_part x) = target_c x.
        d1_unlifted : Deriv (atomic (eqn (ap1 thmT (ap1 f_part x))
                                          (target_c x)))
        d1_unlifted = ruleTrans (step3_pre x) (step3_canon x)

        antec1 : Term
        antec1 = ap2 Pair (encoded_th_x_at x) (reify (code cG))

        antec2 : Term
        antec2 = ap2 Pair encoded_sub_ii (reify (code cG))

        conseq : Term
        conseq = ap2 Pair (encoded_th_x_at x) encoded_sub_ii

        inner_rest : Term
        inner_rest = ap2 Pair (reify tagImp) (ap2 Pair antec2 conseq)

        ----------------------------------------------------------------
        -- Step 2: Inner mp dispatch (using lifted dispatcher
        -- thmTDispMp_param_l with verifying body_mp_v).
        -- y1T = ap1 f_part x ; y2T = ap1 D_thmT x.
        -- innerL is built from step1_l x bridged via corCGBridge.

        y1T_inner : Term
        y1T_inner = ap1 f_part x

        y2T_inner : Term
        y2T_inner = ap1 D_thmT x

        f_part_pair_form : Term
        f_part_pair_form = ap2 Pair tagCode_ruleInst
                             (ap2 Pair (ap2 Pair varCode0T (encoded_th_x_at x))
                                       (ap1 f_part_inner1 x))

        shape_inner_step1 : Deriv (atomic (eqn (ap1 Fst y1T_inner)
                                                 (ap1 Fst f_part_pair_form)))
        shape_inner_step1 = cong1 Fst (f_part_unfold x)

        shape_inner_step2 : Deriv (atomic (eqn (ap1 Fst f_part_pair_form)
                                                 tagCode_ruleInst))
        shape_inner_step2 = axFst tagCode_ruleInst
                              (ap2 Pair (ap2 Pair varCode0T (encoded_th_x_at x))
                                        (ap1 f_part_inner1 x))

        shape_inner : Deriv (atomic (eqn (ap1 Fst y1T_inner) tagCode_ruleInst))
        shape_inner = ruleTrans shape_inner_step1 shape_inner_step2

        shape_inner_pair : Deriv (atomic (eqn (ap1 Fst y1T_inner)
                                                (ap2 Pair O (ap1 Snd tagCode_ruleInst))))
        shape_inner_pair = ruleTrans shape_inner shape_inner_pair_bridge

        ----------------------------------------------------------------
        -- Lift the closed hypotheses to PrAtX x form.

        shape_inner_pair_L :
          Deriv (Pf imp atomic (eqn (ap1 Fst y1T_inner)
                                     (ap2 Pair O (ap1 Snd tagCode_ruleInst))))
        shape_inner_pair_L = liftAxiom Pf shape_inner_pair

        d1_inner_L :
          Deriv (Pf imp atomic (eqn (ap1 thmT y1T_inner) (target_c x)))
        d1_inner_L = liftAxiom Pf d1_unlifted

        ----------------------------------------------------------------
        -- innerCheck for inner mp:  thmT (D_thmT x) = antec1 .
        -- step1_l x : thmT(D_thmT x) = codeFTeq1Hyp thmT x cG
        --           = Pair (encoded_th_x_at x) (cor cG) .
        -- corCGBridge gives  cor cG = reify (code cG) , so
        --   liftedCongR Pair (cor cG) (reify (code cG)) (encoded_th_x_at x)
        -- bridges  Pair (encoded_th_x_at x) (cor cG) -> antec1 .

        cor_cG_eq_L :
          Deriv (Pf imp atomic (eqn (ap1 cor cG) (reify (code cG))))
        cor_cG_eq_L = liftAxiom Pf corCGBridge

        codeFTeq1Hyp_to_antec1_L :
          Deriv (Pf imp atomic (eqn
            (ap2 Pair (encoded_th_x_at x) (ap1 cor cG))
            antec1))
        codeFTeq1Hyp_to_antec1_L =
          liftedCongR Pf Pair (ap1 cor cG) (reify (code cG))
            (encoded_th_x_at x) cor_cG_eq_L

        innerCheck_inner_L :
          Deriv (Pf imp atomic (eqn (ap1 thmT y2T_inner) antec1))
        innerCheck_inner_L =
          liftedRuleTrans Pf (ap1 thmT y2T_inner)
            (ap2 Pair (encoded_th_x_at x) (ap1 cor cG))
            antec1
            (step1_l x) codeFTeq1Hyp_to_antec1_L

        inner_mp_raw_L :
          Deriv (Pf imp atomic (eqn
            (ap1 thmT (ap2 Pair tagCode_mp (ap2 Pair y1T_inner y2T_inner)))
            inner_rest))
        inner_mp_raw_L = thmTDispMp_param_l Pf y1T_inner y2T_inner
                           (ap1 Snd tagCode_ruleInst) O
                           antec1 inner_rest
                           shape_inner_pair_L d1_inner_L
                           innerCheck_inner_L

        inner_mp_L :
          Deriv (Pf imp atomic (eqn (ap1 thmT (ap1 g_part_inner x)) inner_rest))
        inner_mp_L =
          liftedRuleTrans Pf
            (ap1 thmT (ap1 g_part_inner x))
            (ap1 thmT (ap2 Pair tagCode_mp (ap2 Pair y1T_inner y2T_inner)))
            inner_rest
            (liftedCong1 Pf thmT
              (ap1 g_part_inner x)
              (ap2 Pair tagCode_mp (ap2 Pair y1T_inner y2T_inner))
              (liftAxiom Pf (g_part_inner_unfold x)))
            inner_mp_raw_L

        ----------------------------------------------------------------
        -- Step 3: Outer mp dispatch.
        -- y1T = ap1 g_part_inner x ; y2T = ap1 D_sub_at_ii x.

        y1T_outer : Term
        y1T_outer = ap1 g_part_inner x

        y2T_outer : Term
        y2T_outer = ap1 D_sub_at_ii x

        g_part_inner_pair_form : Term
        g_part_inner_pair_form = ap2 Pair tagCode_mp (ap2 Pair y1T_inner y2T_inner)

        shape_outer_step1 : Deriv (atomic (eqn (ap1 Fst y1T_outer)
                                                 (ap1 Fst g_part_inner_pair_form)))
        shape_outer_step1 = cong1 Fst (g_part_inner_unfold x)

        shape_outer_step2 : Deriv (atomic (eqn (ap1 Fst g_part_inner_pair_form) tagCode_mp))
        shape_outer_step2 = axFst tagCode_mp (ap2 Pair y1T_inner y2T_inner)

        shape_outer : Deriv (atomic (eqn (ap1 Fst y1T_outer) tagCode_mp))
        shape_outer = ruleTrans shape_outer_step1 shape_outer_step2

        shape_outer_pair : Deriv (atomic (eqn (ap1 Fst y1T_outer)
                                                (ap2 Pair O (ap1 Snd tagCode_mp))))
        shape_outer_pair = ruleTrans shape_outer shape_outer_pair_bridge

        shape_outer_pair_L :
          Deriv (Pf imp atomic (eqn (ap1 Fst y1T_outer)
                                     (ap2 Pair O (ap1 Snd tagCode_mp))))
        shape_outer_pair_L = liftAxiom Pf shape_outer_pair

        ----------------------------------------------------------------
        -- innerCheck for outer mp:  thmT (D_sub_at_ii x) = antec2 .
        -- step2_l x : thmT(ap2 D_sub i i) = codeFTeq2Hyp sub i i cG
        --   = Pair (Pair tagAp2 (Pair codeF2sub (Pair (cor i)(cor i)))) (cor cG) .
        -- LHS bridge: D_sub_at_ii x = ap2 D_sub i i  via axComp2 + axKT.
        -- RHS bridge: cor i -> reify (code i)  via corOfReify j (twice),
        --             cor cG -> reify (code cG) via corCGBridge.

        kt_red : Deriv (atomic (eqn (ap1 (KT i) x) i))
        kt_red = axKT j x

        D_sub_at_ii_unfold :
          Deriv (atomic (eqn (ap1 D_sub_at_ii x) (ap2 D_sub i i)))
        D_sub_at_ii_unfold =
          let s1 = axComp2 D_sub (KT i) (KT i) x
              bL = congL D_sub (ap1 (KT i) x) kt_red
              bR = congR D_sub i kt_red
          in ruleTrans s1 (ruleTrans bL bR)

        thmT_lhs_outer_eq :
          Deriv (atomic (eqn (ap1 thmT (ap1 D_sub_at_ii x))
                              (ap1 thmT (ap2 D_sub i i))))
        thmT_lhs_outer_eq = cong1 thmT D_sub_at_ii_unfold

        thmT_lhs_outer_eq_L :
          Deriv (Pf imp atomic (eqn (ap1 thmT (ap1 D_sub_at_ii x))
                                     (ap1 thmT (ap2 D_sub i i))))
        thmT_lhs_outer_eq_L = liftAxiom Pf thmT_lhs_outer_eq

        -- Bridge codeFTeq2Hyp form to antec2.
        cor_i_eq : Deriv (atomic (eqn (ap1 cor i) (reify (code i))))
        cor_i_eq = corOfReify j

        innermostL :
          Deriv (atomic (eqn (ap2 Pair (ap1 cor i) (ap1 cor i))
                              (ap2 Pair (reify (code i)) (ap1 cor i))))
        innermostL = congL Pair (ap1 cor i) cor_i_eq

        innermostR :
          Deriv (atomic (eqn (ap2 Pair (reify (code i)) (ap1 cor i))
                              (ap2 Pair (reify (code i)) (reify (code i)))))
        innermostR = congR Pair (reify (code i)) cor_i_eq

        innermost :
          Deriv (atomic (eqn (ap2 Pair (ap1 cor i) (ap1 cor i))
                              (ap2 Pair (reify (code i)) (reify (code i)))))
        innermost = ruleTrans innermostL innermostR

        layer3 :
          Deriv (atomic (eqn (ap2 Pair (reify (codeF2 sub))
                                        (ap2 Pair (ap1 cor i) (ap1 cor i)))
                              (ap2 Pair (reify (codeF2 sub))
                                        (ap2 Pair (reify (code i)) (reify (code i))))))
        layer3 = congR Pair (reify (codeF2 sub)) innermost

        layer2 :
          Deriv (atomic (eqn
            (ap2 Pair (reify tagAp2)
                       (ap2 Pair (reify (codeF2 sub))
                                  (ap2 Pair (ap1 cor i) (ap1 cor i))))
            encoded_sub_ii))
        layer2 = congR Pair (reify tagAp2) layer3

        layer1 :
          Deriv (atomic (eqn
            (ap2 Pair (ap2 Pair (reify tagAp2)
                       (ap2 Pair (reify (codeF2 sub))
                                  (ap2 Pair (ap1 cor i) (ap1 cor i))))
                       (ap1 cor cG))
            (ap2 Pair encoded_sub_ii (ap1 cor cG))))
        layer1 = congL Pair (ap1 cor cG) layer2

        layer0 :
          Deriv (atomic (eqn (ap2 Pair encoded_sub_ii (ap1 cor cG))
                              antec2))
        layer0 = congR Pair encoded_sub_ii corCGBridge

        codeFTeq2Hyp_to_antec2 :
          Deriv (atomic (eqn
            (ap2 Pair (ap2 Pair (reify tagAp2)
                       (ap2 Pair (reify (codeF2 sub))
                                  (ap2 Pair (ap1 cor i) (ap1 cor i))))
                       (ap1 cor cG))
            antec2))
        codeFTeq2Hyp_to_antec2 = ruleTrans layer1 layer0

        codeFTeq2Hyp_to_antec2_L :
          Deriv (Pf imp atomic (eqn
            (ap2 Pair (ap2 Pair (reify tagAp2)
                       (ap2 Pair (reify (codeF2 sub))
                                  (ap2 Pair (ap1 cor i) (ap1 cor i))))
                       (ap1 cor cG))
            antec2))
        codeFTeq2Hyp_to_antec2_L = liftAxiom Pf codeFTeq2Hyp_to_antec2

        innerCheck_outer_L :
          Deriv (Pf imp atomic (eqn (ap1 thmT y2T_outer) antec2))
        innerCheck_outer_L =
          let -- Compose: thmT(D_sub_at_ii x) = thmT(D_sub i i) = codeFTeq2Hyp = antec2 .
              step_LHS =
                liftedRuleTrans Pf
                  (ap1 thmT (ap1 D_sub_at_ii x))
                  (ap1 thmT (ap2 D_sub i i))
                  _
                  thmT_lhs_outer_eq_L
                  (step2_l x)
          in liftedRuleTrans Pf
               (ap1 thmT (ap1 D_sub_at_ii x))
               _
               antec2
               step_LHS
               codeFTeq2Hyp_to_antec2_L

        outer_mp_raw_L :
          Deriv (Pf imp atomic (eqn
            (ap1 thmT (ap2 Pair tagCode_mp (ap2 Pair y1T_outer y2T_outer)))
            conseq))
        outer_mp_raw_L = thmTDispMp_param_l Pf y1T_outer y2T_outer
                           (ap1 Snd tagCode_mp) O
                           antec2 conseq
                           shape_outer_pair_L inner_mp_L
                           innerCheck_outer_L

    in liftedRuleTrans Pf
         (ap1 thmT (ap1 g_part x))
         (ap1 thmT (ap2 Pair tagCode_mp (ap2 Pair y1T_outer y2T_outer)))
         conseq
         (liftedCong1 Pf thmT
           (ap1 g_part x)
           (ap2 Pair tagCode_mp (ap2 Pair y1T_outer y2T_outer))
           (liftAxiom Pf (g_part_unfold x)))
         outer_mp_raw_L
