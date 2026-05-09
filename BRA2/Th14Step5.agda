{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Th14Step5
--
-- Phase C step 5 of the Theorem 14 closure: step5_l + final constr5.
--
-- The encoded constr5 chain:
--   constr5_final(x) = mp_enc (mp_enc (h_part_skel(x), g_part(x)), K_part(x))
--
-- Two mp dispatches (thmTDispMp_param) collapse the chain:
--   * Inner mp at `mp(h_part_skel, g_part)`:
--     thmT(h_part_skel x) = encoded ex-falso (3-piece imp)  via h_part_canon.
--     Dispatcher projects to encoded "((thmT(cor x) ≠ sub(i,i)) imp bot)".
--   * Outer mp at `mp(constr5_inner, K_part)`:
--     d1 = encoded "(neg ...) imp bot" (imp-shaped).
--     Dispatcher projects to encoded bot.
--
-- Result:  step5_l : (x : Term) ->
--   Deriv (PrAtX x imp atomic (eqn (ap1 thmT (ap1 constr5_final x))
--                                   (reify (codeFormula bot))))
--
-- Note: K_part_l (the soundness verification for the negation step)
-- is NOT used in this derivation -- the dispatcher's qT projection
-- gives us the equation regardless of K_part_l's value.  K_part_l is
-- still needed to certify the OVERALL soundness of constr5 as a proof
-- (it verifies that the syntactic Pair tagCode_mp ... is a sound
-- inference), but step5_l's syntactic-projection contract does not
-- depend on it.
--
-- The body uses no PrAtX hypothesis -- it's all unlifted dispatchers
-- composed via liftAxiom at the end.
--
-- ASCII only.  No postulates, no holes.

module BRA2.Th14Step5 where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.DerivThreshold
open import BRA2.Cor      using (cor)
open import BRA2.Sub      using (sub)
open import BRA2.SubT     using (subT)
open import BRA2.StepReduce using (ktRed)
open import BRA2.Thm.Tag  using (tagMp ; tagAxContrapos ; tagRuleInst)

open import BRA2.Thm.ThmT using
  ( thmT ; tagCode_ruleInst ; tagCode_mp
  ; thmTDispMp_param ; thmTDispMp_param_l )

open import BRA2.Thm.EvalHelpers using
  ( liftAxiom ; liftedRuleTrans ; liftedCong1 )

open import BRA2.Thm12 using (Thm12_F1_Result ; Thm12_F2_Result)
open import BRA2.Thm14Constr5Final using (module Th14Constr5Final)

open import BRA2.GoedelII using (cG ; G ; i ; j ; PrAtX ; bot)

open import BRA2.Th14Step5HPart
  using (target_h ; target_h_eq01 ; module Th14Step5HPart)

import BRA2.Th14StepHPre
import BRA2.Th14HUnfolds
import BRA2.Th14Step3
import BRA2.Th14Step4Final

----------------------------------------------------------------------
-- Convenience.

private
  encoded_th_x_at : Term -> Term
  encoded_th_x_at x = ap2 Pair (reify tagAp1)
                              (ap2 Pair (reify (codeF1 thmT)) (ap1 cor x))

  encoded_sub_ii : Term
  encoded_sub_ii = reify (code (ap2 sub i i))

  -- bot_local matches Th14Step5HPart's bot_local:
  -- bot = atomic (eqn O (ap2 Pair O O)).
  bot_local : Formula
  bot_local = atomic (eqn O (ap2 Pair O O))

----------------------------------------------------------------------
-- The Th14Step5 module proper.

module Th14Step5
  (r12_th  : Thm12_F1_Result thmT)
  (r12_sub : Thm12_F2_Result sub)
  where

  open Th14Constr5Final r12_th r12_sub
    using (h_part_skel ; g_part ; K_part)

  open BRA2.Th14HUnfolds.Th14HUnfolds r12_th r12_sub
    using (h_part_skel_unfold)

  open BRA2.Th14StepHPre.Th14StepHPre r12_th r12_sub
    using (h_part_pre)

  open BRA2.Th14Step5HPart.Th14Step5HPart r12_th r12_sub
    using (h_part_skel_l)

  open import BRA2.Th14Step5HPart using (h_part_canon)

  -- Inner-check witnesses for the verifying mp dispatcher
  -- (load-bearing under PrAtX x):
  open BRA2.Th14Step3.Th14Step3 r12_th r12_sub using (step3_l)
  open BRA2.Th14Step4Final.Th14Step4Final r12_th r12_sub using (K_part_l)

  --------------------------------------------------------------------
  -- constr5_final : the corrected constr5 using h_part_skel directly.
  --
  -- mp(mp(h_part_skel, g_part), K_part) — Guard's intended chain.

  constr5_inner_final : Fun1
  constr5_inner_final =
    Comp2 Pair (KT tagCode_mp) (Comp2 Pair h_part_skel g_part)

  constr5_final : Fun1
  constr5_final =
    Comp2 Pair (KT tagCode_mp) (Comp2 Pair constr5_inner_final K_part)

  --------------------------------------------------------------------
  -- Pair-of-Comp2 unfolds for constr5_final.

  constr5_inner_final_unfold : (x : Term) ->
    Deriv (atomic (eqn (ap1 constr5_inner_final x)
                       (ap2 Pair tagCode_mp
                          (ap2 Pair (ap1 h_part_skel x) (ap1 g_part x)))))
  constr5_inner_final_unfold x =
    let
        mid : Fun1
        mid = Comp2 Pair h_part_skel g_part

        mid_step : Deriv (atomic (eqn (ap1 mid x)
                                       (ap2 Pair (ap1 h_part_skel x)
                                                 (ap1 g_part x))))
        mid_step = axComp2 Pair h_part_skel g_part x

        outer_step : Deriv (atomic (eqn (ap1 constr5_inner_final x)
                                         (ap2 Pair (ap1 (KT tagCode_mp) x)
                                                   (ap1 mid x))))
        outer_step = axComp2 Pair (KT tagCode_mp) mid x

        kt_tag : Deriv (atomic (eqn (ap1 (KT tagCode_mp) x) tagCode_mp))
        kt_tag = ktRed (natCode tagMp) (natCode_isValue tagMp) x

        outer_simp1 : Deriv (atomic (eqn (ap1 constr5_inner_final x)
                                          (ap2 Pair tagCode_mp (ap1 mid x))))
        outer_simp1 = ruleTrans outer_step (congL Pair (ap1 mid x) kt_tag)
    in
        ruleTrans outer_simp1 (congR Pair tagCode_mp mid_step)

  constr5_final_unfold : (x : Term) ->
    Deriv (atomic (eqn (ap1 constr5_final x)
                       (ap2 Pair tagCode_mp
                          (ap2 Pair (ap1 constr5_inner_final x) (ap1 K_part x)))))
  constr5_final_unfold x =
    let
        mid : Fun1
        mid = Comp2 Pair constr5_inner_final K_part

        mid_step : Deriv (atomic (eqn (ap1 mid x)
                                       (ap2 Pair (ap1 constr5_inner_final x)
                                                 (ap1 K_part x))))
        mid_step = axComp2 Pair constr5_inner_final K_part x

        outer_step : Deriv (atomic (eqn (ap1 constr5_final x)
                                         (ap2 Pair (ap1 (KT tagCode_mp) x)
                                                   (ap1 mid x))))
        outer_step = axComp2 Pair (KT tagCode_mp) mid x

        kt_tag : Deriv (atomic (eqn (ap1 (KT tagCode_mp) x) tagCode_mp))
        kt_tag = ktRed (natCode tagMp) (natCode_isValue tagMp) x

        outer_simp1 : Deriv (atomic (eqn (ap1 constr5_final x)
                                          (ap2 Pair tagCode_mp (ap1 mid x))))
        outer_simp1 = ruleTrans outer_step (congL Pair (ap1 mid x) kt_tag)
    in
        ruleTrans outer_simp1 (congR Pair tagCode_mp mid_step)

  --------------------------------------------------------------------
  -- Helper bridges (h_part_skel and constr5_inner_final's Fst projections).

  shape_inner_pair_bridge_step5 :
    Deriv (atomic (eqn tagCode_ruleInst
                        (ap2 Pair O (ap1 Snd tagCode_ruleInst))))
  shape_inner_pair_bridge_step5 =
    congR Pair O (ruleSym (axSnd O (reify (natCode tagMp))))

  shape_outer_pair_bridge_step5 :
    Deriv (atomic (eqn tagCode_mp (ap2 Pair O (ap1 Snd tagCode_mp))))
  shape_outer_pair_bridge_step5 =
    congR Pair O (ruleSym (axSnd O (reify (natCode tagAxContrapos))))

  --------------------------------------------------------------------
  -- step5_l : the final Thm 14 contract, lifted under PrAtX x.

  step5_l : (x : Term) ->
    Deriv (PrAtX x imp atomic (eqn (ap1 thmT (ap1 constr5_final x))
                                    (reify (codeFormula bot))))
  step5_l x =
    let
        ----------------------------------------------------------------
        -- Step 1: Combine h_part_pre + h_part_canon to get
        --   thmT (ap1 h_part_skel x) = target_h x.
        d1_unlifted : Deriv (atomic (eqn (ap1 thmT (ap1 h_part_skel x))
                                          (target_h x)))
        d1_unlifted = ruleTrans (h_part_pre x) (h_part_canon x)

        ----------------------------------------------------------------
        -- target_h x decomposed:
        --   = Pair tagImp (Pair P_enc R_enc)
        -- where:
        --   P_enc = target_h_eq01 x = encoded "thmT(cor x) = sub(i,i)"
        --   R_enc = Pair tagImp (Pair (Pair tagNeg P_enc) (codeFormula bot))

        P_enc : Term
        P_enc = target_h_eq01 x

        neg_P : Term
        neg_P = ap2 Pair (reify tagNeg) P_enc

        bot_enc : Term
        bot_enc = reify (codeFormula bot_local)

        R_enc : Term
        R_enc = ap2 Pair (reify tagImp) (ap2 Pair neg_P bot_enc)

        ----------------------------------------------------------------
        -- Step 2: Inner mp dispatch at mp(h_part_skel, g_part).

        y1T_inner : Term
        y1T_inner = ap1 h_part_skel x

        y2T_inner : Term
        y2T_inner = ap1 g_part x

        -- Shape: Fst (h_part_skel x) = tagCode_ruleInst (= Pair O ...).
        shape_inner_step1 : Deriv (atomic (eqn (ap1 Fst y1T_inner)
                                                 (ap1 Fst (ap2 Pair tagCode_ruleInst
                                                   (ap2 Pair (ap2 Pair (reify (code (var zero)))
                                                                       (encoded_th_x_at x))
                                                             (ap1 (Th14Constr5Final.h_part_inner1 r12_th r12_sub) x))))))
        shape_inner_step1 = cong1 Fst (h_part_skel_unfold x)

        shape_inner_step2 : Deriv (atomic (eqn
          (ap1 Fst (ap2 Pair tagCode_ruleInst
                       (ap2 Pair (ap2 Pair (reify (code (var zero)))
                                            (encoded_th_x_at x))
                                  (ap1 (Th14Constr5Final.h_part_inner1 r12_th r12_sub) x))))
          tagCode_ruleInst))
        shape_inner_step2 = axFst tagCode_ruleInst
          (ap2 Pair (ap2 Pair (reify (code (var zero)))
                              (encoded_th_x_at x))
                    (ap1 (Th14Constr5Final.h_part_inner1 r12_th r12_sub) x))

        shape_inner : Deriv (atomic (eqn (ap1 Fst y1T_inner) tagCode_ruleInst))
        shape_inner = ruleTrans shape_inner_step1 shape_inner_step2

        shape_inner_pair : Deriv (atomic (eqn (ap1 Fst y1T_inner)
                                                (ap2 Pair O (ap1 Snd tagCode_ruleInst))))
        shape_inner_pair = ruleTrans shape_inner shape_inner_pair_bridge_step5

        ----------------------------------------------------------------
        -- Lifted hypotheses for thmTDispMp_param_l (under PrAtX x).

        Pf : Formula
        Pf = PrAtX x

        shape_inner_pair_L :
          Deriv (Pf imp atomic (eqn (ap1 Fst y1T_inner)
                                     (ap2 Pair O (ap1 Snd tagCode_ruleInst))))
        shape_inner_pair_L = liftAxiom Pf shape_inner_pair

        d1_inner_L :
          Deriv (Pf imp atomic (eqn (ap1 thmT y1T_inner) (target_h x)))
        d1_inner_L = liftAxiom Pf d1_unlifted

        -- step3_l x is exactly the inner-check witness:
        --   Deriv (Pf imp atomic (eqn (thmT (g_part x)) P_enc))
        innerCheck_inner_L :
          Deriv (Pf imp atomic (eqn (ap1 thmT y2T_inner) P_enc))
        innerCheck_inner_L = step3_l x

        inner_mp_raw_L :
          Deriv (Pf imp atomic (eqn
            (ap1 thmT (ap2 Pair tagCode_mp (ap2 Pair y1T_inner y2T_inner)))
            R_enc))
        inner_mp_raw_L =
          thmTDispMp_param_l Pf y1T_inner y2T_inner
            (ap1 Snd tagCode_ruleInst) O P_enc R_enc
            shape_inner_pair_L d1_inner_L innerCheck_inner_L

        inner_mp_L :
          Deriv (Pf imp atomic (eqn (ap1 thmT (ap1 constr5_inner_final x)) R_enc))
        inner_mp_L =
          liftedRuleTrans Pf
            (ap1 thmT (ap1 constr5_inner_final x))
            (ap1 thmT (ap2 Pair tagCode_mp (ap2 Pair y1T_inner y2T_inner)))
            R_enc
            (liftedCong1 Pf thmT
              (ap1 constr5_inner_final x)
              (ap2 Pair tagCode_mp (ap2 Pair y1T_inner y2T_inner))
              (liftAxiom Pf (constr5_inner_final_unfold x)))
            inner_mp_raw_L

        ----------------------------------------------------------------
        -- Step 3: Outer mp dispatch at mp(constr5_inner_final, K_part).

        y1T_outer : Term
        y1T_outer = ap1 constr5_inner_final x

        y2T_outer : Term
        y2T_outer = ap1 K_part x

        -- Shape: Fst (constr5_inner_final x) = tagCode_mp.
        shape_outer_step1 : Deriv (atomic (eqn (ap1 Fst y1T_outer)
                                                 (ap1 Fst (ap2 Pair tagCode_mp (ap2 Pair y1T_inner y2T_inner)))))
        shape_outer_step1 = cong1 Fst (constr5_inner_final_unfold x)

        shape_outer_step2 : Deriv (atomic (eqn
          (ap1 Fst (ap2 Pair tagCode_mp (ap2 Pair y1T_inner y2T_inner)))
          tagCode_mp))
        shape_outer_step2 = axFst tagCode_mp (ap2 Pair y1T_inner y2T_inner)

        shape_outer : Deriv (atomic (eqn (ap1 Fst y1T_outer) tagCode_mp))
        shape_outer = ruleTrans shape_outer_step1 shape_outer_step2

        shape_outer_pair : Deriv (atomic (eqn (ap1 Fst y1T_outer)
                                                (ap2 Pair O (ap1 Snd tagCode_mp))))
        shape_outer_pair = ruleTrans shape_outer shape_outer_pair_bridge_step5

        shape_outer_pair_L :
          Deriv (Pf imp atomic (eqn (ap1 Fst y1T_outer)
                                     (ap2 Pair O (ap1 Snd tagCode_mp))))
        shape_outer_pair_L = liftAxiom Pf shape_outer_pair

        -- K_part_l x is the outer-check witness:
        --   Deriv (Pf imp atomic (eqn (thmT (K_part x)) neg_P))
        innerCheck_outer_L :
          Deriv (Pf imp atomic (eqn (ap1 thmT y2T_outer) neg_P))
        innerCheck_outer_L = K_part_l x

        outer_mp_raw_L :
          Deriv (Pf imp atomic (eqn
            (ap1 thmT (ap2 Pair tagCode_mp (ap2 Pair y1T_outer y2T_outer)))
            bot_enc))
        outer_mp_raw_L =
          thmTDispMp_param_l Pf y1T_outer y2T_outer
            (ap1 Snd tagCode_mp) O neg_P bot_enc
            shape_outer_pair_L inner_mp_L innerCheck_outer_L

    in liftedRuleTrans Pf
         (ap1 thmT (ap1 constr5_final x))
         (ap1 thmT (ap2 Pair tagCode_mp (ap2 Pair y1T_outer y2T_outer)))
         bot_enc
         (liftedCong1 Pf thmT
           (ap1 constr5_final x)
           (ap2 Pair tagCode_mp (ap2 Pair y1T_outer y2T_outer))
           (liftAxiom Pf (constr5_final_unfold x)))
         outer_mp_raw_L
