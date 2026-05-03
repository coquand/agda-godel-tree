{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Th14Step4
--
-- Phase C step 4 of the Theorem 14 closure (NEXT-SESSION-PHASE-C.md):
-- single sb-step at proof-index x, substituent (cor x), var index 1,
-- under hypothesis  PrAtX x = atomic (eqn (ap1 thmT x) cG) .
--
-- Mirrors Guard p.17 line 4 (the K(x) step):
--     th(x) = j  =>  th(K(x)) = "th(cor x) != sub(i,i)"
-- where  K(x) = sb(num x, 1, j)  encoded as a single ruleInst layer.
--
-- This file delivers
--
--   step4_l : (x : Term) ->
--     Deriv (PrAtX x imp atomic (eqn (ap1 thmT (ap1 K_part x))
--                                     (ap2 subT (ap2 Pair varCode1T
--                                                     (ap1 cor x))
--                                                cG)))
--
-- where the RHS is the literal subT-output of the Definition 12 line 2
-- evaluation (= encoded "th(cor x) != sub(i,i)" once we identify subT
-- at codeFormula G with cG-substituted form per Guard's encoding).
--
-- ASCII only.  No postulates, no holes.

module BRA.Th14Step4 where

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
  ; thmTDispRuleInst_param
  ; thmTDispRuleInst_param_l
  ; tagCode_ruleInst
  )

open import BRA.Thm.EvalHelpers
  using (liftAxiom ; liftedRuleTrans ; liftedCongR)

open import BRA.Thm14SubLemma using (thmTSubLemma)

open import BRA.Thm12 using (Thm12_F1_Result ; Thm12_F2_Result)

open import BRA.Thm14Constr5Final using (module Th14Constr5Final)

open import BRA.GoedelII using (i ; cG ; G ; PrAtX)
open import BRA.SoundRuleInstVProof using (codeFormulaPairShape)

----------------------------------------------------------------------
-- Convenience.

private
  varCode1T : Term
  varCode1T = reify (code (var (suc zero)))

----------------------------------------------------------------------
-- The Th14Step4 module proper, parametric in r12_th, r12_sub (so that
-- it can refer to  K_part  defined in  Thm14Constr5Final ).

module Th14Step4
  (r12_th  : Thm12_F1_Result thmT)
  (r12_sub : Thm12_F2_Result sub)
  where

  open Th14Constr5Final r12_th r12_sub using (K_part)

  --------------------------------------------------------------------
  -- K_part_unfold : ap1 K_part x = Pair tagCode_ruleInst
  --                                  (Pair (Pair varCode1T (cor x)) x)
  --
  -- Bridge: K_part is a 4-deep Comp2 Pair tower; reduces by axComp2
  -- + ktRed + axI to the explicit ruleInst-payload Pair shape that
  -- thmTSubLemma consumes.

  K_part_unfold : (x : Term) ->
    Deriv (atomic (eqn (ap1 K_part x)
                       (ap2 Pair tagCode_ruleInst
                          (ap2 Pair (ap2 Pair varCode1T (ap1 cor x)) x))))
  K_part_unfold x =
    let
        -- Inner Comp2 Pair (KT varCode1T) cor : applied to x, gives
        --   Pair varCode1T (cor x).
        inner1 : Fun1
        inner1 = Comp2 Pair (KT varCode1T) cor

        inner1_step : Deriv (atomic (eqn (ap1 inner1 x)
                                          (ap2 Pair (ap1 (KT varCode1T) x)
                                                    (ap1 cor x))))
        inner1_step = axComp2 Pair (KT varCode1T) cor x

        kt_v1 : Deriv (atomic (eqn (ap1 (KT varCode1T) x) varCode1T))
        kt_v1 = ktRed (code (var (suc zero))) x

        inner1_simp : Deriv (atomic (eqn (ap1 inner1 x)
                                          (ap2 Pair varCode1T (ap1 cor x))))
        inner1_simp =
          ruleTrans inner1_step (congL Pair (ap1 cor x) kt_v1)

        -- Middle Comp2 Pair inner1 I : applied to x gives Pair (inner1 x) (I x).
        middle : Fun1
        middle = Comp2 Pair inner1 I

        middle_step : Deriv (atomic (eqn (ap1 middle x)
                                          (ap2 Pair (ap1 inner1 x) (ap1 I x))))
        middle_step = axComp2 Pair inner1 I x

        i_x : Deriv (atomic (eqn (ap1 I x) x))
        i_x = axI x

        middle_simp1 : Deriv (atomic (eqn (ap1 middle x)
                                          (ap2 Pair (ap1 inner1 x) x)))
        middle_simp1 = ruleTrans middle_step (congR Pair (ap1 inner1 x) i_x)

        middle_simp : Deriv (atomic (eqn (ap1 middle x)
                                          (ap2 Pair (ap2 Pair varCode1T (ap1 cor x))
                                                    x)))
        middle_simp = ruleTrans middle_simp1 (congL Pair x inner1_simp)

        -- Outer Comp2 Pair (KT tagCode_ruleInst) middle : applied to x gives
        --   Pair tagCode_ruleInst (middle x).
        outer_step : Deriv (atomic (eqn (ap1 K_part x)
                                         (ap2 Pair (ap1 (KT tagCode_ruleInst) x)
                                                   (ap1 middle x))))
        outer_step = axComp2 Pair (KT tagCode_ruleInst) middle x

        kt_tag : Deriv (atomic (eqn (ap1 (KT tagCode_ruleInst) x) tagCode_ruleInst))
        kt_tag = ktRed (natCode tagRuleInst) x

        outer_simp1 : Deriv (atomic (eqn (ap1 K_part x)
                                          (ap2 Pair tagCode_ruleInst
                                                    (ap1 middle x))))
        outer_simp1 = ruleTrans outer_step (congL Pair (ap1 middle x) kt_tag)
    in
        ruleTrans outer_simp1 (congR Pair tagCode_ruleInst middle_simp)

  --------------------------------------------------------------------
  -- step4_l : Phase C step 4 in internal-implication form.
  --
  -- Built by lifting thmTSubLemma at proof-index x:
  --   * Closed dispatch (no hypothesis):
  --       thmT (Pair tagCode_ruleInst (Pair (Pair varCode1T (cor x)) x))
  --         = subT (Pair varCode1T (cor x)) (thmT x)
  --   * Hypothesis use:
  --       subT (Pair varCode1T (cor x)) (thmT x)
  --         = subT (Pair varCode1T (cor x)) cG
  --     via congR subT applied to the hypothesis (thmT x = cG).
  --
  -- Lifted versions of both threaded under  PrAtX x  via  liftAxiom +
  -- liftedCongR + liftedRuleTrans.
  --
  -- Then bridge the LHS  thmT (encoded form)  to  thmT (ap1 K_part x)
  -- via cong1 thmT applied to the K_part_unfold equation (lifted).

  step4_l : (x : Term) ->
    Deriv (PrAtX x imp
            atomic (eqn (ap1 thmT (ap1 K_part x))
                        (ap2 subT (ap2 Pair varCode1T (ap1 cor x)) cG)))
  step4_l x =
    let
        P : Formula
        P = PrAtX x

        -- Encoded payload (the "argument" to thmT in thmTSubLemma's output).
        encodedT : Term
        encodedT = ap2 Pair tagCode_ruleInst
                     (ap2 Pair (ap2 Pair varCode1T (ap1 cor x)) x)

        -- The hypothesis IS  P  itself, so axImpRefl P  gives us the
        -- eqn-form  P imp (eqn (thmT x) cG)  used to drive both the
        -- inner-check Pair-shape witness AND the post-dispatch rewrite.
        sb_axImpRefl : Deriv (P imp atomic (eqn (ap1 thmT x) cG))
        sb_axImpRefl =
          mp (mp (axS P (P imp P) P)
                 (axK P (P imp P)))
             (axK P P)

        -- Pair-shape of cG = reify(codeFormula G) via codeFormulaPairShape.
        shapeG = codeFormulaPairShape G
        fp : Term
        fp = fst shapeG
        sp : Term
        sp = fst (snd shapeG)
        cGPairEq : Deriv (atomic (eqn cG (ap2 Pair fp sp)))
        cGPairEq = snd (snd shapeG)

        -- Lifted Pair-shape inner-check witness:
        --   P imp (thmT x = Pair fp sp), via sb_axImpRefl + cGPairEq.
        innerL : Deriv (P imp atomic (eqn (ap1 thmT x) (ap2 Pair fp sp)))
        innerL = liftedRuleTrans P (ap1 thmT x) cG (ap2 Pair fp sp)
                   sb_axImpRefl (liftAxiom P cGPairEq)

        -- Step (a): the LIFTED dispatch using the verifying body's
        -- inner check.  Replaces the closed thmTDispRuleInst_param +
        -- liftAxiom combo with the soundified lifted dispatcher.
        sa_lifted :
          Deriv (P imp atomic (eqn (ap1 thmT encodedT)
                                    (ap2 subT (ap2 Pair varCode1T (ap1 cor x))
                                              (ap1 thmT x))))
        sa_lifted =
          thmTDispRuleInst_param_l P (suc zero) (ap1 cor x) x fp sp innerL

        sb_lifted :
          Deriv (P imp atomic (eqn
                                 (ap2 subT (ap2 Pair varCode1T (ap1 cor x))
                                            (ap1 thmT x))
                                 (ap2 subT (ap2 Pair varCode1T (ap1 cor x))
                                            cG)))
        sb_lifted = liftedCongR P subT (ap1 thmT x) cG
                       (ap2 Pair varCode1T (ap1 cor x))
                       sb_axImpRefl

        -- Compose (a) + (b): thmT encodedT = subT (...) cG, lifted under P.
        sab :
          Deriv (P imp atomic (eqn (ap1 thmT encodedT)
                                    (ap2 subT (ap2 Pair varCode1T (ap1 cor x))
                                              cG)))
        sab = liftedRuleTrans P
                (ap1 thmT encodedT)
                (ap2 subT (ap2 Pair varCode1T (ap1 cor x)) (ap1 thmT x))
                (ap2 subT (ap2 Pair varCode1T (ap1 cor x)) cG)
                sa_lifted sb_lifted

        -- Step (c): bridge  thmT (ap1 K_part x) = thmT encodedT  (lifted).
        sc_closed : Deriv (atomic (eqn (ap1 thmT (ap1 K_part x))
                                        (ap1 thmT encodedT)))
        sc_closed = cong1 thmT (K_part_unfold x)

        sc_lifted :
          Deriv (P imp atomic (eqn (ap1 thmT (ap1 K_part x))
                                    (ap1 thmT encodedT)))
        sc_lifted = liftAxiom P sc_closed

    in liftedRuleTrans P
         (ap1 thmT (ap1 K_part x))
         (ap1 thmT encodedT)
         (ap2 subT (ap2 Pair varCode1T (ap1 cor x)) cG)
         sc_lifted sab
