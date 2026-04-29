{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm14Step4Test
--
-- Parametric thmT-subRule equation needed by step 4 of Theorem 14.
--
-- RESULT (verified): the body_ruleInst computation IS parametric.  No
-- new axiom needed.  The proof requires an xShape parameter (a Deriv
-- that Fst x is Pair-shaped) — same pattern as Comp2.agda's Df_shape.
--
-- Components verified to typecheck:
--   * step4_body x bb distH
--       body_ruleInst's evaluation parametric in x, given distH.
--   * distHDerivation x xShape
--       distH derived parametrically given xShape (Fst-shape on x).
--   * step4_body_full x xShape
--       Composition: full body_ruleInst output up to subT form.
--
-- Remaining (dispatch chain): straightforward; lives in ThmT.agda's
-- abstract block (since it uses thmTDispRuleInst's structure).  Same
-- 37-skip-1-hit chain as the closed form, mechanical to port.
--
-- Conclusion: step 4 of Theorem 14 is finishable without adding
-- axThmTSubRule.  The xShape parameter is exactly the same pattern
-- used in Comp2.agda for Df_shape, and Theorem 14's closure can
-- supply it from constr5's structure (constr5 must output Pair-shape).

module BRA.Thm14Step4Test where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor using (cor)
open import BRA.Sb using (sb ; repackageSb ; rightSb ; repackageSbAt ; rightSbAt)
open import BRA.Thm.Tag
open import BRA.SubT using (subT)
open import BRA.Thm.ThmT
  using ( thmT ; tagCode_ruleInst
        ; thmTDispRuleInst
        ; thmTDistrib_param
        ; body_ruleInst ; body_ruleInst_eval_param
        ; fstReifyCodeVar )

------------------------------------------------------------------------
-- Constants.

varCode1T : Term
varCode1T = reify (code (var (suc zero)))   -- = Pair tagVarT (reify (natCode 1))

subProofEnc : Term -> Term
subProofEnc x = ap2 Pair tagCode_ruleInst
                  (ap2 Pair varCode1T
                    (ap2 Pair x (ap1 cor x)))

------------------------------------------------------------------------
-- The body_ruleInst evaluation, parametric in x.  Uses
-- body_ruleInst_eval_param + closed-form distH derivation up to where
-- distrib2 (the OPEN-xT thmTDistrib step) is needed.

step4_body :
  (x : Term)
  (bb : Term)
  (distH : Deriv (atomic (eqn (ap1 Snd bb)
                              (ap2 Pair (ap1 thmT varCode1T)
                                        (ap2 Pair (ap1 thmT x)
                                                  (ap1 thmT (ap1 cor x))))))) ->
  Deriv (atomic (eqn
    (ap2 body_ruleInst
          (ap2 Pair tagCode_ruleInst
                (ap2 Pair varCode1T (ap2 Pair x (ap1 cor x))))
          bb)
    (ap2 subT (ap2 Pair varCode1T (ap1 cor x)) (ap1 thmT x))))
step4_body x bb distH =
  body_ruleInst_eval_param (suc zero) (ap1 cor x) x bb (ap1 thmT x)
                            distH (axRefl (ap1 thmT x))

------------------------------------------------------------------------
-- Now the question: can we DERIVE distH parametrically?
--
-- distH requires:
--   Snd bb = Pair (thmT varCode1T) (Pair (thmT x) (thmT (cor x)))
--
-- For bb = Pair (thmT tagCode_ruleInst) (thmT payT), we have:
--   Snd bb = thmT payT       [by axSnd, parametric].
--
-- Need: thmT payT = Pair (thmT varCode1T) (Pair (thmT x) (thmT (cor x))).
--
-- payT = Pair varCode1T (Pair x (cor x)).
--
-- Step 1 (distrib1, OUTER): thmTDistrib_param at y1T = varCode1T.
--   Fst-shape: Fst varCode1T = reify tagVar = Pair (Pair O O) O.  ✓ closed.
--   Result: thmT payT = Pair (thmT varCode1T) (thmT (Pair x (cor x))).
--
-- Step 2 (distrib2, INNER): thmTDistrib_param at y1T = x.
--   Fst-shape needed: Fst x = Pair x' y'.
--   For OPEN x : Term: ap1 Fst x does NOT reduce. ✗
--   No Deriv inhabitant for arbitrary open x.

distHDerivation :
  (x : Term)
  -- Hypothetical shape-on-x parameter (would unblock distrib2):
  (xShape : Sigma Term (\ y' -> Sigma Term (\ x' ->
    Deriv (atomic (eqn (ap1 Fst x) (ap2 Pair x' y')))))) ->
  let bb : Term
      bb = ap2 Pair (ap1 thmT tagCode_ruleInst)
                    (ap1 thmT (ap2 Pair varCode1T (ap2 Pair x (ap1 cor x))))
  in Deriv (atomic (eqn (ap1 Snd bb)
                        (ap2 Pair (ap1 thmT varCode1T)
                                  (ap2 Pair (ap1 thmT x)
                                            (ap1 thmT (ap1 cor x))))))
distHDerivation x xShape =
  let payT : Term
      payT = ap2 Pair varCode1T (ap2 Pair x (ap1 cor x))
      bb : Term
      bb = ap2 Pair (ap1 thmT tagCode_ruleInst) (ap1 thmT payT)
      sndB_unfold = axSnd (ap1 thmT tagCode_ruleInst) (ap1 thmT payT)
      shapeV = fstReifyCodeVar (suc zero)
      -- distrib1 — closed shape on varCode1T.  Works.
      distrib1 = thmTDistrib_param varCode1T (ap2 Pair x (ap1 cor x))
                                   {x' = fst shapeV} (fst (snd shapeV))
                                   (snd (snd shapeV))
      -- distrib2 — needs OPEN shape on x.  Supplied via xShape parameter.
      distrib2 = thmTDistrib_param x (ap1 cor x)
                                   {x' = fst (snd xShape)} (fst xShape)
                                   (snd (snd xShape))
      distrib2_lifted = congR Pair (ap1 thmT varCode1T) distrib2
      distrib_full = ruleTrans distrib1 distrib2_lifted
  in ruleTrans sndB_unfold distrib_full

------------------------------------------------------------------------
-- Composed: body_ruleInst output, parametric in x with xShape param.
-- Uses step4_body + distHDerivation to discharge distH.

step4_body_full :
  (x : Term)
  (xShape : Sigma Term (\ y' -> Sigma Term (\ x' ->
    Deriv (atomic (eqn (ap1 Fst x) (ap2 Pair x' y')))))) ->
  let bb : Term
      bb = ap2 Pair (ap1 thmT tagCode_ruleInst)
                    (ap1 thmT (ap2 Pair varCode1T (ap2 Pair x (ap1 cor x))))
  in Deriv (atomic (eqn
       (ap2 body_ruleInst
             (ap2 Pair tagCode_ruleInst
                   (ap2 Pair varCode1T (ap2 Pair x (ap1 cor x))))
             bb)
       (ap2 subT (ap2 Pair varCode1T (ap1 cor x)) (ap1 thmT x))))
step4_body_full x xShape =
  step4_body x _ (distHDerivation x xShape)

