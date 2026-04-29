{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.SubEnc
--
-- Parametric reduction of thmT applied to a sub-rule encoded proof
-- code.  Wraps thmTDispRuleInst_param (BRA/Thm/ThmT.agda) with the
-- bridge to sb's expanded form.
--
-- Output: the parametric defining equation of th's sub-rule clause,
-- Guard's Definition 12 line 2:
--
--   thmT (subProofEnc x) = sb (Pair (cor x) (reify (natCode 1))) (thmT x)
--
-- This is exactly the encoded equation needed for Theorem 14 step 4.
-- xShape parameter is supplied at the use site, derived from the
-- specific construction (e.g., constr5's Pair-shape output).

module BRA.SubEnc where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor using (cor)
open import BRA.Sb using (sb ; repackageSb ; rightSb
                       ; repackageSbAt ; rightSbAt)
open import BRA.SubT using (subT)
open import BRA.Thm.Tag
open import BRA.Thm.ThmT
  using (thmT ; tagCode_ruleInst ; thmTDispRuleInst_param)

------------------------------------------------------------------------
-- subProofEnc : Term -> Term
--
-- Encoded form of "applying the sub rule with var index 1 and term cor x
-- to proof code x".  Mirrors Guard's 4J(J(num x, 1), x) + 1 construction.

subProofEnc : Term -> Term
subProofEnc x = ap2 Pair tagCode_ruleInst
                  (ap2 Pair (reify (code (var (suc zero))))
                    (ap2 Pair x (ap1 cor x)))

------------------------------------------------------------------------
-- subEncAux : the subT-form output from thmTDispRuleInst_param,
-- before bridging to sb-form.

subEncAux : (x : Term)
  (xShape : Sigma Term (\ y' -> Sigma Term (\ x' ->
     Deriv (atomic (eqn (ap1 Fst x) (ap2 Pair x' y')))))) ->
  Deriv (atomic (eqn (ap1 thmT (subProofEnc x))
                     (ap2 subT (ap2 Pair (reify (code (var (suc zero))))
                                          (ap1 cor x))
                               (ap1 thmT x))))
subEncAux x xShape =
  thmTDispRuleInst_param (suc zero) (ap1 cor x) x xShape

------------------------------------------------------------------------
-- Bridge: sb's defining equation expansion at our specific args.
--
-- sb = Fan repackageSb rightSb subT
-- sb (Pair (cor x) (reify (natCode 1))) (thmT x)
--   = subT (repackageSb (...) (thmT x)) (rightSb (...) (thmT x))
--   = subT (Pair (Pair tagVarT (reify (natCode 1))) (cor x)) (thmT x)
--   = subT (Pair (reify (code (var 1))) (cor x)) (thmT x)
--
-- where (Pair tagVarT (reify (natCode 1))) = reify (code (var 1)) by
-- the definition of code on var.

sbExpand : (x : Term) ->
  Deriv (atomic (eqn
    (ap2 sb (ap2 Pair (ap1 cor x) (reify (natCode (suc zero))))
            (ap1 thmT x))
    (ap2 subT (ap2 Pair (reify (code (var (suc zero)))) (ap1 cor x))
              (ap1 thmT x))))
sbExpand x =
  let p : Term
      p = ap1 cor x
      q : Term
      q = reify (natCode (suc zero))
      arg1 : Term
      arg1 = ap2 Pair p q
      argB : Term
      argB = ap1 thmT x

      -- sb (Pair p q) argB = subT (repackageSb _ _) (rightSb _ _).
      e1 : Deriv (atomic (eqn (ap2 sb arg1 argB)
                              (ap2 subT (ap2 repackageSb arg1 argB)
                                         (ap2 rightSb arg1 argB))))
      e1 = axFan repackageSb rightSb subT arg1 argB

      -- repackageSb (Pair p q) argB = Pair (Pair tagVarT q) p.
      e2 : Deriv (atomic (eqn (ap2 repackageSb arg1 argB)
                              (ap2 Pair (ap2 Pair (reify tagVar) q) p)))
      e2 = repackageSbAt p q argB

      -- rightSb (Pair p q) argB = argB.
      e3 : Deriv (atomic (eqn (ap2 rightSb arg1 argB) argB))
      e3 = rightSbAt arg1 argB

      e4 : Deriv (atomic (eqn (ap2 subT (ap2 repackageSb arg1 argB)
                                         (ap2 rightSb arg1 argB))
                              (ap2 subT (ap2 Pair (ap2 Pair (reify tagVar) q) p)
                                         (ap2 rightSb arg1 argB))))
      e4 = congL subT (ap2 rightSb arg1 argB) e2

      e5 : Deriv (atomic (eqn (ap2 subT (ap2 Pair (ap2 Pair (reify tagVar) q) p)
                                         (ap2 rightSb arg1 argB))
                              (ap2 subT (ap2 Pair (ap2 Pair (reify tagVar) q) p)
                                         argB)))
      e5 = congR subT (ap2 Pair (ap2 Pair (reify tagVar) q) p) e3

  in ruleTrans e1 (ruleTrans e4 e5)

------------------------------------------------------------------------
-- Main result: the parametric thmT-subRule equation.
--
-- Guard's Definition 12 line 2 specialised to var-index 1, parametric
-- in the proof index x (with xShape supplied at use site).
--
-- This is the equation that step 4 of Theorem 14 needs.

subRuleReduction : (x : Term)
  (xShape : Sigma Term (\ y' -> Sigma Term (\ x' ->
     Deriv (atomic (eqn (ap1 Fst x) (ap2 Pair x' y')))))) ->
  Deriv (atomic (eqn (ap1 thmT (subProofEnc x))
                     (ap2 sb (ap2 Pair (ap1 cor x) (reify (natCode (suc zero))))
                              (ap1 thmT x))))
subRuleReduction x xShape =
  ruleTrans (subEncAux x xShape) (ruleSym (sbExpand x))
