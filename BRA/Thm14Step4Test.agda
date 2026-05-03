{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm14Step4Test
--
-- Parametric thmT-subRule equation for step 4 of Theorem 14, in the
-- post-2026-05-02 encoding (proof-index at outer Snd).  No xShape
-- obligation: the only distribution thmT must do walks past the closed
-- (varCode, tCode) Pair.
--
-- This file demonstrates the SHAPE-FREE form of body_ruleInst's
-- parametric evaluation now that  encRuleInst  has been reordered.
-- Compare with the historical comments in
-- BRA/NEXT-SESSION-THM14-PHASE-C.md (now obsolete).

module BRA.Thm14Step4Test where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor using (cor)
open import BRA.Thm.Tag
open import BRA.SubT using (subT)
open import BRA.Thm.ThmT
  using ( thmT ; tagCode_ruleInst
        ; thmTDispRuleInst_param )

------------------------------------------------------------------------
-- Constants.

varCode1T : Term
varCode1T = reify (code (var (suc zero)))

------------------------------------------------------------------------
-- The K_part-style parametric Definition 12 line 2.  Shape-free in x.
--
-- subProofEnc x = Pair tagCode_ruleInst (Pair (Pair varCode1T (cor x)) x)
--
-- (closed (varCode, cor x) at inner Fst, OPEN proof-index x at outer Snd).
--
-- Result: thmT (subProofEnc x) = subT (Pair varCode1T (cor x)) (thmT x).

step4_param :
  (x : Term) (fp sp : Term) ->
  -- Pair-shape witness for the verifying body's inner check.
  Deriv (atomic (eqn (ap1 thmT x) (ap2 Pair fp sp))) ->
  Deriv (atomic (eqn
    (ap1 thmT (ap2 Pair tagCode_ruleInst
                (ap2 Pair (ap2 Pair varCode1T (ap1 cor x)) x)))
    (ap2 subT (ap2 Pair varCode1T (ap1 cor x)) (ap1 thmT x))))
step4_param x fp sp dh =
  thmTDispRuleInst_param (suc zero) (ap1 cor x) x fp sp dh
