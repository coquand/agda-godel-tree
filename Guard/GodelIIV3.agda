{-# OPTIONS --safe --without-K --exact-split #-}

-- V3 Gödel's Second Incompleteness Theorem.
--
-- From godelIDerivV3 (V3 Gödel I, proved genuine without mkProofEAny),
-- produce provBot : Prov3 gs (trueT = falseT) via necessitation.
-- Then conToBotV3 closes the diagonal: assuming gs proves its own
-- consistency (conSentenceV3), gs proves trueT = falseT.
-- godelIIV3 packages this as consistency-⇒-unprovability.

module Guard.GodelIIV3 where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.ThFunTForV3 using (thmT)
open import Guard.SubstTForPrecompV3
open import Guard.Thm14EV3 using (thm14EV3)
open import Guard.GodelIV3 using (godelIDerivV3)
open import Guard.Nelson.SubstReify using (substReify)
open import Guard.ProvV3

------------------------------------------------------------------------
-- The V3 internal consistency statement, specialised to godelSentenceV3.
--
-- conSentenceV3 = "for all x, (thmT(reify cGSV3)(x), codeBot) ≠ equal"
-- i.e. no proof encoding x gives  thmT(reify cGSV3)(x) = codeBot.

conSentenceV3 : Equation
conSentenceV3 = eqn (ap2 TreeEq (ap1 (thmT (reify cGSV3)) (var zero)) codeBotT)
                    falseT

------------------------------------------------------------------------
-- provBot: the V3 encoding of  godelSentenceV3 ⊢ trueT = falseT .

provBot : Prov3 godelSentenceV3 (eqn trueT falseT)
provBot = necessitation (thm14EV3 godelIDerivV3)

------------------------------------------------------------------------
-- conToBotV3: if godelSentenceV3 proves its own consistency, then it
-- proves  trueT = falseT  (equivalently, it's inconsistent).

conToBotV3 : {hyp : Equation} ->
  Deriv hyp conSentenceV3 ->
  Deriv hyp (eqn trueT falseT)
conToBotV3 {hyp} dCon = diagContradict codeBotT chainTop
  where
  -- Instantiate conSentenceV3 at  var 0  with  enc provBot .
  -- This gives TreeEq(thmT(reify cGSV3)(enc provBot), codeBotT) = falseT
  -- (modulo subst, which is identity on the closed reify terms).
  instD0 : Deriv hyp (substEq zero (enc provBot) conSentenceV3)
  instD0 = ruleInst zero (enc provBot) dCon

  -- substEq zero X conSentenceV3 reduces to the expected form via
  -- substReify on codeBot, codeEqn godelSentenceV3 (both closed).
  instForm : Eq (substEq zero (enc provBot) conSentenceV3)
               (eqn (ap2 TreeEq (ap1 (thmT (reify cGSV3)) (enc provBot))
                                codeBotT)
                    falseT)
  instForm =
    eqCong2 eqn
      (eqCong2 (ap2 TreeEq)
        (eqCong2 ap1
          (eqCong thmT (substReify zero (enc provBot) cGSV3))
          refl)
        (substReify zero (enc provBot) codeBot))
      refl

  instD : Deriv hyp (eqn (ap2 TreeEq (ap1 (thmT (reify cGSV3)) (enc provBot))
                                     codeBotT)
                         falseT)
  instD = eqSubst (\eq -> Deriv hyp eq) instForm instD0

  -- corr provBot : ap1 (thmT (reify (codeEqn godelSentenceV3))) (enc provBot)
  --             = reify (codeEqn (eqn trueT falseT)) = codeBotT.
  -- Bridge  codeEqn godelSentenceV3  with  cGSV3  via cGSdefV3.
  corrBot : Deriv hyp (eqn (ap1 (thmT (reify cGSV3)) (enc provBot)) codeBotT)
  corrBot = eqSubst
    (\c -> Deriv hyp (eqn (ap1 (thmT (reify c)) (enc provBot)) codeBotT))
    (eqSym cGSdefV3)
    (corr provBot)

  chainTop : Deriv hyp (eqn (ap2 TreeEq codeBotT codeBotT) falseT)
  chainTop = ruleTrans
    (ruleSym (congL TreeEq codeBotT corrBot)) instD

------------------------------------------------------------------------
-- Gödel II (positive / constructive form, specialised to godelSentenceV3):
--
--   if  godelSentenceV3  proves its own internal consistency statement,
--   then  godelSentenceV3  proves  trueT = falseT .

godelIIPositive :
  Deriv godelSentenceV3 conSentenceV3 ->
  Deriv godelSentenceV3 (eqn trueT falseT)
godelIIPositive dCon = conToBotV3 dCon

------------------------------------------------------------------------
-- Gödel II (negative / contrapositive form): no consistent hypothesis
-- proves its own consistency.  Specialised here to  godelSentenceV3 .

godelIIV3 : Consistent godelSentenceV3 ->
  Deriv godelSentenceV3 conSentenceV3 ->
  Empty
godelIIV3 con dCon = con (godelIIPositive dCon)

------------------------------------------------------------------------
-- Gödel II, sharpest formulation:  conSentenceV3  alone is
-- inconsistent.  From the internal consistency sentence as the only
-- ambient hypothesis, the base equational system derives  trueT = falseT .
--
-- This is the "positive" statement of Gödel II without any other
-- premise: the internal consistency statement is refutable by the
-- system, because the system has enough computational content to
-- exhibit a concrete proof-encoding  enc_⊥  with  thmT(⌜gs⌝)(enc_⊥) =
-- ⌜trueT = falseT⌝ , and  conSentenceV3  asserts no such witness exists.

godelIIConAlone : Deriv conSentenceV3 (eqn trueT falseT)
godelIIConAlone = conToBotV3 (ruleHyp {conSentenceV3})
