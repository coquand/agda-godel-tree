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
open import Guard.ThFun using (codeEqn)
open import Guard.ThFunTForV3 using (thmT)
open import Guard.SubstTForPrecompV3
open import Guard.TreeEqSelf using (treeEqSelf)
open import Guard.Thm14EV3 using (ProofE3 ; thm14EV3 ; encT ; corr)
open import Guard.GodelIV3 using (godelIDerivV3)
open import Guard.Nelson.SubstReify using (substReify)

------------------------------------------------------------------------
-- Tree-level truth values and the ⊥ code.

trueT : Term
trueT = O

falseT : Term
falseT = ap2 Pair O O

codeBot : Tree
codeBot = codeEqn (eqn trueT falseT)

codeBotT : Term
codeBotT = reify codeBot

------------------------------------------------------------------------
-- Prov3 H eq: internal provability of  eq  under hypothesis code  H .

record Prov3 (H eq : Equation) : Set where
  constructor mkProv3
  field
    enc  : Term
    corr : {hyp : Equation} ->
           Deriv hyp (eqn (ap1 (thmT (reify (codeEqn H))) enc)
                          (reify (codeEqn eq)))
open Prov3 public

------------------------------------------------------------------------
-- Necessitation: wrap a ProofE3 witness as a Prov3.

necessitation : {H eq : Equation} -> ProofE3 H eq -> Prov3 H eq
necessitation pe = mkProv3 (encT pe) (corr pe)

------------------------------------------------------------------------
-- The V3 internal consistency statement, specialised to godelSentenceV3.
--
-- conSentenceV3 = "for all x, (thmT(reify cGSV3)(x), codeBot) ≠ equal"
-- i.e. no proof encoding x gives  thmT(reify cGSV3)(x) = codeBot.

conSentenceV3 : Equation
conSentenceV3 = eqn (ap2 TreeEq (ap1 (thmT (reify cGSV3)) (var zero)) codeBotT)
                    falseT

------------------------------------------------------------------------
-- Cantor diagonal: from  TreeEq(c,c) = falseT , derive  trueT = falseT .

diagContradict : {hyp : Equation} (c : Term) ->
  Deriv hyp (eqn (ap2 TreeEq c c) falseT) ->
  Deriv hyp (eqn trueT falseT)
diagContradict c d = ruleTrans (ruleSym (treeEqSelf c)) d

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
-- Gödel II (constructive form): no consistent hypothesis proves its
-- own consistency.  Specialised here to  godelSentenceV3 .

godelIIV3 : Consistent godelSentenceV3 ->
  Deriv godelSentenceV3 conSentenceV3 ->
  Empty
godelIIV3 con dCon = con (conToBotV3 dCon)
