{-# OPTIONS --safe --without-K --exact-split #-}

-- Test: can we prove Gödel II *without* Gödel I, using only
-- mkProofEAny trueT falseT as the witness?  If this file
-- typechecks, the current conSentence is refutable by pure
-- computation axioms and the role of Gödel I in the proof is
-- inessential.

module Guard.GodelIITest where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.ThFun using (codeEqn)
open import Guard.ThFunTFor using (thFunTFor)
open import Guard.GodelII using (treeEqSelf)
open import Guard.Thm14E using (ProofE)
open import Guard.ProofEAny using (mkProofEAny)

trueT : Term
trueT = O

falseT : Term
falseT = ap2 Pair O O

codeBot : Tree
codeBot = codeEqn (eqn trueT falseT)

codeBotT : Term
codeBotT = reify codeBot

conSentence : Equation
conSentence = eqn (ap2 TreeEq (ap1 thFunTFor (var zero)) codeBotT) falseT

-- Construct the witness directly, no Gödel I.
peSimple : ProofE (eqn trueT falseT)
peSimple = mkProofEAny trueT falseT

encS : Term
encS = ap2 Pair (reify (fst peSimple)) (reify (fst (snd peSimple)))

corrS : {hyp : Equation} ->
        Deriv hyp (eqn (ap1 thFunTFor encS) codeBotT)
corrS = fst (snd (snd (snd peSimple)))

-- Gödel II without Gödel I.
conToBotSimple : {hyp : Equation} ->
                 Deriv hyp conSentence ->
                 Deriv hyp (eqn trueT falseT)
conToBotSimple {hyp} dCon =
  let conInst = ruleInst zero encS dCon
      step   = ruleTrans (ruleSym (congL TreeEq codeBotT (corrS {hyp}))) conInst
      selfEq = treeEqSelf codeBotT
  in ruleTrans (ruleSym selfEq) step
