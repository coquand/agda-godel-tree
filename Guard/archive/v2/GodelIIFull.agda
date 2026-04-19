{-# OPTIONS --safe --without-K --exact-split #-}

-- Gödel's Second Incompleteness Theorem.
--
-- conSentence: "for all x, TreeEq(thFunTFor(x), codeBotT) = falseT"
-- i.e., no proof tree encodes a derivation of trueT = falseT.
--
-- Proof:
-- 1. Pre-compute enc_bot from the Gödel I proof (with hyp = godelSentence).
--    This is the encoding of the derivation: godelSentence ⊢ trueT = falseT.
-- 2. corrBot: thFunTFor(enc_bot) = codeBotT — polymorphic, no hypothesis needed.
-- 3. From conSentence at enc_bot: TreeEq(thFunTFor(enc_bot), codeBotT) = falseT.
-- 4. Replace thFunTFor(enc_bot) with codeBotT: TreeEq(codeBotT, codeBotT) = falseT.
-- 5. treeEqSelf: TreeEq(codeBotT, codeBotT) = trueT.
-- 6. trueT = falseT. Contradiction with Consistent hyp.

module Guard.GodelIIFull where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.ThFun using (codeEqn)
open import Guard.ThFunTFor using (thFunTFor)
open import Guard.SubstTForPrecomp
  using (godelSentence ; cGS ; cGSdef ; cstf ;
         templateCode ; crTC ;
         substGodelSentence ; instForm2)
open import Guard.SubstTFor using (substTFor)
open import Guard.GodelII using (treeEqSelf ; diagFTarget)
open import Guard.Thm14E using (ProofE ; thm14E)
open import Guard.ProofEAny using (mkProofEAny)

------------------------------------------------------------------------
-- Tree-level truth values.

trueT : Term
trueT = O

falseT : Term
falseT = ap2 Pair O O

------------------------------------------------------------------------
-- The internal consistency statement.

codeBot : Tree
codeBot = codeEqn (eqn trueT falseT)

codeBotT : Term
codeBotT = reify codeBot

conSentence : Equation
conSentence = eqn (ap2 TreeEq (ap1 thFunTFor (var zero)) codeBotT) falseT

------------------------------------------------------------------------
-- Pre-computed encoding of the Gödel I derivation.
--
-- With hyp = godelSentence, ruleHyp gives Deriv godelSentence godelSentence.
-- The Gödel I argument produces Deriv godelSentence (eqn trueT falseT).
-- By Theorem 14, this has encoding enc_bot with:
--   thFunTFor(enc_bot) = codeBotT  (polymorphic in hyp — no hypothesis used)

private
  v1 : Nat ; v1 = suc zero
  v11 : Nat ; v11 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
  v12 : Nat ; v12 = suc v11
  tgtT : Term ; tgtT = reify (natCode v1)

  -- Helper: decompose any equation for mkProofEAny
  mkPH : (eq : Equation) -> ProofE eq
  mkPH (eqn l r) = mkProofEAny l r

  -- Gödel I derivation with hyp = godelSentence
  botDeriv0 : Deriv godelSentence (eqn trueT falseT)
  botDeriv0 =
    let hyp = godelSentence
        dG = ruleHyp {godelSentence}
        ph = mkPH godelSentence
        pe = thm14E dG ph
        enc = ap2 Pair (reify (fst pe)) (reify (fst (snd pe)))
        corrPf : Deriv hyp (eqn (ap1 thFunTFor enc) (reify cGS))
        corrPf = eqSubst (\t -> Deriv hyp (eqn (ap1 thFunTFor enc) (reify t)))
                          (eqSym cGSdef)
                          (fst (snd (snd (snd pe))) {hyp})
        chain = ruleTrans corrPf (ruleSym (diagFTarget {hyp}))
        instD = eqSubst (\eq -> Deriv hyp eq) (substGodelSentence enc) (ruleInst zero enc dG)
        step1 = ruleTrans (ruleSym (congL TreeEq (ap1 substTFor (reify templateCode)) chain)) instD
        step2 = eqSubst (\eq -> Deriv hyp eq) instForm2
                         (ruleInst v12 tgtT (ruleInst v11 (reify crTC) step1))
        selfEq = treeEqSelf (ap1 cstf (reify templateCode))
    in ruleTrans (ruleSym selfEq) step2

  -- Theorem 14 applied to botDeriv0
  peBot : ProofE (eqn trueT falseT)
  peBot = thm14E botDeriv0 (mkPH godelSentence)

  -- The encoding and its correctness (polymorphic — no hypothesis needed)
  enc_bot : Term
  enc_bot = ap2 Pair (reify (fst peBot)) (reify (fst (snd peBot)))

  corrBot : {hyp : Equation} -> Deriv hyp (eqn (ap1 thFunTFor enc_bot) codeBotT)
  corrBot = fst (snd (snd (snd peBot)))

------------------------------------------------------------------------
-- Gödel II (constructive form): if T proves Con, then T proves 0 = 1.
--
-- This is the direct constructive content: from a derivation of
-- conSentence, produce a derivation of trueT = falseT.
-- No consistency assumption needed. No Markov's principle.

conToBot : {hyp : Equation} ->
  Deriv hyp conSentence ->
  Deriv hyp (eqn trueT falseT)
conToBot {hyp} dCon =
  let -- Instantiate conSentence at enc_bot
      conInst = ruleInst zero enc_bot dCon
      -- Replace thFunTFor(enc_bot) with codeBotT using corrBot
      step = ruleTrans (ruleSym (congL TreeEq codeBotT (corrBot {hyp}))) conInst
      -- treeEqSelf gives trueT
      selfEq = treeEqSelf codeBotT
  in ruleTrans (ruleSym selfEq) step

------------------------------------------------------------------------
-- Gödel II (standard form): conSentence is not derivable from
-- a consistent hypothesis.

godelII : {hyp : Equation} ->
  Consistent hyp ->
  Deriv hyp conSentence ->
  Empty
godelII con dCon = con (conToBot dCon)
