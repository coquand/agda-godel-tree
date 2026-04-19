{-# OPTIONS --safe --without-K --exact-split #-}

-- Fast variant of Guard.GodelIIFull.
--
-- Provides the same theorems (`conToBot`, `godelII`) as the original
-- Guard.GodelIIFull, but built on the *Fast* chain
-- (SubstTForPrecompFast / SubstTForPrecomp2Fast / GodelIIFast) which
-- avoids the 108-second `instForm2` computation.
--
-- The Gödel II proof itself is identical in structure: pre-compute
-- `enc_bot` from the Gödel I derivation under hypothesis G, exploit
-- the hypothesis-polymorphism of `corrBot`, instantiate `Con` at
-- `enc_bot`, contradict via `treeEqSelf`.

module Guard.GodelIIFullFast where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.SubstCorrect
open import Guard.SubstTFor using (substTFor)
open import Guard.SubstTForCorrect
open import Guard.ThFun using (codeEqn)
open import Guard.ThFunTFor using (thFunTFor)
open import Guard.SubstTForPrecompFast
  using (godelSentence ; cGS ; cGSdef ; cstf ; cstfDef ;
         templateCode ; crTC ;
         substGodelSentence)
open import Guard.GodelIIFast using (treeEqSelf ; diagFTarget ; substCstf)
open import Guard.Thm14E using (ProofE ; thm14E)
open import Guard.ProofEAnyFast using (mkProofEAny)
open import Guard.Nelson.SubstReify using (substReify)
open import Guard.Nelson.ThFunTForSubst using (thFunTForClosed ; thFunTForSubstEq)
open import Guard.Nelson.InstForm using (instFormGen)

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
-- Pre-computed encoding of the Gödel I derivation, via the FAST proof.

private
  v1 : Nat ; v1 = suc zero
  v11 : Nat ; v11 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
  v12 : Nat ; v12 = suc v11
  poo : Term ; poo = ap2 Pair O O

  -- Helper: decompose any equation for mkProofEAny
  mkPH : (eq : Equation) -> ProofE eq
  mkPH (eqn l r) = mkProofEAny l r

  -- Gödel I derivation under hypothesis = godelSentence, using the
  -- schematic Nelson approach instead of instForm2.  Inlined from
  -- the body of Guard.GodelIIFast.godelIIFast specialized to
  -- hyp = godelSentence and dG = ruleHyp.

  botDeriv0 : Deriv godelSentence (eqn trueT falseT)
  botDeriv0 = ruleTrans (ruleSym selfEq) step2
    where
    hyp : Equation
    hyp = godelSentence

    dG : Deriv hyp hyp
    dG = ruleHyp {hyp}

    pe : ProofE godelSentence
    pe = thm14E dG (mkPH godelSentence)

    pa : Tree ; pa = fst pe
    pb : Tree ; pb = fst (snd pe)

    enc : Term
    enc = ap2 Pair (reify pa) (reify pb)

    corrPf : Deriv hyp (eqn (ap1 thFunTFor enc) (reify cGS))
    corrPf = eqSubst (\t -> Deriv hyp (eqn (ap1 thFunTFor enc) (reify t)))
                      (eqSym cGSdef)
                      (fst (snd (snd (snd pe))) {hyp})

    chain : Deriv hyp (eqn (ap1 thFunTFor enc) (ap1 cstf (reify templateCode)))
    chain = ruleTrans corrPf (ruleSym diagFTarget)

    instD : Deriv hyp (eqn (ap2 TreeEq (ap1 thFunTFor enc) (ap1 substTFor (reify templateCode))) poo)
    instD = eqSubst (\eq -> Deriv hyp eq) (substGodelSentence enc) (ruleInst zero enc dG)

    instD2pre : Deriv hyp (eqn (ap2 TreeEq (ap1 (thFunTForClosed crTC (natCode v1)) enc)
                                            (ap1 (closedSubstTFor (reify crTC) (reify (natCode v1))) (reify templateCode)))
                                poo)
    instD2pre = eqSubst (\eq -> Deriv hyp eq)
                         (instFormGen crTC (natCode v1) pa pb templateCode)
                         (ruleInst v11 (reify crTC) (ruleInst v12 (reify (natCode v1)) instD))

    instD2 : Deriv hyp (eqn (ap2 TreeEq (ap1 (thFunTForClosed crTC (natCode v1)) enc)
                                         (ap1 cstf (reify templateCode)))
                             poo)
    instD2 = eqSubst (\f -> Deriv hyp (eqn (ap2 TreeEq (ap1 (thFunTForClosed crTC (natCode v1)) enc)
                                                        (ap1 f (reify templateCode)))
                                            poo))
                      (eqSym cstfDef) instD2pre

    chainBridge :
      Eq (substEq v11 (reify crTC) (substEq v12 (reify (natCode v1))
           (eqn (ap1 thFunTFor enc) (ap1 cstf (reify templateCode)))))
         (eqn (ap1 (thFunTForClosed crTC (natCode v1)) enc) (ap1 cstf (reify templateCode)))
    chainBridge =
      eqCong2 eqn
        (eqCong2 ap1
          (thFunTForSubstEq crTC (natCode v1))
          (eqTrans
            (eqCong (subst v11 (reify crTC))
              (eqCong2 (ap2 Pair)
                (substReify v12 (reify (natCode v1)) pa)
                (substReify v12 (reify (natCode v1)) pb)))
            (eqCong2 (ap2 Pair)
              (substReify v11 (reify crTC) pa)
              (substReify v11 (reify crTC) pb))))
        (eqCong2 ap1
          (eqTrans (eqCong (substF1 v11 (reify crTC)) (substCstf v12 (reify (natCode v1))))
                   (substCstf v11 (reify crTC)))
          (eqTrans
            (eqCong (subst v11 (reify crTC)) (substReify v12 (reify (natCode v1)) templateCode))
            (substReify v11 (reify crTC) templateCode)))

    chainSubst : Deriv hyp (eqn (ap1 (thFunTForClosed crTC (natCode v1)) enc)
                                (ap1 cstf (reify templateCode)))
    chainSubst = eqSubst (\eq -> Deriv hyp eq) chainBridge
                         (ruleInst v11 (reify crTC) (ruleInst v12 (reify (natCode v1)) chain))

    step2 : Deriv hyp (eqn (ap2 TreeEq (ap1 cstf (reify templateCode)) (ap1 cstf (reify templateCode))) poo)
    step2 = ruleTrans (ruleSym (congL TreeEq (ap1 cstf (reify templateCode)) chainSubst)) instD2

    selfEq : Deriv hyp (eqn (ap2 TreeEq (ap1 cstf (reify templateCode)) (ap1 cstf (reify templateCode))) O)
    selfEq = treeEqSelf (ap1 cstf (reify templateCode))

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

conToBot : {hyp : Equation} ->
  Deriv hyp conSentence ->
  Deriv hyp (eqn trueT falseT)
conToBot {hyp} dCon =
  let conInst = ruleInst zero enc_bot dCon
      step    = ruleTrans (ruleSym (congL TreeEq codeBotT (corrBot {hyp}))) conInst
      selfEq  = treeEqSelf codeBotT
  in ruleTrans (ruleSym selfEq) step

------------------------------------------------------------------------
-- Gödel II (standard form): conSentence is not derivable from
-- a consistent hypothesis.

godelII : {hyp : Equation} ->
  Consistent hyp ->
  Deriv hyp conSentence ->
  Empty
godelII con dCon = con (conToBot dCon)
