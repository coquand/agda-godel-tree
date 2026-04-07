{-# OPTIONS --safe --without-K --exact-split #-}

-- Rose Theorem 18 (p.135): Gödel's Second Incompleteness Theorem.
--
-- Following Rose exactly. The proof has three layers:
--
-- Layer 1 (Theorem 16 for our f):
--   H1: for all y, thFunTFor(y) ≠ code([cGST = O])
--   H2: for all y, thFunTFor(y) ≠ code([cGST = thFunTFor(Pair(a,b))])
--   ⊢ TreeEq(cGST, thFunTFor(x)) = falseT  (= godelSentence)
--
-- Layer 2 (Rose part (i) and (ii)):
--   Derive H1 from conR alone.
--   Derive H2 from conR + "G is provable" (second premise of Thm 18).
--
-- Layer 3 (Assembly):
--   From conR + godelSentence, derive trueT = falseT.
--   This is Theorem 18 = Gödel I with Rose's consistency formulation.
--   Gödel II follows by Rose's meta-argument.

module Guard.Nelson.Thm18 where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.ThFun using (codeEqn)
open import Guard.ThFunTFor using (thFunTFor ; thFunStep)
open import Guard.SubstTForPrecomp
  using (godelSentence ; cGS ; cGSdef ; cGSisCS ; cstf ;
         templateCode ; crTC ;
         substGodelSentence ; instForm2 ;
         codeLhsT ; codePoo)
open import Guard.SubstTFor using (substTFor)
open import Guard.GodelII using (treeEqSelf ; diagFTarget)
open import Guard.Thm14E using (ProofE ; thm14E)
open import Guard.Nelson.ProofEAny using (mkProofEAny ; godelI)
open import Guard.Nelson.ComplementEqn using (eF ; eFRed ; conR ; trueT ; falseT)

private
  poo : Term ; poo = ap2 Pair O O
  v0 : Term ; v0 = var zero
  v1T : Term ; v1T = var (suc zero)
  v1 : Nat ; v1 = suc zero
  v11 : Nat ; v11 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
  v12 : Nat ; v12 = suc v11
  tgtT : Term ; tgtT = reify (natCode v1)

  -- cGST = reify cGS — the Gödel sentence code as a term
  cGST : Term
  cGST = reify cGS

------------------------------------------------------------------------
-- Layer 3: Theorem 18 = Gödel I with Rose's consistency.
-- From conR + godelSentence, derive trueT = falseT.
-- (= mkDoubleBot, using conR instead of weak conSentence)

thm18 : {hyp : Equation} ->
  Deriv hyp conR ->
  Deriv hyp godelSentence ->
  Deriv hyp (eqn trueT falseT)
thm18 {eqn l r} dConR dG =
  let hyp = eqn l r
      -- Gödel I: from dG, construct derivation of trueT = falseT
      ph = mkProofEAny l r
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
      botD : Deriv hyp (eqn trueT falseT)
      botD = ruleTrans (ruleSym selfEq) step2
      -- Encode botD via Theorem 14
      peBot = thm14E botD ph
      enc_bot = ap2 Pair (reify (fst peBot)) (reify (fst (snd peBot)))
      corrBot : Deriv hyp (eqn (ap1 thFunTFor enc_bot) (reify (codeEqn (eqn trueT falseT))))
      corrBot = fst (snd (snd (snd peBot))) {hyp}
      -- codeBotT = reify(codeEqn(eqn trueT falseT))
      codeBotT : Term
      codeBotT = reify (codeEqn (eqn trueT falseT))
      -- From conR at x = enc_bot, z = enc_complement:
      -- We need thFunTFor(enc_bot) ≠ eF(thFunTFor(z)) for some z.
      -- Actually, simpler: TreeEq(codeBotT, codeBotT) = trueT (treeEqSelf)
      -- and TreeEq(codeBotT, codeBotT) = falseT (from conR chain).
      -- Use conR: thFunTFor(enc_bot) = codeBotT, and we need contradiction.
      --
      -- Simplest: from botD we already have trueT = falseT.
  in botD

------------------------------------------------------------------------
-- Gödel II: conR is not derivable from a consistent hypothesis.
--
-- The gap: we need Deriv hyp conR → Deriv hyp godelSentence.
-- Once we have that, thm18 gives trueT = falseT.
--
-- Rose derives this using Theorem 16 (layers 1-2 above).
-- Theorem 16 for our specific f needs:
--   H1: from conR, no theorem proves cGST = thFunTFor(O)  [base]
--   H2: from conR + dG, no theorem proves cGST = thFunTFor(Pair(a,b))  [step]
-- H1 uses conR alone. H2 uses conR + the second premise.
--
-- Rose's meta-argument: if conR is a theorem, then by the Theorem 18
-- derivation (which constructs G via Theorem 16), G is also a theorem.
-- This contradicts godelI (= Gödel I).

godelII : {hyp : Equation} ->
  Consistent hyp ->
  Deriv hyp conR ->
  Empty
godelII {eqn l r} con dConR = con (thm18 dConR dG)
  where
  dG : Deriv (eqn l r) godelSentence
  dG = {!!}  -- THE GAP: derive godelSentence from conR
