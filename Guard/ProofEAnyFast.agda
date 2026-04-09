{-# OPTIONS --safe --without-K --exact-split #-}

-- Fast variant of Guard.ProofEAny.
--
-- Provides:
--   * mkProofEAny — same as in Guard.ProofEAny (no dependency on the
--     slow Guard.SubstTForPrecomp).
--   * godelIToBotFast — strengthened Gödel I, restructured to use the
--     schematic Nelson helpers instead of instForm2.
--
-- The original Guard.ProofEAny is preserved.

module Guard.ProofEAnyFast where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.ThFun
open import Guard.ThFunCorrect
open import Guard.ThFunTFor
open import Guard.ThFunTForDefs
open import Guard.ThFunTForCases0
open import Guard.ThFunTForCases1
open import Guard.ThFunTForCases2
open import Guard.ThFunTForCases3
open import Guard.ThFunTForCorrectDefs
open import Guard.NdDispatchProofs
open import Guard.ExtractorRed
open import Guard.SubstCorrect
open import Guard.IntermediatePassthrough
open import Guard.PairPassthroughAll
open import Guard.SubstTFor using (substTFor)
open import Guard.SubstTForCorrect
open import Guard.Thm14E using (ProofE ; mkProofE ; thm14E ; thm14ERefl ; passthroughSuc)

------------------------------------------------------------------------
-- mkProofEAny: identical to Guard.ProofEAny.mkProofEAny.

private
  n17 : Nat ; n17 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))
  n18 : Nat ; n18 = suc n17
  n19 : Nat ; n19 = suc n18

mkProofEAny : (A B : Term) -> ProofE (eqn A B)
mkProofEAny A B =
  let pe1 = thm14ERefl A
      pe2 = thm14ERefl B
      pa1 = fst pe1
      pb1 = fst (snd pe1)
      thfPf1 = fst (snd (snd pe1))
      corrPf1 = fst (snd (snd (snd pe1)))
      passPf1 = snd (snd (snd (snd pe1)))
      pa2 = fst pe2
      pb2 = fst (snd pe2)
      thfPf2 = fst (snd (snd pe2))
      corrPf2 = fst (snd (snd (snd pe2)))
  in mkProofE {eqn A B} (natCode n19) (nd (nd pa1 pb1) (nd pa2 pb2))
       (eqCong2 (\eq1 eq2 -> nd (leftT eq1) (rightT eq2)) thfPf1 thfPf2)
       (correct pa1 pb1 pa2 pb2 corrPf1 corrPf2 passPf1)
       (\x' rc' -> passthroughSuc n18 (nd (nd pa1 pb1) (nd pa2 pb2)) x' rc')
  where
  aC : Term ; aC = reify (code A)
  bC : Term ; bC = reify (code B)

  correct : (pa1 pb1 pa2 pb2 : Tree) ->
    ({hyp : Equation} -> Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair (reify pa1) (reify pb1)))
                                        (reify (codeEqn (eqn A A))))) ->
    ({hyp : Equation} -> Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair (reify pa2) (reify pb2)))
                                        (reify (codeEqn (eqn B B))))) ->
    ((x' rcs : Term) -> {hyp : Equation} ->
      Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (ap2 Pair (reify pa1) (reify pb1)) x') rcs)
                     (ap2 sndArg2 (ap2 Pair (ap2 Pair (reify pa1) (reify pb1)) x') rcs))) ->
    ({hyp : Equation} -> Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair (reify (natCode n19))
                                              (ap2 Pair (ap2 Pair (reify pa1) (reify pb1))
                                                        (ap2 Pair (reify pa2) (reify pb2)))))
                                        (reify (codeEqn (eqn A B)))))
  correct pa1 pb1 pa2 pb2 corrPf1 corrPf2 passPf1 =
    let sp1R = ap2 Pair (reify pa1) (reify pb1)
        sp2R = ap2 Pair (reify pa2) (reify pb2)
        tagR = reify (natCode n19)
        dat = ap2 Pair sp1R sp2R
        orig = ap2 Pair tagR dat
        recs' = ap2 Pair (ap1 thFunTFor tagR) (ap2 Pair (ap2 Pair aC aC) (ap2 Pair bC bC))

        datExpand : {hyp : Equation} ->
          Deriv hyp (eqn (ap1 thFunTFor dat) (ap2 Pair (ap2 Pair aC aC) (ap2 Pair bC bC)))
        datExpand =
          ruleTrans (intermediateGeneric sp1R sp2R (reify pa2) (reify pb2) (\x' rc' -> passPf1 x' rc'))
          (ruleTrans (congL Pair (ap1 thFunTFor sp2R) corrPf1) (congR Pair (ap2 Pair aC aC) corrPf2))

        recsExpand : {hyp : Equation} -> Deriv hyp (eqn (ap2 Pair (ap1 thFunTFor tagR) (ap1 thFunTFor dat)) recs')
        recsExpand = congR Pair (ap1 thFunTFor tagR) datExpand
    in
    ruleTrans (recNdRed O thFunStep tagR dat)
    (ruleTrans (congR thFunStep orig recsExpand)
    (ruleTrans (guardNd tagR sp1R sp2R recs')
    (ruleTrans (ndDisp19 dat recs')
    (mkEqFRed recsAL recsBR orig recs' aC bC
      (recsALRed orig (ap1 thFunTFor tagR) aC aC (ap2 Pair bC bC))
      (recsBRRed orig (ap1 thFunTFor tagR) (ap2 Pair aC aC) bC bC)))))

------------------------------------------------------------------------
-- Strengthened Gödel I, FAST version.
-- Uses the Nelson schematic helpers instead of instForm2.

open import Guard.SubstTForPrecompFast
  using (godelSentence ; cGS ; cGSdef ; cstf ; cstfDef ;
         templateCode ; crTC ;
         substGodelSentence)
open import Guard.GodelIIFast using (treeEqSelf ; diagFTarget ; substCstf)
open import Guard.Nelson.SubstReify using (substReify)
open import Guard.Nelson.ThFunTForSubst using (thFunTForClosed ; thFunTForSubstEq)
open import Guard.Nelson.InstForm using (instFormGen)

private
  poo : Term ; poo = ap2 Pair O O
  v1' : Nat ; v1' = suc zero
  v11' : Nat ; v11' = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
  v12' : Nat ; v12' = suc v11'

-- Constructive form: if T proves G, then T proves 0 = 1.
godelIToBotFast : {hyp : Equation} ->
  Deriv hyp godelSentence -> Deriv hyp (eqn O poo)
godelIToBotFast {eqn l r} dG = ruleTrans (ruleSym selfEq) step2
  where
  hyp : Equation
  hyp = eqn l r

  ph : ProofE hyp
  ph = mkProofEAny l r

  pe : ProofE godelSentence
  pe = thm14E dG ph

  pa : Tree ; pa = fst pe
  pb : Tree ; pb = fst (snd pe)

  enc : Term
  enc = ap2 Pair (reify pa) (reify pb)

  corrPf : Deriv hyp (eqn (ap1 thFunTFor enc) (reify cGS))
  corrPf = eqSubst (\t -> Deriv hyp (eqn (ap1 thFunTFor enc) (reify t)))
                    (eqSym cGSdef)
                    (fst (snd (snd (snd pe))) {hyp})

  chain : Deriv hyp (eqn (ap1 thFunTFor enc) (ap1 cstf (reify templateCode)))
  chain = ruleTrans corrPf (ruleSym (diagFTarget {hyp}))

  instD : Deriv hyp (eqn (ap2 TreeEq (ap1 thFunTFor enc) (ap1 substTFor (reify templateCode))) poo)
  instD = eqSubst (\eq -> Deriv hyp eq) (substGodelSentence enc) (ruleInst zero enc dG)

  instD2pre : Deriv hyp (eqn (ap2 TreeEq (ap1 (thFunTForClosed crTC (natCode v1')) enc)
                                          (ap1 (closedSubstTFor (reify crTC) (reify (natCode v1'))) (reify templateCode)))
                              poo)
  instD2pre = eqSubst (\eq -> Deriv hyp eq)
                       (instFormGen crTC (natCode v1') pa pb templateCode)
                       (ruleInst v11' (reify crTC) (ruleInst v12' (reify (natCode v1')) instD))

  instD2 : Deriv hyp (eqn (ap2 TreeEq (ap1 (thFunTForClosed crTC (natCode v1')) enc)
                                       (ap1 cstf (reify templateCode)))
                           poo)
  instD2 = eqSubst (\f -> Deriv hyp (eqn (ap2 TreeEq (ap1 (thFunTForClosed crTC (natCode v1')) enc)
                                                      (ap1 f (reify templateCode)))
                                          poo))
                    (eqSym cstfDef) instD2pre

  chainBridge :
    Eq (substEq v11' (reify crTC) (substEq v12' (reify (natCode v1'))
         (eqn (ap1 thFunTFor enc) (ap1 cstf (reify templateCode)))))
       (eqn (ap1 (thFunTForClosed crTC (natCode v1')) enc) (ap1 cstf (reify templateCode)))
  chainBridge =
    eqCong2 eqn
      (eqCong2 ap1
        (thFunTForSubstEq crTC (natCode v1'))
        (eqTrans
          (eqCong (subst v11' (reify crTC))
            (eqCong2 (ap2 Pair)
              (substReify v12' (reify (natCode v1')) pa)
              (substReify v12' (reify (natCode v1')) pb)))
          (eqCong2 (ap2 Pair)
            (substReify v11' (reify crTC) pa)
            (substReify v11' (reify crTC) pb))))
      (eqCong2 ap1
        (eqTrans (eqCong (substF1 v11' (reify crTC)) (substCstf v12' (reify (natCode v1'))))
                 (substCstf v11' (reify crTC)))
        (eqTrans
          (eqCong (subst v11' (reify crTC)) (substReify v12' (reify (natCode v1')) templateCode))
          (substReify v11' (reify crTC) templateCode)))

  chainSubst : Deriv hyp (eqn (ap1 (thFunTForClosed crTC (natCode v1')) enc)
                              (ap1 cstf (reify templateCode)))
  chainSubst = eqSubst (\eq -> Deriv hyp eq) chainBridge
                       (ruleInst v11' (reify crTC) (ruleInst v12' (reify (natCode v1')) chain))

  step2 : Deriv hyp (eqn (ap2 TreeEq (ap1 cstf (reify templateCode)) (ap1 cstf (reify templateCode))) poo)
  step2 = ruleTrans (ruleSym (congL TreeEq (ap1 cstf (reify templateCode)) chainSubst)) instD2

  selfEq : Deriv hyp (eqn (ap2 TreeEq (ap1 cstf (reify templateCode)) (ap1 cstf (reify templateCode))) O)
  selfEq = treeEqSelf (ap1 cstf (reify templateCode))

-- Standard form: G is not derivable from a consistent hypothesis.
godelIFast : {hyp : Equation} -> Consistent hyp ->
             Deriv hyp godelSentence -> Empty
godelIFast con dG = con (godelIToBotFast dG)
