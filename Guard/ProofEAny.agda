{-# OPTIONS --safe --without-K --exact-split #-}

-- ProofEAny: ProofE is constructible for any equation.
--
-- Key result: mkProofEAny constructs ProofE (eqn A B) for ANY terms A, B.
-- Uses the trans-from-two-refls technique (tag 19 with two tag-17 sub-encodings).
--
-- Corollary: godelI — strengthened Gödel I without ProofE hyp assumption.

module Guard.ProofEAny where

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
open import Guard.Thm14E using (ProofE ; mkProofE ; thm14E ; thm14ERefl ; passthroughSuc)

------------------------------------------------------------------------
-- mkProofEAny: construct ProofE for any equation.
--
-- Strategy: encode eqn A B as trans(refl(A), refl(B)).
-- Encoding tree: nd (natCode 19) (nd (nd pa1 pb1) (nd pa2 pb2))
-- where (pa1, pb1) comes from thm14ERefl A
-- and   (pa2, pb2) comes from thm14ERefl B.

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
-- Strengthened Gödel I: no ProofE hyp needed.

open import Guard.GodelII using (godelII)
open import Guard.SubstTForPrecomp using (godelSentence)

godelI : {hyp : Equation} -> Consistent hyp ->
         Deriv hyp godelSentence -> Empty
godelI {eqn l r} con dG = godelII (mkProofEAny l r) con dG
