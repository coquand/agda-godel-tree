{-# OPTIONS --safe --without-K --exact-split #-}

-- NelsonAxPost.agda
-- Nelson base case: axPost (tag 7).
-- Encoding: Pair(tag7T, Pair(fC, Pair(hC, Pair(aC, bC))))
-- case7 = mkEqF (mkAp2F postCode origB2a origB2b) (mkAp1F origA (mkAp2F origB1 origB2a origB2b))
-- where postCode = Fan (kF2 codePostTag) (Fan origA origB1 Pair) Pair
-- Result: Pair(mkAp2(Post(f,h), a, b), mkAp1(f, mkAp2(h, a, b)))

module Guard.Nelson.NelsonAxPost where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.ThFunTForDefs
open import Guard.ThFunTForCases1
open import Guard.ThFunTFor
open import Guard.Nelson.NelsonDispatch
open import Guard.Nelson.NelsonExtractors

private
  tag7T : Term ; tag7T = reify (natCode n7)
  n26 : Nat ; n26 = suc n25
  n27 : Nat ; n27 = suc n26
  n28 : Nat ; n28 = suc n27
  n29 : Nat ; n29 = suc n28
  codePostTag : Term ; codePostTag = reify (natCode n29)

  -- Deep extractor reductions
  origB2aRed : (tagT x b1 b2a b2b recs : Term) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap2 origB2a (ap2 Pair tagT (ap2 Pair x (ap2 Pair b1 (ap2 Pair b2a b2b)))) recs) b2a)
  origB2aRed tagT x b1 b2a b2b recs =
    let origT = ap2 Pair tagT (ap2 Pair x (ap2 Pair b1 (ap2 Pair b2a b2b)))
    in ruleTrans (axPost Fst origB2 origT recs)
       (ruleTrans (cong1 Fst (origB2Red tagT x b1 (ap2 Pair b2a b2b) recs))
                  (axFst b2a b2b))

  origB2bRed : (tagT x b1 b2a b2b recs : Term) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap2 origB2b (ap2 Pair tagT (ap2 Pair x (ap2 Pair b1 (ap2 Pair b2a b2b)))) recs) b2b)
  origB2bRed tagT x b1 b2a b2b recs =
    let origT = ap2 Pair tagT (ap2 Pair x (ap2 Pair b1 (ap2 Pair b2a b2b)))
    in ruleTrans (axPost Snd origB2 origT recs)
       (ruleTrans (cong1 Snd (origB2Red tagT x b1 (ap2 Pair b2a b2b) recs))
                  (axSnd b2a b2b))

nelsonAxPost : (fC hC aC bC : Term) -> {hyp : Equation} ->
  let postCode = ap2 Pair codePostTag (ap2 Pair fC hC)
      hOfAB = ap2 Pair (reify tagAp2) (ap2 Pair hC (ap2 Pair aC bC))
  in Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair tag7T (ap2 Pair fC (ap2 Pair hC (ap2 Pair aC bC)))))
                    (ap2 Pair (ap2 Pair (reify tagAp2) (ap2 Pair postCode (ap2 Pair aC bC)))
                              (ap2 Pair (reify tagAp1) (ap2 Pair fC hOfAB))))
nelsonAxPost fC hC aC bC =
  let origT = ap2 Pair tag7T (ap2 Pair fC (ap2 Pair hC (ap2 Pair aC bC)))
      recsT = ap2 Pair (ap1 thFunTFor tag7T) (ap1 thFunTFor (ap2 Pair fC (ap2 Pair hC (ap2 Pair aC bC))))
      postCode = ap2 Pair codePostTag (ap2 Pair fC hC)
      hOfAB = ap2 Pair (reify tagAp2) (ap2 Pair hC (ap2 Pair aC bC))

      step12 = ruleTrans (phase1Nd tag7T fC (ap2 Pair hC (ap2 Pair aC bC)))
                         (ndDispatchToCase7 (ap2 Pair fC (ap2 Pair hC (ap2 Pair aC bC))) recsT)

      oaR = origARed tag7T fC (ap2 Pair hC (ap2 Pair aC bC)) recsT
      ob1R = origB1Red tag7T fC hC (ap2 Pair aC bC) recsT
      ob2aR = origB2aRed tag7T fC hC aC bC recsT
      ob2bR = origB2bRed tag7T fC hC aC bC recsT

      -- Post code: Fan (kF2 codePostTag) (Fan origA origB1 Pair) Pair
      -- Reduces to Pair(codePostTag, Pair(fC, hC))
      postCodeR : {h : Equation} -> Deriv h (eqn (ap2 (Fan (kF2 codePostTag) (Fan origA origB1 Pair) Pair) origT recsT) postCode)
      postCodeR = ruleTrans (axFan (kF2 codePostTag) (Fan origA origB1 Pair) Pair origT recsT)
                  (ruleTrans (congL Pair (ap2 (Fan origA origB1 Pair) origT recsT)
                                (constF2Red codePostTag origT recsT))
                  (congR Pair codePostTag
                    (ruleTrans (axFan origA origB1 Pair origT recsT)
                    (ruleTrans (congL Pair (ap2 origB1 origT recsT) oaR)
                               (congR Pair fC ob1R)))))

      -- LHS: mkAp2F postCode origB2a origB2b
      leftRed = mkAp2FRed (Fan (kF2 codePostTag) (Fan origA origB1 Pair) Pair) origB2a origB2b
                  origT recsT postCode aC bC postCodeR ob2aR ob2bR

      -- mkAp2F origB1 origB2a origB2b -> Pair(tagAp2T, Pair(hC, Pair(aC, bC))) = hOfAB
      hOfABR = mkAp2FRed origB1 origB2a origB2b origT recsT hC aC bC ob1R ob2aR ob2bR

      -- RHS: mkAp1F origA (mkAp2F origB1 origB2a origB2b)
      rightRed = mkAp1FRed origA (mkAp2F origB1 origB2a origB2b) origT recsT fC hOfAB oaR hOfABR

      step4 = mkEqFRed (mkAp2F (Fan (kF2 codePostTag) (Fan origA origB1 Pair) Pair) origB2a origB2b)
                        (mkAp1F origA (mkAp2F origB1 origB2a origB2b))
                origT recsT
                (ap2 Pair (reify tagAp2) (ap2 Pair postCode (ap2 Pair aC bC)))
                (ap2 Pair (reify tagAp1) (ap2 Pair fC hOfAB))
                leftRed rightRed
  in
  ruleTrans step12 step4
