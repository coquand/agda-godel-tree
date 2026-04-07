{-# OPTIONS --safe --without-K --exact-split #-}

-- NelsonAxComp2.agda
-- Nelson base case: axComp2 (tag 5).
-- Encoding: Pair(tag5T, Pair(hC, Pair(fC, Pair(gC, tC))))
-- case5 = mkEqF (mkAp1F comp2Code origB2b) (mkAp2F origA (mkAp1F origB1 origB2b) (mkAp1F origB2a origB2b))
-- where comp2Code = Fan (kF2 codeComp2Tag) (Fan origA (Fan origB1 origB2a Pair) Pair) Pair
-- Result: Pair(mkAp1(Comp2(h,f,g), t), mkAp2(h, mkAp1(f,t), mkAp1(g,t)))

module Guard.Nelson.NelsonAxComp2 where

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
  tag5T : Term ; tag5T = reify (natCode n5)
  n26 : Nat ; n26 = suc n25
  n27 : Nat ; n27 = suc n26
  n28 : Nat ; n28 = suc n27
  n29 : Nat ; n29 = suc n28
  n30 : Nat ; n30 = suc n29
  codeComp2Tag : Term ; codeComp2Tag = reify (natCode n30)

  -- Deep extractor reductions (not in NelsonExtractors)
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

nelsonAxComp2 : (hC fC gC tC : Term) -> {hyp : Equation} ->
  let comp2Code = ap2 Pair codeComp2Tag (ap2 Pair hC (ap2 Pair fC gC))
      fOfT = ap2 Pair (reify tagAp1) (ap2 Pair fC tC)
      gOfT = ap2 Pair (reify tagAp1) (ap2 Pair gC tC)
  in Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair tag5T (ap2 Pair hC (ap2 Pair fC (ap2 Pair gC tC)))))
                    (ap2 Pair (ap2 Pair (reify tagAp1) (ap2 Pair comp2Code tC))
                              (ap2 Pair (reify tagAp2) (ap2 Pair hC (ap2 Pair fOfT gOfT)))))
nelsonAxComp2 hC fC gC tC =
  let origT = ap2 Pair tag5T (ap2 Pair hC (ap2 Pair fC (ap2 Pair gC tC)))
      recsT = ap2 Pair (ap1 thFunTFor tag5T) (ap1 thFunTFor (ap2 Pair hC (ap2 Pair fC (ap2 Pair gC tC))))
      comp2Code = ap2 Pair codeComp2Tag (ap2 Pair hC (ap2 Pair fC gC))
      fOfT = ap2 Pair (reify tagAp1) (ap2 Pair fC tC)
      gOfT = ap2 Pair (reify tagAp1) (ap2 Pair gC tC)

      step12 = ruleTrans (phase1Nd tag5T hC (ap2 Pair fC (ap2 Pair gC tC)))
                         (ndDispatchToCase5 (ap2 Pair hC (ap2 Pair fC (ap2 Pair gC tC))) recsT)

      oaR = origARed tag5T hC (ap2 Pair fC (ap2 Pair gC tC)) recsT
      ob1R = origB1Red tag5T hC fC (ap2 Pair gC tC) recsT
      ob2aR = origB2aRed tag5T hC fC gC tC recsT
      ob2bR = origB2bRed tag5T hC fC gC tC recsT

      -- Comp2 code: Fan (kF2 codeComp2Tag) (Fan origA (Fan origB1 origB2a Pair) Pair) Pair
      -- Reduces to Pair(codeComp2Tag, Pair(hC, Pair(fC, gC)))
      innerFGR : {h : Equation} -> Deriv h (eqn (ap2 (Fan origB1 origB2a Pair) origT recsT) (ap2 Pair fC gC))
      innerFGR = ruleTrans (axFan origB1 origB2a Pair origT recsT)
                 (ruleTrans (congL Pair (ap2 origB2a origT recsT) ob1R)
                            (congR Pair fC ob2aR))

      comp2CodeR : {h : Equation} -> Deriv h (eqn (ap2 (Fan (kF2 codeComp2Tag) (Fan origA (Fan origB1 origB2a Pair) Pair) Pair) origT recsT) comp2Code)
      comp2CodeR = ruleTrans (axFan (kF2 codeComp2Tag) (Fan origA (Fan origB1 origB2a Pair) Pair) Pair origT recsT)
                   (ruleTrans (congL Pair (ap2 (Fan origA (Fan origB1 origB2a Pair) Pair) origT recsT)
                                 (constF2Red codeComp2Tag origT recsT))
                   (congR Pair codeComp2Tag
                     (ruleTrans (axFan origA (Fan origB1 origB2a Pair) Pair origT recsT)
                     (ruleTrans (congL Pair (ap2 (Fan origB1 origB2a Pair) origT recsT) oaR)
                                (congR Pair hC innerFGR)))))

      -- LHS: mkAp1F comp2Code origB2b -> Pair(tagAp1T, Pair(comp2Code, tC))
      leftRed = mkAp1FRed (Fan (kF2 codeComp2Tag) (Fan origA (Fan origB1 origB2a Pair) Pair) Pair)
                  origB2b origT recsT comp2Code tC comp2CodeR ob2bR

      -- mkAp1F origB1 origB2b -> Pair(tagAp1T, Pair(fC, tC)) = fOfT
      fOfTR = mkAp1FRed origB1 origB2b origT recsT fC tC ob1R ob2bR

      -- mkAp1F origB2a origB2b -> Pair(tagAp1T, Pair(gC, tC)) = gOfT
      gOfTR = mkAp1FRed origB2a origB2b origT recsT gC tC ob2aR ob2bR

      -- RHS: mkAp2F origA (mkAp1F origB1 origB2b) (mkAp1F origB2a origB2b)
      rightRed = mkAp2FRed origA (mkAp1F origB1 origB2b) (mkAp1F origB2a origB2b)
                   origT recsT hC fOfT gOfT oaR fOfTR gOfTR

      step4 = mkEqFRed (mkAp1F (Fan (kF2 codeComp2Tag) (Fan origA (Fan origB1 origB2a Pair) Pair) Pair) origB2b)
                        (mkAp2F origA (mkAp1F origB1 origB2b) (mkAp1F origB2a origB2b))
                origT recsT
                (ap2 Pair (reify tagAp1) (ap2 Pair comp2Code tC))
                (ap2 Pair (reify tagAp2) (ap2 Pair hC (ap2 Pair fOfT gOfT)))
                leftRed rightRed
  in
  ruleTrans step12 step4
