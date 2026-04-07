{-# OPTIONS --safe --without-K --exact-split #-}

-- NelsonAxFan.agda
-- Nelson base case: axFan (tag 8).
-- Encoding: Pair(tag8T, Pair(h1C, Pair(h2C, Pair(hC, Pair(aC, bC)))))
-- case8 = mkEqF (mkAp2F fanCode origB2b1 origB2b2)
--               (mkAp2F origB2a (mkAp2F origA origB2b1 origB2b2) (mkAp2F origB1 origB2b1 origB2b2))
-- where fanCode = Fan (kF2 codeFanTag) (Fan origA (Fan origB1 origB2a Pair) Pair) Pair
-- Result: Pair(mkAp2(Fan(h1,h2,h), a, b), mkAp2(h, mkAp2(h1,a,b), mkAp2(h2,a,b)))

module Guard.Nelson.NelsonAxFan where

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
  tag8T : Term ; tag8T = reify (natCode n8)
  n26 : Nat ; n26 = suc n25
  n27 : Nat ; n27 = suc n26
  n28 : Nat ; n28 = suc n27
  n29 : Nat ; n29 = suc n28
  n30 : Nat ; n30 = suc n29
  codeFanTag : Term ; codeFanTag = reify (natCode n30)

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

  -- Even deeper: origB2b1 = Post Fst origB2b, origB2b2 = Post Snd origB2b
  origB2b1' : Fun2 ; origB2b1' = Post Fst origB2b
  origB2b2' : Fun2 ; origB2b2' = Post Snd origB2b

  origB2b1Red : (tagT x b1 b2a b2b1 b2b2 recs : Term) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap2 origB2b1' (ap2 Pair tagT (ap2 Pair x (ap2 Pair b1 (ap2 Pair b2a (ap2 Pair b2b1 b2b2))))) recs) b2b1)
  origB2b1Red tagT x b1 b2a b2b1 b2b2 recs =
    let origT = ap2 Pair tagT (ap2 Pair x (ap2 Pair b1 (ap2 Pair b2a (ap2 Pair b2b1 b2b2))))
    in ruleTrans (axPost Fst origB2b origT recs)
       (ruleTrans (cong1 Fst (origB2bRed tagT x b1 b2a (ap2 Pair b2b1 b2b2) recs))
                  (axFst b2b1 b2b2))

  origB2b2Red : (tagT x b1 b2a b2b1 b2b2 recs : Term) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap2 origB2b2' (ap2 Pair tagT (ap2 Pair x (ap2 Pair b1 (ap2 Pair b2a (ap2 Pair b2b1 b2b2))))) recs) b2b2)
  origB2b2Red tagT x b1 b2a b2b1 b2b2 recs =
    let origT = ap2 Pair tagT (ap2 Pair x (ap2 Pair b1 (ap2 Pair b2a (ap2 Pair b2b1 b2b2))))
    in ruleTrans (axPost Snd origB2b origT recs)
       (ruleTrans (cong1 Snd (origB2bRed tagT x b1 b2a (ap2 Pair b2b1 b2b2) recs))
                  (axSnd b2b1 b2b2))

nelsonAxFan : (h1C h2C hC aC bC : Term) -> {hyp : Equation} ->
  let fanCode = ap2 Pair codeFanTag (ap2 Pair h1C (ap2 Pair h2C hC))
      h1AB = ap2 Pair (reify tagAp2) (ap2 Pair h1C (ap2 Pair aC bC))
      h2AB = ap2 Pair (reify tagAp2) (ap2 Pair h2C (ap2 Pair aC bC))
  in Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair tag8T (ap2 Pair h1C (ap2 Pair h2C (ap2 Pair hC (ap2 Pair aC bC))))))
                    (ap2 Pair (ap2 Pair (reify tagAp2) (ap2 Pair fanCode (ap2 Pair aC bC)))
                              (ap2 Pair (reify tagAp2) (ap2 Pair hC (ap2 Pair h1AB h2AB)))))
nelsonAxFan h1C h2C hC aC bC =
  let origT = ap2 Pair tag8T (ap2 Pair h1C (ap2 Pair h2C (ap2 Pair hC (ap2 Pair aC bC))))
      recsT = ap2 Pair (ap1 thFunTFor tag8T)
                        (ap1 thFunTFor (ap2 Pair h1C (ap2 Pair h2C (ap2 Pair hC (ap2 Pair aC bC)))))
      fanCode = ap2 Pair codeFanTag (ap2 Pair h1C (ap2 Pair h2C hC))
      h1AB = ap2 Pair (reify tagAp2) (ap2 Pair h1C (ap2 Pair aC bC))
      h2AB = ap2 Pair (reify tagAp2) (ap2 Pair h2C (ap2 Pair aC bC))

      step12 = ruleTrans (phase1Nd tag8T h1C (ap2 Pair h2C (ap2 Pair hC (ap2 Pair aC bC))))
                         (ndDispatchToCase8 (ap2 Pair h1C (ap2 Pair h2C (ap2 Pair hC (ap2 Pair aC bC)))) recsT)

      oaR = origARed tag8T h1C (ap2 Pair h2C (ap2 Pair hC (ap2 Pair aC bC))) recsT
      ob1R = origB1Red tag8T h1C h2C (ap2 Pair hC (ap2 Pair aC bC)) recsT
      ob2aR = origB2aRed tag8T h1C h2C hC (ap2 Pair aC bC) recsT
      ob2b1R = origB2b1Red tag8T h1C h2C hC aC bC recsT
      ob2b2R = origB2b2Red tag8T h1C h2C hC aC bC recsT

      -- Fan code: Fan (kF2 codeFanTag) (Fan origA (Fan origB1 origB2a Pair) Pair) Pair
      -- Reduces to Pair(codeFanTag, Pair(h1C, Pair(h2C, hC)))
      innerH2HR : {h : Equation} -> Deriv h (eqn (ap2 (Fan origB1 origB2a Pair) origT recsT) (ap2 Pair h2C hC))
      innerH2HR = ruleTrans (axFan origB1 origB2a Pair origT recsT)
                  (ruleTrans (congL Pair (ap2 origB2a origT recsT) ob1R)
                             (congR Pair h2C ob2aR))

      fanCodeR : {h : Equation} -> Deriv h (eqn (ap2 (Fan (kF2 codeFanTag) (Fan origA (Fan origB1 origB2a Pair) Pair) Pair) origT recsT) fanCode)
      fanCodeR = ruleTrans (axFan (kF2 codeFanTag) (Fan origA (Fan origB1 origB2a Pair) Pair) Pair origT recsT)
                 (ruleTrans (congL Pair (ap2 (Fan origA (Fan origB1 origB2a Pair) Pair) origT recsT)
                               (constF2Red codeFanTag origT recsT))
                 (congR Pair codeFanTag
                   (ruleTrans (axFan origA (Fan origB1 origB2a Pair) Pair origT recsT)
                   (ruleTrans (congL Pair (ap2 (Fan origB1 origB2a Pair) origT recsT) oaR)
                              (congR Pair h1C innerH2HR)))))

      -- LHS: mkAp2F fanCode origB2b1 origB2b2
      leftRed = mkAp2FRed (Fan (kF2 codeFanTag) (Fan origA (Fan origB1 origB2a Pair) Pair) Pair)
                  origB2b1' origB2b2' origT recsT fanCode aC bC fanCodeR ob2b1R ob2b2R

      -- mkAp2F origA origB2b1 origB2b2 -> h1AB
      h1ABR = mkAp2FRed origA origB2b1' origB2b2' origT recsT h1C aC bC oaR ob2b1R ob2b2R

      -- mkAp2F origB1 origB2b1 origB2b2 -> h2AB
      h2ABR = mkAp2FRed origB1 origB2b1' origB2b2' origT recsT h2C aC bC ob1R ob2b1R ob2b2R

      -- RHS: mkAp2F origB2a (mkAp2F origA ...) (mkAp2F origB1 ...)
      rightRed = mkAp2FRed origB2a (mkAp2F origA origB2b1' origB2b2') (mkAp2F origB1 origB2b1' origB2b2')
                   origT recsT hC h1AB h2AB ob2aR h1ABR h2ABR

      step4 = mkEqFRed (mkAp2F (Fan (kF2 codeFanTag) (Fan origA (Fan origB1 origB2a Pair) Pair) Pair)
                                origB2b1' origB2b2')
                        (mkAp2F origB2a (mkAp2F origA origB2b1' origB2b2') (mkAp2F origB1 origB2b1' origB2b2'))
                origT recsT
                (ap2 Pair (reify tagAp2) (ap2 Pair fanCode (ap2 Pair aC bC)))
                (ap2 Pair (reify tagAp2) (ap2 Pair hC (ap2 Pair h1AB h2AB)))
                leftRed rightRed
  in
  ruleTrans step12 step4
