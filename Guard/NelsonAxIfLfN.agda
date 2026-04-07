{-# OPTIONS --safe --without-K --exact-split #-}

-- NelsonAxIfLfN.agda
-- Nelson base case: axIfLfN (tag 12).
-- Encoding: Pair(tag12T, Pair(xC, Pair(yC, Pair(aC, bC))))
-- case12 = mkEqF (mkAp2F (kF2 iflfCF) (mkAp2F (kF2 pairCF) origA origB1)
--                        (mkAp2F (kF2 pairCF) origB2a origB2b))
--                origB2b
-- Result: Pair(mkAp2(IfLf, Pair(x,y), Pair(a,b)), b)

module Guard.NelsonAxIfLfN where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.ThFunTForDefs
open import Guard.ThFunTForCases2
open import Guard.ThFunTFor
open import Guard.NelsonDispatch
open import Guard.NelsonExtractors

private
  tag12T : Term ; tag12T = reify (natCode n12)
  iflfCF : Term ; iflfCF = reify (codeF2 IfLf)
  pairCF : Term ; pairCF = reify (codeF2 Pair)

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

nelsonAxIfLfN : (xC yC aC bC : Term) -> {hyp : Equation} ->
  let pairXY = ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair xC yC))
      pairAB = ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair aC bC))
  in Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair tag12T (ap2 Pair xC (ap2 Pair yC (ap2 Pair aC bC)))))
                    (ap2 Pair (ap2 Pair (reify tagAp2) (ap2 Pair iflfCF (ap2 Pair pairXY pairAB)))
                              bC))
nelsonAxIfLfN xC yC aC bC =
  let origT = ap2 Pair tag12T (ap2 Pair xC (ap2 Pair yC (ap2 Pair aC bC)))
      recsT = ap2 Pair (ap1 thFunTFor tag12T) (ap1 thFunTFor (ap2 Pair xC (ap2 Pair yC (ap2 Pair aC bC))))
      pairXY = ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair xC yC))
      pairAB = ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair aC bC))

      step12 = ruleTrans (phase1Nd tag12T xC (ap2 Pair yC (ap2 Pair aC bC)))
                         (ndDispatchToCase12 (ap2 Pair xC (ap2 Pair yC (ap2 Pair aC bC))) recsT)

      oaR = origARed tag12T xC (ap2 Pair yC (ap2 Pair aC bC)) recsT
      ob1R = origB1Red tag12T xC yC (ap2 Pair aC bC) recsT
      ob2aR = origB2aRed tag12T xC yC aC bC recsT
      ob2bR = origB2bRed tag12T xC yC aC bC recsT

      kIfR : {h : Equation} -> Deriv h (eqn (ap2 (kF2 iflfCF) origT recsT) iflfCF)
      kIfR = constF2Red iflfCF origT recsT
      kPairR : {h : Equation} -> Deriv h (eqn (ap2 (kF2 pairCF) origT recsT) pairCF)
      kPairR = constF2Red pairCF origT recsT

      -- mkAp2F (kF2 pairCF) origA origB1 -> pairXY
      pairXYR = mkAp2FRed (kF2 pairCF) origA origB1 origT recsT pairCF xC yC kPairR oaR ob1R

      -- mkAp2F (kF2 pairCF) origB2a origB2b -> pairAB
      pairABR = mkAp2FRed (kF2 pairCF) origB2a origB2b origT recsT pairCF aC bC kPairR ob2aR ob2bR

      -- LHS: mkAp2F (kF2 iflfCF) pairXYF pairABF
      leftRed = mkAp2FRed (kF2 iflfCF) (mkAp2F (kF2 pairCF) origA origB1)
                  (mkAp2F (kF2 pairCF) origB2a origB2b)
                  origT recsT iflfCF pairXY pairAB kIfR pairXYR pairABR

      step4 = mkEqFRed (mkAp2F (kF2 iflfCF) (mkAp2F (kF2 pairCF) origA origB1)
                                             (mkAp2F (kF2 pairCF) origB2a origB2b))
                        origB2b
                origT recsT
                (ap2 Pair (reify tagAp2) (ap2 Pair iflfCF (ap2 Pair pairXY pairAB)))
                bC
                leftRed ob2bR
  in
  ruleTrans step12 step4
