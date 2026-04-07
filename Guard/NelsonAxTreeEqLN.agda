{-# OPTIONS --safe --without-K --exact-split #-}

-- NelsonAxTreeEqLN.agda
-- Nelson base case: axTreeEqLN (tag 14).
-- Encoding: Pair(tag14T, Pair(aC, bC))
-- case14 = mkEqF (mkAp2F (kF2 treeeqCF) (kF2 oC) (mkAp2F (kF2 pairCF) origA origB)) (kF2 oneC)
-- Result: Pair(mkAp2(TreeEq, O, Pair(a,b)), Pair(O,O))
-- where oneC = mkAp2(Pair, O, O) as a coded term

module Guard.NelsonAxTreeEqLN where

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
  tag14T : Term ; tag14T = reify (natCode n14)
  oC : Term ; oC = ap2 Pair O O
  treeeqCF : Term ; treeeqCF = reify (codeF2 TreeEq)
  pairCF : Term ; pairCF = reify (codeF2 Pair)
  -- oneC = mkAp2(Pair, O, O) = Pair(tagAp2, Pair(pairCF, Pair(O,O)))
  reifyTagAp2 : Term ; reifyTagAp2 = ap2 Pair O (ap2 Pair O (ap2 Pair O O))
  oneC : Term ; oneC = ap2 Pair reifyTagAp2 (ap2 Pair pairCF (ap2 Pair oC oC))

nelsonAxTreeEqLN : (aC bC : Term) -> {hyp : Equation} ->
  let pairAB = ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair aC bC))
  in Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair tag14T (ap2 Pair aC bC)))
                    (ap2 Pair (ap2 Pair (reify tagAp2) (ap2 Pair treeeqCF (ap2 Pair oC pairAB)))
                              oneC))
nelsonAxTreeEqLN aC bC =
  let origT = ap2 Pair tag14T (ap2 Pair aC bC)
      recsT = ap2 Pair (ap1 thFunTFor tag14T) (ap1 thFunTFor (ap2 Pair aC bC))
      pairAB = ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair aC bC))

      step12 = ruleTrans (phase1Nd tag14T aC bC)
                         (ndDispatchToCase14 (ap2 Pair aC bC) recsT)

      oaR = origARed tag14T aC bC recsT
      obR = origBRed tag14T aC bC recsT

      kTrR : {h : Equation} -> Deriv h (eqn (ap2 (kF2 treeeqCF) origT recsT) treeeqCF)
      kTrR = constF2Red treeeqCF origT recsT
      kOR : {h : Equation} -> Deriv h (eqn (ap2 (kF2 oC) origT recsT) oC)
      kOR = constF2Red oC origT recsT
      kPairR : {h : Equation} -> Deriv h (eqn (ap2 (kF2 pairCF) origT recsT) pairCF)
      kPairR = constF2Red pairCF origT recsT
      kOneCR : {h : Equation} -> Deriv h (eqn (ap2 (kF2 oneC) origT recsT) oneC)
      kOneCR = constF2Red oneC origT recsT

      -- mkAp2F (kF2 pairCF) origA origB -> pairAB
      pairABR = mkAp2FRed (kF2 pairCF) origA origB origT recsT pairCF aC bC kPairR oaR obR

      -- LHS: mkAp2F (kF2 treeeqCF) (kF2 oC) (mkAp2F (kF2 pairCF) origA origB)
      leftRed = mkAp2FRed (kF2 treeeqCF) (kF2 oC) (mkAp2F (kF2 pairCF) origA origB)
                  origT recsT treeeqCF oC pairAB kTrR kOR pairABR

      step4 = mkEqFRed (mkAp2F (kF2 treeeqCF) (kF2 oC) (mkAp2F (kF2 pairCF) origA origB))
                        (kF2 oneC)
                origT recsT
                (ap2 Pair (reify tagAp2) (ap2 Pair treeeqCF (ap2 Pair oC pairAB)))
                oneC
                leftRed kOneCR
  in
  ruleTrans step12 step4
