{-# OPTIONS --safe --without-K --exact-split #-}

-- NelsonAxTreeEqNL.agda
-- Nelson base case: axTreeEqNL (tag 15).
-- Encoding: Pair(tag15T, Pair(aC, bC))
-- case15 = mkEqF (mkAp2F (kF2 treeeqCF) (mkAp2F (kF2 pairCF) origA origB) (kF2 oC)) (kF2 oneC)
-- Result: Pair(mkAp2(TreeEq, Pair(a,b), O), Pair(O,O))

module Guard.Nelson.NelsonAxTreeEqNL where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.ThFunTForDefs
open import Guard.ThFunTForCases2
open import Guard.ThFunTFor
open import Guard.Nelson.NelsonDispatch
open import Guard.Nelson.NelsonExtractors

private
  tag15T : Term ; tag15T = reify (natCode n15)
  oC : Term ; oC = ap2 Pair O O
  treeeqCF : Term ; treeeqCF = reify (codeF2 TreeEq)
  pairCF : Term ; pairCF = reify (codeF2 Pair)
  reifyTagAp2 : Term ; reifyTagAp2 = ap2 Pair O (ap2 Pair O (ap2 Pair O O))
  oneC : Term ; oneC = ap2 Pair reifyTagAp2 (ap2 Pair pairCF (ap2 Pair oC oC))

nelsonAxTreeEqNL : (aC bC : Term) -> {hyp : Equation} ->
  let pairAB = ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair aC bC))
  in Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair tag15T (ap2 Pair aC bC)))
                    (ap2 Pair (ap2 Pair (reify tagAp2) (ap2 Pair treeeqCF (ap2 Pair pairAB oC)))
                              oneC))
nelsonAxTreeEqNL aC bC =
  let origT = ap2 Pair tag15T (ap2 Pair aC bC)
      recsT = ap2 Pair (ap1 thFunTFor tag15T) (ap1 thFunTFor (ap2 Pair aC bC))
      pairAB = ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair aC bC))

      step12 = ruleTrans (phase1Nd tag15T aC bC)
                         (ndDispatchToCase15 (ap2 Pair aC bC) recsT)

      oaR = origARed tag15T aC bC recsT
      obR = origBRed tag15T aC bC recsT

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

      -- LHS: mkAp2F (kF2 treeeqCF) (mkAp2F (kF2 pairCF) origA origB) (kF2 oC)
      leftRed = mkAp2FRed (kF2 treeeqCF) (mkAp2F (kF2 pairCF) origA origB) (kF2 oC)
                  origT recsT treeeqCF pairAB oC kTrR pairABR kOR

      step4 = mkEqFRed (mkAp2F (kF2 treeeqCF) (mkAp2F (kF2 pairCF) origA origB) (kF2 oC))
                        (kF2 oneC)
                origT recsT
                (ap2 Pair (reify tagAp2) (ap2 Pair treeeqCF (ap2 Pair pairAB oC)))
                oneC
                leftRed kOneCR
  in
  ruleTrans step12 step4
