{-# OPTIONS --safe --without-K --exact-split #-}

-- NelsonAxIfLfL.agda
-- Nelson base case: axIfLfL (tag 11).
-- Encoding: Pair(tag11T, Pair(aC, bC))
-- case11 = mkEqF (mkAp2F (kF2 iflfCF) (kF2 oC) (mkAp2F (kF2 pairCF) origA origB)) origA
-- Result: Pair(mkAp2(IfLf, O, mkAp2(Pair, a, b)), a)

module Guard.Nelson.NelsonAxIfLfL where

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
  tag11T : Term ; tag11T = reify (natCode n11)
  oC : Term ; oC = ap2 Pair O O
  iflfCF : Term ; iflfCF = reify (codeF2 IfLf)
  pairCF : Term ; pairCF = reify (codeF2 Pair)

nelsonAxIfLfL : (aC bC : Term) -> {hyp : Equation} ->
  let pairAB = ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair aC bC))
  in Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair tag11T (ap2 Pair aC bC)))
                    (ap2 Pair (ap2 Pair (reify tagAp2) (ap2 Pair iflfCF (ap2 Pair oC pairAB)))
                              aC))
nelsonAxIfLfL aC bC =
  let origT = ap2 Pair tag11T (ap2 Pair aC bC)
      recsT = ap2 Pair (ap1 thFunTFor tag11T) (ap1 thFunTFor (ap2 Pair aC bC))
      pairAB = ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair aC bC))

      step12 = ruleTrans (phase1Nd tag11T aC bC)
                         (ndDispatchToCase11 (ap2 Pair aC bC) recsT)

      oaR = origARed tag11T aC bC recsT
      obR = origBRed tag11T aC bC recsT

      kIfR : {h : Equation} -> Deriv h (eqn (ap2 (kF2 iflfCF) origT recsT) iflfCF)
      kIfR = constF2Red iflfCF origT recsT
      kOR : {h : Equation} -> Deriv h (eqn (ap2 (kF2 oC) origT recsT) oC)
      kOR = constF2Red oC origT recsT
      kPairR : {h : Equation} -> Deriv h (eqn (ap2 (kF2 pairCF) origT recsT) pairCF)
      kPairR = constF2Red pairCF origT recsT

      -- mkAp2F (kF2 pairCF) origA origB -> Pair(tagAp2T, Pair(pairCF, Pair(aC, bC)))
      innerPairR = mkAp2FRed (kF2 pairCF) origA origB origT recsT pairCF aC bC kPairR oaR obR

      -- mkAp2F (kF2 iflfCF) (kF2 oC) innerPair -> Pair(tagAp2T, Pair(iflfCF, Pair(oC, pairAB)))
      leftRed = mkAp2FRed (kF2 iflfCF) (kF2 oC) (mkAp2F (kF2 pairCF) origA origB)
                  origT recsT iflfCF oC pairAB kIfR kOR innerPairR

      step4 = mkEqFRed (mkAp2F (kF2 iflfCF) (kF2 oC) (mkAp2F (kF2 pairCF) origA origB)) origA
                origT recsT
                (ap2 Pair (reify tagAp2) (ap2 Pair iflfCF (ap2 Pair oC pairAB)))
                aC
                leftRed oaR
  in
  ruleTrans step12 step4
