{-# OPTIONS --safe --without-K --exact-split #-}

-- Nelson base case: axConst (tag 3).
-- Encoding: nd(natCode 3)(nd aC bC) = Pair(tag3T, Pair(aC, bC))
-- Result: Pair(mkAp2(codeConst, aC, bC), aC)
-- case3 = mkEqF (mkAp2F (kF2 constCF) origA origB) origA

module Guard.NelsonAxConst where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.ThFunTForDefs
open import Guard.ThFunTForCases0
open import Guard.ThFunTFor
open import Guard.NelsonDispatch
open import Guard.NelsonExtractors

private
  tag3T : Term ; tag3T = reify (natCode n3)
  constCF : Term ; constCF = reify (codeF2 Const)

nelsonAxConst : (aC bC : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair tag3T (ap2 Pair aC bC)))
                 (ap2 Pair (ap2 Pair (reify tagAp2) (ap2 Pair constCF (ap2 Pair aC bC)))
                           aC))
nelsonAxConst aC bC =
  let origT = ap2 Pair tag3T (ap2 Pair aC bC)
      recsT = ap2 Pair (ap1 thFunTFor tag3T) (ap1 thFunTFor (ap2 Pair aC bC))

      -- Phase 1+2: thFunTFor(origT) = case3(origT, recsT)
      step12 = ruleTrans (phase1Nd tag3T aC bC)
                         (ndDispatchToCase3 (ap2 Pair aC bC) recsT)

      -- Extractor reductions
      oaR = origARed tag3T aC bC recsT
      obR = origBRed tag3T aC bC recsT
      kConstR : {h : Equation} -> Deriv h (eqn (ap2 (kF2 constCF) origT recsT) constCF)
      kConstR = constF2Red constCF origT recsT

      -- mkAp2F (kF2 constCF) origA origB -> Pair(tagAp2T, Pair(constCF, Pair(aC, bC)))
      leftRed = mkAp2FRed (kF2 constCF) origA origB origT recsT constCF aC bC kConstR oaR obR

      -- case3 = mkEqF (mkAp2F ...) origA
      step4 = mkEqFRed (mkAp2F (kF2 constCF) origA origB) origA
                origT recsT
                (ap2 Pair (reify tagAp2) (ap2 Pair constCF (ap2 Pair aC bC)))
                aC
                leftRed oaR
  in
  ruleTrans step12 step4
