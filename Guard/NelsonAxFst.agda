{-# OPTIONS --safe --without-K --exact-split #-}

-- Nelson base case: axFst (tag 1).
-- Encoding: nd(natCode 1)(nd aC bC) = Pair(tag1T, Pair(aC, bC))
-- Result: Pair(mkAp1(codeFst, mkAp2(codePair, aC, bC)), aC)
-- case1 = mkEqF (mkAp1F (kF2 codeFstF) (mkAp2F (kF2 pairCF) origA origB)) origA

module Guard.NelsonAxFst where

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
  tag1T : Term ; tag1T = reify (natCode n1)
  codeFstF : Term ; codeFstF = reify (codeF1 Fst)
  pairCF : Term ; pairCF = reify (codeF2 Pair)

nelsonAxFst : (aC bC : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair tag1T (ap2 Pair aC bC)))
                 (ap2 Pair (ap2 Pair (reify tagAp1) (ap2 Pair codeFstF
                              (ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair aC bC)))))
                           aC))
nelsonAxFst aC bC =
  let origT = ap2 Pair tag1T (ap2 Pair aC bC)
      recsT = ap2 Pair (ap1 thFunTFor tag1T) (ap1 thFunTFor (ap2 Pair aC bC))

      -- Phase 1+2: thFunTFor(origT) = case1(origT, recsT)
      step12 = ruleTrans (phase1Nd tag1T aC bC)
                         (ndDispatchToCase1 (ap2 Pair aC bC) recsT)

      -- Extractor reductions
      oaR = origARed tag1T aC bC recsT
      obR = origBRed tag1T aC bC recsT
      kFstR : {h : Equation} -> Deriv h (eqn (ap2 (kF2 codeFstF) origT recsT) codeFstF)
      kFstR = constF2Red codeFstF origT recsT
      kPairR : {h : Equation} -> Deriv h (eqn (ap2 (kF2 pairCF) origT recsT) pairCF)
      kPairR = constF2Red pairCF origT recsT

      -- mkAp2F (kF2 pairCF) origA origB -> Pair(tagAp2T, Pair(pairCF, Pair(aC, bC)))
      ap2R = mkAp2FRed (kF2 pairCF) origA origB origT recsT pairCF aC bC kPairR oaR obR

      -- mkAp1F (kF2 codeFstF) (mkAp2F ...) -> Pair(tagAp1T, Pair(codeFstF, mkAp2Result))
      leftRed = mkAp1FRed (kF2 codeFstF) (mkAp2F (kF2 pairCF) origA origB) origT recsT
                  codeFstF (ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair aC bC)))
                  kFstR ap2R

      -- case1 = mkEqF (mkAp1F ...) origA
      step4 = mkEqFRed (mkAp1F (kF2 codeFstF) (mkAp2F (kF2 pairCF) origA origB)) origA
                origT recsT
                (ap2 Pair (reify tagAp1) (ap2 Pair codeFstF
                  (ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair aC bC)))))
                aC
                leftRed oaR
  in
  ruleTrans step12 step4
