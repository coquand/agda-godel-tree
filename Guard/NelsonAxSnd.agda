{-# OPTIONS --safe --without-K --exact-split #-}

-- Nelson base case: axSnd (tag 2).
-- Encoding: nd(natCode 2)(nd aC bC) = Pair(tag2T, Pair(aC, bC))
-- Result: Pair(mkAp1(codeSnd, mkAp2(codePair, aC, bC)), bC)
-- case2 = mkEqF (mkAp1F (kF2 codeSndF) (mkAp2F (kF2 pairCF) origA origB)) origB

module Guard.NelsonAxSnd where

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
  tag2T : Term ; tag2T = reify (natCode n2)
  codeSndF : Term ; codeSndF = reify (codeF1 Snd)
  pairCF : Term ; pairCF = reify (codeF2 Pair)

nelsonAxSnd : (aC bC : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair tag2T (ap2 Pair aC bC)))
                 (ap2 Pair (ap2 Pair (reify tagAp1) (ap2 Pair codeSndF
                              (ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair aC bC)))))
                           bC))
nelsonAxSnd aC bC =
  let origT = ap2 Pair tag2T (ap2 Pair aC bC)
      recsT = ap2 Pair (ap1 thFunTFor tag2T) (ap1 thFunTFor (ap2 Pair aC bC))

      -- Phase 1+2: thFunTFor(origT) = case2(origT, recsT)
      step12 = ruleTrans (phase1Nd tag2T aC bC)
                         (ndDispatchToCase2 (ap2 Pair aC bC) recsT)

      -- Extractor reductions
      oaR = origARed tag2T aC bC recsT
      obR = origBRed tag2T aC bC recsT
      kSndR : {h : Equation} -> Deriv h (eqn (ap2 (kF2 codeSndF) origT recsT) codeSndF)
      kSndR = constF2Red codeSndF origT recsT
      kPairR : {h : Equation} -> Deriv h (eqn (ap2 (kF2 pairCF) origT recsT) pairCF)
      kPairR = constF2Red pairCF origT recsT

      -- mkAp2F (kF2 pairCF) origA origB -> Pair(tagAp2T, Pair(pairCF, Pair(aC, bC)))
      ap2R = mkAp2FRed (kF2 pairCF) origA origB origT recsT pairCF aC bC kPairR oaR obR

      -- mkAp1F (kF2 codeSndF) (mkAp2F ...) -> Pair(tagAp1T, Pair(codeSndF, mkAp2Result))
      leftRed = mkAp1FRed (kF2 codeSndF) (mkAp2F (kF2 pairCF) origA origB) origT recsT
                  codeSndF (ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair aC bC)))
                  kSndR ap2R

      -- case2 = mkEqF (mkAp1F ...) origB
      step4 = mkEqFRed (mkAp1F (kF2 codeSndF) (mkAp2F (kF2 pairCF) origA origB)) origB
                origT recsT
                (ap2 Pair (reify tagAp1) (ap2 Pair codeSndF
                  (ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair aC bC)))))
                bC
                leftRed obR
  in
  ruleTrans step12 step4
