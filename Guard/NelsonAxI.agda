{-# OPTIONS --safe --without-K --exact-split #-}

-- Nelson base case: axI (tag 0).
-- Encoding: nd(natCode 0)(nd tC lf) = Pair(tag0T, Pair(tC, O))
-- Result: Pair(mkAp1(codeI, tC), tC)
-- case0 = mkEqF (mkAp1F (kF2 codeIF) origA) origA

module Guard.NelsonAxI where

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
  tag0T : Term ; tag0T = reify (natCode n0)
  codeIF : Term ; codeIF = reify (codeF1 I)
  tagAp1T : Term ; tagAp1T = reify tagAp1

nelsonAxI : (tC : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair tag0T (ap2 Pair tC O)))
                 (ap2 Pair (ap2 Pair tagAp1T (ap2 Pair codeIF tC)) tC))
nelsonAxI tC =
  let origT = ap2 Pair tag0T (ap2 Pair tC O)
      recsT = ap2 Pair (ap1 thFunTFor tag0T) (ap1 thFunTFor (ap2 Pair tC O))

      -- Phase 1+2: thFunTFor(origT) = case0(origT, recsT)
      step12 = ruleTrans (phase1Nd tag0T tC O)
                         (ndDispatchToCase0 (ap2 Pair tC O) recsT)

      -- origA(origT, recsT) = tC
      oaR = origARed tag0T tC O recsT

      -- kF2 codeIF (origT, recsT) = codeIF
      kIR : {h : Equation} -> Deriv h (eqn (ap2 (kF2 codeIF) origT recsT) codeIF)
      kIR = constF2Red codeIF origT recsT

      -- kF2 tagAp1T (origT, recsT) = tagAp1T
      kTR : {h : Equation} -> Deriv h (eqn (ap2 (kF2 tagAp1T) origT recsT) tagAp1T)
      kTR = constF2Red tagAp1T origT recsT

      -- mkAp1F (kF2 codeIF) origA (origT, recsT)
      -- = Fan (kF2 tagAp1T) (Fan (kF2 codeIF) origA Pair) Pair (origT, recsT)
      -- = Pair(tagAp1T, Pair(codeIF, tC))
      leftRed : {h : Equation} -> Deriv h (eqn (ap2 (mkAp1F (kF2 codeIF) origA) origT recsT)
                                                (ap2 Pair tagAp1T (ap2 Pair codeIF tC)))
      leftRed = ruleTrans (axFan (kF2 tagAp1T) (Fan (kF2 codeIF) origA Pair) Pair origT recsT)
                (ruleTrans (congL Pair (ap2 (Fan (kF2 codeIF) origA Pair) origT recsT) kTR)
                (congR Pair tagAp1T
                  (ruleTrans (axFan (kF2 codeIF) origA Pair origT recsT)
                  (ruleTrans (congL Pair (ap2 origA origT recsT) kIR)
                             (congR Pair codeIF oaR)))))

      -- case0 = mkEqF (mkAp1F (kF2 codeIF) origA) origA
      step4 = mkEqFRed (mkAp1F (kF2 codeIF) origA) origA origT recsT
                        (ap2 Pair tagAp1T (ap2 Pair codeIF tC)) tC
                        leftRed oaR
  in
  ruleTrans step12 step4
