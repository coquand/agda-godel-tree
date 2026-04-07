{-# OPTIONS --safe --without-K --exact-split #-}

-- NelsonAxKT.agda
-- Nelson base case: axKT (tag 25).
-- Encoding: Pair(tag25T, Pair(tC, xC))
-- case25 = mkEqF (mkAp1F (Fan (kF2 codeKTTag) origA Pair) origB) origA
-- Result: Pair(mkAp1(Pair(codeKTTag, tC), xC), tC)
-- i.e., Pair(code(KT(t)(x)), code(t))

module Guard.Nelson.NelsonAxKT where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.ThFunTForDefs
open import Guard.ThFunTForCases3
open import Guard.ThFunTFor
open import Guard.Nelson.NelsonDispatch
open import Guard.Nelson.NelsonExtractors

private
  tag25T : Term ; tag25T = reify (natCode n25)
  codeKTTag : Term ; codeKTTag = reify (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))))))))))))

nelsonAxKT : (tC xC : Term) -> {hyp : Equation} ->
  let ktCode = ap2 Pair codeKTTag tC
  in Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair tag25T (ap2 Pair tC xC)))
                    (ap2 Pair (ap2 Pair (reify tagAp1) (ap2 Pair ktCode xC))
                              tC))
nelsonAxKT tC xC =
  let origT = ap2 Pair tag25T (ap2 Pair tC xC)
      recsT = ap2 Pair (ap1 thFunTFor tag25T) (ap1 thFunTFor (ap2 Pair tC xC))
      ktCode = ap2 Pair codeKTTag tC

      -- Phase 1+2
      step12 = ruleTrans (phase1Nd tag25T tC xC)
                         (ndDispatchToCase25 (ap2 Pair tC xC) recsT)

      -- Extractors
      oaR = origARed tag25T tC xC recsT
      obR = origBRed tag25T tC xC recsT

      -- Fan (kF2 codeKTTag) origA Pair (origT, recsT) = Pair(codeKTTag, tC) = ktCode
      ktCodeR : {h : Equation} -> Deriv h (eqn (ap2 (Fan (kF2 codeKTTag) origA Pair) origT recsT) ktCode)
      ktCodeR = ruleTrans (axFan (kF2 codeKTTag) origA Pair origT recsT)
                (ruleTrans (congL Pair (ap2 origA origT recsT) (constF2Red codeKTTag origT recsT))
                           (congR Pair codeKTTag oaR))

      -- mkAp1F (Fan ...) origB -> Pair(tagAp1T, Pair(ktCode, xC))
      leftRed = mkAp1FRed (Fan (kF2 codeKTTag) origA Pair) origB origT recsT ktCode xC ktCodeR obR

      -- case25 = mkEqF left origA
      step4 = mkEqFRed (mkAp1F (Fan (kF2 codeKTTag) origA Pair) origB) origA
                origT recsT
                (ap2 Pair (reify tagAp1) (ap2 Pair ktCode xC))
                tC
                leftRed oaR
  in
  ruleTrans step12 step4
