{-# OPTIONS --safe --without-K --exact-split #-}

-- NelsonAxRecLf.agda
-- Nelson base case: axRecLf (tag 9).
-- Encoding: Pair(tag9T, Pair(zC, sC))
-- case9 = mkEqF (mkAp1F (codeRecF origA origB) (kF2 oC)) origA
-- Result: Pair(mkAp1(Rec(z,s), O), z)
-- where Rec(z,s) code = Pair(recTag, Pair(z, s))

module Guard.NelsonAxRecLf where

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
  tag9T : Term ; tag9T = reify (natCode n9)
  oC : Term ; oC = ap2 Pair O O
  n31 : Nat ; n31 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))))))))))
  recTag : Term ; recTag = reify (natCode n31)

nelsonAxRecLf : (zC sC : Term) -> {hyp : Equation} ->
  let recCode = ap2 Pair recTag (ap2 Pair zC sC)
  in Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair tag9T (ap2 Pair zC sC)))
                    (ap2 Pair (ap2 Pair (reify tagAp1) (ap2 Pair recCode oC))
                              zC))
nelsonAxRecLf zC sC =
  let origT = ap2 Pair tag9T (ap2 Pair zC sC)
      recsT = ap2 Pair (ap1 thFunTFor tag9T) (ap1 thFunTFor (ap2 Pair zC sC))
      recCode = ap2 Pair recTag (ap2 Pair zC sC)

      step12 = ruleTrans (phase1Nd tag9T zC sC)
                         (ndDispatchToCase9 (ap2 Pair zC sC) recsT)

      oaR = origARed tag9T zC sC recsT
      obR = origBRed tag9T zC sC recsT

      -- codeRecF origA origB = Fan (kF2 recTag) (Fan origA origB Pair) Pair
      -- Reduces to Pair(recTag, Pair(zC, sC)) = recCode
      recCodeR : {h : Equation} -> Deriv h (eqn (ap2 (Fan (kF2 recTag) (Fan origA origB Pair) Pair) origT recsT) recCode)
      recCodeR = ruleTrans (axFan (kF2 recTag) (Fan origA origB Pair) Pair origT recsT)
                 (ruleTrans (congL Pair (ap2 (Fan origA origB Pair) origT recsT)
                               (constF2Red recTag origT recsT))
                 (congR Pair recTag
                   (ruleTrans (axFan origA origB Pair origT recsT)
                   (ruleTrans (congL Pair (ap2 origB origT recsT) oaR)
                              (congR Pair zC obR)))))

      -- kF2 oC = oC
      kOCR : {h : Equation} -> Deriv h (eqn (ap2 (kF2 oC) origT recsT) oC)
      kOCR = constF2Red oC origT recsT

      -- mkAp1F (codeRecF origA origB) (kF2 oC) -> Pair(tagAp1T, Pair(recCode, oC))
      leftRed = mkAp1FRed (Fan (kF2 recTag) (Fan origA origB Pair) Pair) (kF2 oC) origT recsT recCode oC recCodeR kOCR

      step4 = mkEqFRed (mkAp1F (Fan (kF2 recTag) (Fan origA origB Pair) Pair) (kF2 oC)) origA
                origT recsT
                (ap2 Pair (reify tagAp1) (ap2 Pair recCode oC))
                zC
                leftRed oaR
  in
  ruleTrans step12 step4
