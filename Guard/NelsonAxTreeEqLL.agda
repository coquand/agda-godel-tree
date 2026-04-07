{-# OPTIONS --safe --without-K --exact-split #-}

-- NelsonAxTreeEqLL.agda
-- Nelson base case: axTreeEqLL (tag 13).
-- Encoding: Pair(tag13T, dataT) where dataT is any term.
-- case13 = mkEqF (mkAp2F (kF2 treeeqCF) (kF2 oC) (kF2 oC)) (kF2 oC)
-- Result: Pair(mkAp2(TreeEq, O, O), O)
-- Note: axTreeEqLL has no parameters; the payload is ignored.

module Guard.NelsonAxTreeEqLL where

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
  tag13T : Term ; tag13T = reify (natCode n13)
  oC : Term ; oC = ap2 Pair O O
  treeeqCF : Term ; treeeqCF = reify (codeF2 TreeEq)

nelsonAxTreeEqLL : (aC bC : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair tag13T (ap2 Pair aC bC)))
                 (ap2 Pair (ap2 Pair (reify tagAp2) (ap2 Pair treeeqCF (ap2 Pair oC oC)))
                           oC))
nelsonAxTreeEqLL aC bC =
  let origT = ap2 Pair tag13T (ap2 Pair aC bC)
      recsT = ap2 Pair (ap1 thFunTFor tag13T) (ap1 thFunTFor (ap2 Pair aC bC))

      step12 = ruleTrans (phase1Nd tag13T aC bC)
                         (ndDispatchToCase13 (ap2 Pair aC bC) recsT)

      kTrR : {h : Equation} -> Deriv h (eqn (ap2 (kF2 treeeqCF) origT recsT) treeeqCF)
      kTrR = constF2Red treeeqCF origT recsT
      kOR : {h : Equation} -> Deriv h (eqn (ap2 (kF2 oC) origT recsT) oC)
      kOR = constF2Red oC origT recsT

      -- LHS: mkAp2F (kF2 treeeqCF) (kF2 oC) (kF2 oC)
      leftRed = mkAp2FRed (kF2 treeeqCF) (kF2 oC) (kF2 oC) origT recsT treeeqCF oC oC kTrR kOR kOR

      step4 = mkEqFRed (mkAp2F (kF2 treeeqCF) (kF2 oC) (kF2 oC)) (kF2 oC)
                origT recsT
                (ap2 Pair (reify tagAp2) (ap2 Pair treeeqCF (ap2 Pair oC oC)))
                oC
                leftRed kOR
  in
  ruleTrans step12 step4
