{-# OPTIONS --safe --without-K --exact-split #-}

-- NelsonAxReflGen.agda
-- Generalized axRefl Nelson proof for arbitrary term x.
--
-- nelsonAxRefl in NelsonAxRefl.agda is specialized to v0 = var zero.
-- This version works for any x:
--   thFunTFor(Pair(tag17T, Pair(x, O))) = Pair(x, x)
--
-- Uses the modular dispatch infrastructure (phase1Nd + ndDispatchToCase17).

module Guard.Nelson.NelsonAxReflGen where

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
  tag17T : Term ; tag17T = reify (natCode n17)

------------------------------------------------------------------------
-- nelsonAxReflGen: generalized axRefl for any term x
--
-- thFunTFor(Pair(tag17T, Pair(x, O))) = Pair(x, x)
-- case17 = mkEqF origA origA = Fan origA origA Pair
-- origA(Pair(tag17T, Pair(x, O)), recs) = Fst(Snd(Pair(tag17T, Pair(x, O)))) = x

nelsonAxReflGen : (x : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair tag17T (ap2 Pair x O)))
                 (ap2 Pair x x))
nelsonAxReflGen x =
  let origT = ap2 Pair tag17T (ap2 Pair x O)
      recsT = ap2 Pair (ap1 thFunTFor tag17T) (ap1 thFunTFor (ap2 Pair x O))

      -- Phase 1+2: thFunTFor(origT) = case17(origT, recsT)
      step12 = ruleTrans (phase1Nd tag17T x O)
                         (ndDispatchToCase17 (ap2 Pair x O) recsT)

      -- origA = Fst(Snd(orig)) = Fst(Pair(x, O)) = x
      oA = origARed tag17T x O recsT

      -- case17 = mkEqF origA origA = Fan origA origA Pair
      step4 = mkEqFRed origA origA origT recsT x x oA oA
  in
  ruleTrans step12 step4
