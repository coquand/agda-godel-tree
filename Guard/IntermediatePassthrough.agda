{-# OPTIONS --safe --without-K --exact-split #-}

module Guard.IntermediatePassthrough where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.ThFun
open import Guard.ThFunTFor
open import Guard.ThFunTForDefs
open import Guard.ThFunTForCorrectDefs
open import Guard.PairPassthrough
open import Guard.PairPassthroughAll

------------------------------------------------------------------------
-- Intermediate passthrough for valid sub-proof pairs.
--
-- When two sub-proofs sp1, sp2 appear as data nd(sp1, sp2) in an encoding,
-- thFunTFor at Pair(reify sp1, reify sp2) passes through to
-- Pair(thFunTFor(reify sp1), thFunTFor(reify sp2)),
-- PROVIDED sp1 is a valid encoding with tag k >= 1
-- (i.e., reify sp1 = Pair(Pair(a1, a2), b) for some a1, a2, b).
--
-- This covers all proof encodings except encAxI (tag 0).

private
  poo : Term
  poo = ap2 Pair O O

-- sndArg2 evaluation: sndArg2(orig, recs) = recs
sndArg2Red : (orig recs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 sndArg2 orig recs) recs)
sndArg2Red orig recs =
  ruleTrans (postRed Snd Pair orig recs) (axSnd orig recs)

-- Full passthrough for Pair-tagged sub-proofs.
-- Given: sp1 has tag k >= 1, so reify(natCode k) = Pair(O, reify(natCode(k-1)))
--   and reify sp1 = Pair(Pair(O, reify(natCode(k-1))), reify data1)
-- Given: sp2 is non-lf (reify sp2 = Pair(...))
-- Then: thFunTFor(Pair(reify sp1, reify sp2)) = Pair(thFunTFor(reify sp1), thFunTFor(reify sp2))

intermediatePassthrough :
  (a1 a2 b : Term)  -- decomposition of reify sp1 = Pair(Pair(a1,a2), b)
  (sp2R : Term)      -- reify sp2
  (sp2a sp2b : Term) -- decomposition sp2R = Pair(sp2a, sp2b) (sp2 is non-lf)
  -> {hyp : Equation} ->
  Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair (ap2 Pair (ap2 Pair a1 a2) b) (ap2 Pair sp2a sp2b)))
                 (ap2 Pair (ap1 thFunTFor (ap2 Pair (ap2 Pair a1 a2) b))
                           (ap1 thFunTFor (ap2 Pair sp2a sp2b))))
intermediatePassthrough a1 a2 b sp2R sp2a sp2b =
  let tag = ap2 Pair (ap2 Pair a1 a2) b
      dat = ap2 Pair sp2a sp2b
      orig = ap2 Pair tag dat
      recs = ap2 Pair (ap1 thFunTFor tag) (ap1 thFunTFor dat)
  in ruleTrans (recNdRed O thFunStep tag dat)
     -- thFunStep(orig, recs)
     (ruleTrans (guardNd tag sp2a sp2b recs)
     -- ndDispatch(orig, recs)
     (ruleTrans (ndDispatchPairMiss a1 a2 b dat recs)
     -- sndArg2(orig, recs)
              (sndArg2Red orig recs)))

------------------------------------------------------------------------
-- Generic intermediate passthrough: takes an ndDispatch miss proof.

intermediateGeneric :
  (tagT datT : Term)      -- tag and data terms (tagT = reify(sp_a), datT = reify(sp_b))
  (sp2a sp2b : Term)       -- decomposition of second element = Pair(sp2a, sp2b)
  -> ((x recs : Term) -> {hyp : Equation} ->
      Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair tagT x) recs)
                     (ap2 sndArg2 (ap2 Pair tagT x) recs)))
  -> {hyp : Equation}
  -> Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair tagT (ap2 Pair sp2a sp2b)))
                    (ap2 Pair (ap1 thFunTFor tagT) (ap1 thFunTFor (ap2 Pair sp2a sp2b))))
intermediateGeneric tagT datT sp2a sp2b dispMiss =
  let dat = ap2 Pair sp2a sp2b
      orig = ap2 Pair tagT dat
      recs = ap2 Pair (ap1 thFunTFor tagT) (ap1 thFunTFor dat)
  in ruleTrans (recNdRed O thFunStep tagT dat)
     (ruleTrans (guardNd tagT sp2a sp2b recs)
     (ruleTrans (dispMiss dat recs)
              (sndArg2Red orig recs)))

------------------------------------------------------------------------
-- Intermediate passthrough for encAxI sub-proofs.
-- Tag = Pair(O, Pair(Pair(c1,c2), d)): first element is O (natCode 0 = lf).

intermediatePassthroughO :
  (c1 c2 d : Term)
  (sp2a sp2b : Term)
  -> {hyp : Equation}
  -> Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair (ap2 Pair O (ap2 Pair (ap2 Pair c1 c2) d)) (ap2 Pair sp2a sp2b)))
                    (ap2 Pair (ap1 thFunTFor (ap2 Pair O (ap2 Pair (ap2 Pair c1 c2) d)))
                              (ap1 thFunTFor (ap2 Pair sp2a sp2b))))
intermediatePassthroughO c1 c2 d sp2a sp2b =
  intermediateGeneric (ap2 Pair O (ap2 Pair (ap2 Pair c1 c2) d)) (ap2 Pair sp2a sp2b) sp2a sp2b
    (\x recs -> ndDispatchOPairMiss c1 c2 d x recs)
