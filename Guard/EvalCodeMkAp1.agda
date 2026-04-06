{-# OPTIONS --safe --without-K --exact-split #-}

-- EvalCodeMkAp1.agda
-- Proves: evalCode(Pair(tagAp1T, Pair(fCode, t))) = evalCode(t)
-- for any fCode that doesn't match tagO or tagAp1 in evalStep.
--
-- This captures the key observation: the current evalCode strips
-- ALL functors (not just I), making cong1 trivially sound.
--
-- Outer: tagAp1 hit -> Snd(Snd(recs)) -> Snd(evalCode(Pair(fCode, t)))
-- Inner: fCode misses both tagO and tagAp1 -> passthrough
--        -> Pair(evalCode(fCode), evalCode(t))
-- Snd -> evalCode(t)

module Guard.EvalCodeMkAp1 where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.ThFunTForDefs
open import Guard.EvalCode
open import Guard.ThFunTForCorrectDefs using (branchMiss ; branchHit)
open import Guard.NelsonExtractors using (sndArg2Red)

private
  poo : Term ; poo = ap2 Pair O O

  -- isTagO reduction: isTagO(Pair(tag, data'), recs) = TreeEq(tag, O)
  isTagORed : (tag data' recs : Term) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap2 isTagO (ap2 Pair tag data') recs)
                   (ap2 TreeEq tag O))
  isTagORed tag data' recs =
    ruleTrans (fanRed (Lift Fst) (kF2 O) TreeEq (ap2 Pair tag data') recs)
    (ruleTrans (congL TreeEq (ap2 (kF2 O) (ap2 Pair tag data') recs)
                 (ruleTrans (liftRed Fst (ap2 Pair tag data') recs)
                            (axFst tag data')))
               (congR TreeEq tag (constF2Red O (ap2 Pair tag data') recs)))

  -- isTagAp1 reduction: isTagAp1(Pair(tag, data'), recs) = TreeEq(tag, tagAp1T)
  isTagAp1Red : (tag data' recs : Term) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap2 isTagAp1 (ap2 Pair tag data') recs)
                   (ap2 TreeEq tag tagAp1T))
  isTagAp1Red tag data' recs =
    ruleTrans (fanRed (Lift Fst) (kF2 tagAp1T) TreeEq (ap2 Pair tag data') recs)
    (ruleTrans (congL TreeEq (ap2 (kF2 tagAp1T) (ap2 Pair tag data') recs)
                 (ruleTrans (liftRed Fst (ap2 Pair tag data') recs)
                            (axFst tag data')))
               (congR TreeEq tag (constF2Red tagAp1T (ap2 Pair tag data') recs)))

  -- tagAp1T self-equality
  tagAp1Self : {hyp : Equation} -> Deriv hyp (eqn (ap2 TreeEq tagAp1T tagAp1T) O)
  tagAp1Self =
    ruleTrans (axTreeEqNN O (ap2 Pair O O) O (ap2 Pair O O))
    (ruleTrans (congL IfLf (ap2 Pair (ap2 TreeEq (ap2 Pair O O) (ap2 Pair O O)) poo) axTreeEqLL)
    (ruleTrans (axIfLfL (ap2 TreeEq (ap2 Pair O O) (ap2 Pair O O)) poo)
    (ruleTrans (axTreeEqNN O O O O)
    (ruleTrans (congL IfLf (ap2 Pair (ap2 TreeEq O O) poo) axTreeEqLL)
    (ruleTrans (axIfLfL (ap2 TreeEq O O) poo) axTreeEqLL)))))

  -- tagAp1Case reduction: Snd(Snd(recs))
  tagAp1CaseRed : (orig recs : Term) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap2 tagAp1Case orig recs) (ap1 Snd (ap1 Snd recs)))
  tagAp1CaseRed orig recs =
    ruleTrans (axPost Snd (Post Snd sndArg2) orig recs)
    (cong1 Snd (ruleTrans (axPost Snd sndArg2 orig recs)
                          (cong1 Snd (sndArg2Red orig recs))))

------------------------------------------------------------------------
-- Main lemma: evalCode(Pair(tagAp1T, Pair(fCode, t))) = evalCode(t)
--
-- Conditions on fCode:
-- (1) TreeEq(fCode, O) = Pair(O,O)       [isTagO miss in inner dispatch]
-- (2) TreeEq(fCode, tagAp1T) = Pair(O,O) [isTagAp1 miss in inner dispatch]

evalCodeMkAp1 :
  (fCode t : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 TreeEq fCode O) poo) ->
  Deriv hyp (eqn (ap2 TreeEq fCode tagAp1T) poo) ->
  Deriv hyp (eqn (ap1 evalCode (ap2 Pair tagAp1T (ap2 Pair fCode t)))
                 (ap1 evalCode t))
evalCodeMkAp1 fCode t tagOMiss tagAp1Miss =
  let innerP = ap2 Pair fCode t
      outerP = ap2 Pair tagAp1T innerP

      -- Outer recs
      outerRecs = ap2 Pair (ap1 evalCode tagAp1T) (ap1 evalCode innerP)
      -- Inner recs
      innerRecs = ap2 Pair (ap1 evalCode fCode) (ap1 evalCode t)

      -- OUTER LAYER: evalCode on Pair(tagAp1T, Pair(fCode, t))
      outerRecNd = axRecNd O evalStep tagAp1T innerP

      -- isTagO miss (tagAp1T = Pair(O, Pair(O,O)) is a Pair)
      outerMissO = branchMiss isTagO tagOCase (branch isTagAp1 tagAp1Case sndArg2)
                     outerP outerRecs
                     (ruleTrans (isTagORed tagAp1T innerP outerRecs)
                                (axTreeEqNL O (ap2 Pair O O)))

      -- isTagAp1 hit (tagAp1T = tagAp1T)
      outerHitAp1 = branchHit isTagAp1 tagAp1Case sndArg2
                      outerP outerRecs
                      (ruleTrans (isTagAp1Red tagAp1T innerP outerRecs) tagAp1Self)

      -- tagAp1Case -> Snd(Snd(outerRecs))
      outerCase = tagAp1CaseRed outerP outerRecs

      -- Snd(outerRecs) = evalCode(innerP)
      sndOuterRecs = axSnd (ap1 evalCode tagAp1T) (ap1 evalCode innerP)

      -- Chain outer: evalCode(outerP) = Snd(evalCode(innerP))
      toSndInner = ruleTrans outerRecNd
                   (ruleTrans outerMissO
                   (ruleTrans outerHitAp1
                   (ruleTrans outerCase
                   (cong1 Snd sndOuterRecs))))

      -- INNER LAYER: evalCode(Pair(fCode, t)) passthrough
      innerRecNd = axRecNd O evalStep fCode t

      -- isTagO miss: TreeEq(fCode, O) = Pair(O,O) [premise]
      innerMissO = branchMiss isTagO tagOCase (branch isTagAp1 tagAp1Case sndArg2)
                     innerP innerRecs
                     (ruleTrans (isTagORed fCode t innerRecs) tagOMiss)

      -- isTagAp1 miss: TreeEq(fCode, tagAp1T) = Pair(O,O) [premise]
      innerMissAp1 = branchMiss isTagAp1 tagAp1Case sndArg2
                       innerP innerRecs
                       (ruleTrans (isTagAp1Red fCode t innerRecs) tagAp1Miss)

      -- default passthrough -> sndArg2 -> innerRecs
      innerDefault = sndArg2Red innerP innerRecs

      -- evalCode(innerP) = Pair(evalCode(fCode), evalCode(t))
      innerToRecs = ruleTrans innerRecNd
                    (ruleTrans innerMissO
                    (ruleTrans innerMissAp1 innerDefault))

      -- Snd -> evalCode(t)
      sndRecs = axSnd (ap1 evalCode fCode) (ap1 evalCode t)

      -- Snd(evalCode(innerP)) = evalCode(t)
      innerFinal = ruleTrans (cong1 Snd innerToRecs) sndRecs

  in ruleTrans toSndInner innerFinal

------------------------------------------------------------------------
-- Specialization: when fCode = Pair(fTag, fData) with fTag a Pair.
-- isTagO miss is axTreeEqNL. Only need isTagAp1 miss as premise.

evalCodeMkAp1Pair :
  (fTag fData t : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 TreeEq (ap2 Pair fTag fData) tagAp1T) poo) ->
  Deriv hyp (eqn (ap1 evalCode (ap2 Pair tagAp1T (ap2 Pair (ap2 Pair fTag fData) t)))
                 (ap1 evalCode t))
evalCodeMkAp1Pair fTag fData t ap1Miss =
  evalCodeMkAp1 (ap2 Pair fTag fData) t (axTreeEqNL fTag fData) ap1Miss

------------------------------------------------------------------------
-- Further specialization: when fTag = Pair(f1, f2) (the most common case).
-- Both miss conditions discharge automatically:
-- TreeEq(Pair(Pair(f1,f2), fData), O) = Pair(O,O) by axTreeEqNL
-- TreeEq(Pair(Pair(f1,f2), fData), tagAp1T):
--   tagAp1T = Pair(O, Pair(O,O))
--   = IfLf(TreeEq(Pair(f1,f2), O), ...) = IfLf(Pair(O,O), ...) = Pair(O,O)

evalCodeMkAp1PairPair :
  (f1 f2 fData t : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap1 evalCode (ap2 Pair tagAp1T (ap2 Pair (ap2 Pair (ap2 Pair f1 f2) fData) t)))
                 (ap1 evalCode t))
evalCodeMkAp1PairPair f1 f2 fData t =
  evalCodeMkAp1Pair (ap2 Pair f1 f2) fData t
    (ruleTrans (axTreeEqNN (ap2 Pair f1 f2) fData O (ap2 Pair O O))
    (ruleTrans (congL IfLf (ap2 Pair (ap2 TreeEq fData (ap2 Pair O O)) poo)
                 (axTreeEqNL f1 f2))
               (axIfLfN O O (ap2 TreeEq fData (ap2 Pair O O)) poo)))
