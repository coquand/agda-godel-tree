{-# OPTIONS --safe --without-K --exact-split #-}

-- Nelson Schema F experiment: prove by internal induction that
-- the passthrough function Rec O sndArg2 equals the identity I.
--
-- This tests whether Schema F can prove properties of recursive
-- functions that appear in the thFunTFor infrastructure.
--
-- The proof:
--   f = Rec O sndArg2 (passthrough)
--   g = I (identity)
--   z = O, s = sndArg2
--   fBase: f(O) = O           (axRecLf)
--   fStep: f(Pair(a,b)) = sndArg2(Pair(a,b), Pair(f(a), f(b)))
--          = Pair(f(a), f(b))  (axRecNd + sndArg2 reduction)
--   gBase: I(O) = O           (axI)
--   gStep: I(Pair(a,b)) = sndArg2(Pair(a,b), Pair(I(a), I(b)))
--          Pair(a,b) = Pair(I(a), I(b))  (by axI on each component)
--   Schema F: f(t) = I(t) = t for all t.

module Guard.NelsonSchemaF where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.ThFunTForDefs using (sndArg2)

private
  v0 : Term ; v0 = var zero
  v1 : Term ; v1 = var (suc zero)

  passF : Fun1
  passF = Rec O sndArg2

  -- sndArg2(orig, recs) = recs
  sndArg2Red : (orig recs : Term) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap2 sndArg2 orig recs) recs)
  sndArg2Red orig recs = ruleTrans (axPost Snd Pair orig recs) (axSnd orig recs)

  -- f base: passF(O) = O
  fBase : {hyp : Equation} -> Deriv hyp (eqn (ap1 passF O) O)
  fBase = axRecLf O sndArg2

  -- f step: passF(Pair(v0, v1)) = sndArg2(Pair(v0,v1), Pair(passF(v0), passF(v1)))
  fStep : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 passF (ap2 Pair v0 v1))
                   (ap2 sndArg2 (ap2 Pair v0 v1) (ap2 Pair (ap1 passF v0) (ap1 passF v1))))
  fStep = axRecNd O sndArg2 v0 v1

  -- g base: I(O) = O
  gBase : {hyp : Equation} -> Deriv hyp (eqn (ap1 I O) O)
  gBase = axI O

  -- g step: I(Pair(v0, v1)) = sndArg2(Pair(v0,v1), Pair(I(v0), I(v1)))
  -- i.e., Pair(v0, v1) = Pair(I(v0), I(v1))
  gStep : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 I (ap2 Pair v0 v1))
                   (ap2 sndArg2 (ap2 Pair v0 v1) (ap2 Pair (ap1 I v0) (ap1 I v1))))
  gStep =
    -- LHS: I(Pair(v0,v1)) = Pair(v0,v1) by axI
    -- RHS: sndArg2(Pair(v0,v1), Pair(I(v0), I(v1))) = Pair(I(v0), I(v1)) by sndArg2Red
    -- Bridge: Pair(v0,v1) = Pair(I(v0), I(v1)) by congL/congR with axI
    ruleTrans (axI (ap2 Pair v0 v1))
    (ruleSym (ruleTrans (sndArg2Red (ap2 Pair v0 v1) (ap2 Pair (ap1 I v0) (ap1 I v1)))
             (ruleTrans (congL Pair (ap1 I v1) (axI v0))
                        (congR Pair v0 (axI v1)))))

------------------------------------------------------------------------
-- Schema F: passF = I on all trees

passFIsIdentity : {hyp : Equation} ->
  Deriv hyp (eqn (ap1 passF (var zero)) (ap1 I (var zero)))
passFIsIdentity = ruleF passF I O sndArg2 fBase fStep gBase gStep

-- Corollary: passF(t) = t for any term t
passFIsId : (t : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap1 passF t) t)
passFIsId t = ruleTrans (ruleInst zero t passFIsIdentity) (axI t)
