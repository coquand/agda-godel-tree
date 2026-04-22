{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.StepReduceUnify -- port of Guard.StepReduce to the unified
-- hyp-less DerivF (Guard.DerivF).
--
-- Same derived reduction lemmas (fanRed, liftRed, postRed, ktRed,
-- constF2Red, compRed, recNdRed) as Guard.StepReduce, but producing
-- DerivF (atomic (eqn _ _)) conclusions.  One-line rewrapping of each
-- axiom call; no logical changes.
--
-- Part of the unify-2 migration (see Guard/UNIFIED-DESIGN.md).

module Guard.StepReduceUnify where

open import Guard.Base
open import Guard.Term
open import Guard.Formula
open import Guard.DerivF

------------------------------------------------------------------------
-- Derived rules: composition chains

-- Fan reduction
fanRed : (h1 h2 h : Fun2) (a b : Term) ->
  Deriv (atomic (eqn (ap2 (Fan h1 h2 h) a b)
                      (ap2 h (ap2 h1 a b) (ap2 h2 a b))))
fanRed h1 h2 h a b = axFan h1 h2 h a b

-- Lift reduction
liftRed : (f : Fun1) (a b : Term) ->
  Deriv (atomic (eqn (ap2 (Lift f) a b) (ap1 f a)))
liftRed f a b = axLift f a b

-- Post reduction
postRed : (f : Fun1) (h : Fun2) (a b : Term) ->
  Deriv (atomic (eqn (ap2 (Post f h) a b) (ap1 f (ap2 h a b))))
postRed f h a b = axPost f h a b

-- KT reduction
ktRed : (t x : Term) ->
  Deriv (atomic (eqn (ap1 (KT t) x) t))
ktRed t x = axKT t x

-- constF2 reduction: ap2 (Lift (KT t)) a b = t
constF2Red : (t a b : Term) ->
  Deriv (atomic (eqn (ap2 (Lift (KT t)) a b) t))
constF2Red t a b = ruleTrans (liftRed (KT t) a b) (ktRed t a)

-- Comp reduction
compRed : (f g : Fun1) (t : Term) ->
  Deriv (atomic (eqn (ap1 (Comp f g) t) (ap1 f (ap1 g t))))
compRed f g t = axComp f g t

------------------------------------------------------------------------
-- Rec unfolding for nd

recNdRed : (z : Term) (s : Fun2) (a b : Term) ->
  Deriv (atomic (eqn (ap1 (Rec z s) (ap2 Pair a b))
                      (ap2 s (ap2 Pair a b)
                             (ap2 Pair (ap1 (Rec z s) a)
                                       (ap1 (Rec z s) b)))))
recNdRed z s a b = axRecNd z s a b
