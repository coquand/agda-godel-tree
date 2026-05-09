{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.StepReduce -- small derived equational lemmas on BRA functors.
--
-- One-line rewrappings of Deriv axioms (fanRed, liftRed, postRed,
-- ktRed, constF2Red, compRed, recNdRed).  Useful as building blocks
-- for longer equational chains where a named rewrapping keeps proofs
-- readable.

module BRA2.StepReduce where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.DerivThreshold

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

-- KT reduction (IsValue-indexed; value-shaped input).
ktRed : (v : Term) -> IsValue v -> (x : Term) ->
  Deriv (atomic (eqn (ap1 (KT v) x) v))
ktRed v iv x = axKT v iv x

-- constF2 reduction: ap2 (Lift (KT v)) a b = v  for value-shaped v.
constF2Red : (v : Term) -> IsValue v -> (a b : Term) ->
  Deriv (atomic (eqn (ap2 (Lift (KT v)) a b) v))
constF2Red v iv a b = ruleTrans (liftRed (KT v) a b) (ktRed v iv a)

-- Comp reduction
compRed : (f g : Fun1) (t : Term) ->
  Deriv (atomic (eqn (ap1 (Comp f g) t) (ap1 f (ap1 g t))))
compRed f g t = axComp f g t

------------------------------------------------------------------------
-- Rec unfolding for nd
--
-- Rec is now an Agda function defined as  Rec s = Comp2 (treeRec Z s) Z I
-- (no z parameter; only z = O is ever used).  The unfolding equation
-- has an extra  Pair O ...  in the first argument to s , reflecting
-- the  Comp2 ... Z I  encoding's  Z -branch supplying the leaf carrier.

recNdRed : (s : Fun2) (a b : Term) ->
  Deriv (atomic (eqn (ap1 (Rec s) (ap2 Pair a b))
                      (ap2 s (ap2 Pair O (ap2 Pair a b))
                             (ap2 Pair (ap1 (Rec s) a)
                                       (ap1 (Rec s) b)))))
recNdRed s a b = axRecNd s a b
