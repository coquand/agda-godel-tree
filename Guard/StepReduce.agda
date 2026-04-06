{-# OPTIONS --safe --without-K --exact-split #-}

module Guard.StepReduce where

open import Guard.Base
open import Guard.Term
open import Guard.Step

------------------------------------------------------------------------
-- Derived rules: composition chains

-- Fan reduction
fanRed : {hyp : Equation} (h1 h2 h : Fun2) (a b : Term) ->
  Deriv hyp (eqn (ap2 (Fan h1 h2 h) a b)
                 (ap2 h (ap2 h1 a b) (ap2 h2 a b)))
fanRed h1 h2 h a b = axFan h1 h2 h a b

-- Lift reduction
liftRed : {hyp : Equation} (f : Fun1) (a b : Term) ->
  Deriv hyp (eqn (ap2 (Lift f) a b) (ap1 f a))
liftRed f a b = axLift f a b

-- Post reduction
postRed : {hyp : Equation} (f : Fun1) (h : Fun2) (a b : Term) ->
  Deriv hyp (eqn (ap2 (Post f h) a b) (ap1 f (ap2 h a b)))
postRed f h a b = axPost f h a b

-- KT reduction
ktRed : {hyp : Equation} (t x : Term) ->
  Deriv hyp (eqn (ap1 (KT t) x) t)
ktRed t x = axKT t x

-- constF2 reduction: ap2 (Lift (KT t)) a b = t
constF2Red : {hyp : Equation} (t a b : Term) ->
  Deriv hyp (eqn (ap2 (Lift (KT t)) a b) t)
constF2Red t a b =
  ruleTrans (liftRed (KT t) a b) (ktRed t a)

-- Comp reduction
compRed : {hyp : Equation} (f g : Fun1) (t : Term) ->
  Deriv hyp (eqn (ap1 (Comp f g) t) (ap1 f (ap1 g t)))
compRed f g t = axComp f g t

------------------------------------------------------------------------
-- Rec unfolding for nd

recNdRed : {hyp : Equation} (z : Term) (s : Fun2) (a b : Term) ->
  Deriv hyp (eqn (ap1 (Rec z s) (ap2 Pair a b))
                 (ap2 s (ap2 Pair a b)
                        (ap2 Pair (ap1 (Rec z s) a)
                                  (ap1 (Rec z s) b))))
recNdRed z s a b = axRecNd z s a b
