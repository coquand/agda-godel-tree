{-# OPTIONS --safe --without-K --exact-split #-}

module Guard.Step where

open import Guard.Base
open import Guard.Term

------------------------------------------------------------------------
-- Derivation system
--
-- Deriv hyp eq means: equation eq is derivable from hypothesis hyp.
-- The system is purely equational (no propositional connectives).

data Deriv (hyp : Equation) : Equation -> Set where

  -- Computation axioms

  axI     : (t : Term) ->
            Deriv hyp (eqn (ap1 I t) t)

  axFst   : (a b : Term) ->
            Deriv hyp (eqn (ap1 Fst (ap2 Pair a b)) a)

  axSnd   : (a b : Term) ->
            Deriv hyp (eqn (ap1 Snd (ap2 Pair a b)) b)

  axConst : (a b : Term) ->
            Deriv hyp (eqn (ap2 Const a b) a)

  axComp  : (f g : Fun1) (t : Term) ->
            Deriv hyp (eqn (ap1 (Comp f g) t) (ap1 f (ap1 g t)))

  axComp2 : (h : Fun2) (f g : Fun1) (t : Term) ->
            Deriv hyp (eqn (ap1 (Comp2 h f g) t) (ap2 h (ap1 f t) (ap1 g t)))

  axLift  : (f : Fun1) (a b : Term) ->
            Deriv hyp (eqn (ap2 (Lift f) a b) (ap1 f a))

  axPost  : (f : Fun1) (h : Fun2) (a b : Term) ->
            Deriv hyp (eqn (ap2 (Post f h) a b) (ap1 f (ap2 h a b)))

  axFan   : (h1 h2 h : Fun2) (a b : Term) ->
            Deriv hyp (eqn (ap2 (Fan h1 h2 h) a b)
                           (ap2 h (ap2 h1 a b) (ap2 h2 a b)))

  axKT    : (t x : Term) ->
            Deriv hyp (eqn (ap1 (KT t) x) t)

  axRecLf : (z : Term) (s : Fun2) ->
            Deriv hyp (eqn (ap1 (Rec z s) O) z)

  axRecNd : (z : Term) (s : Fun2) (a b : Term) ->
            Deriv hyp (eqn (ap1 (Rec z s) (ap2 Pair a b))
                           (ap2 s (ap2 Pair a b)
                                  (ap2 Pair (ap1 (Rec z s) a)
                                            (ap1 (Rec z s) b))))

  -- Conditional (IfLf)

  axIfLfL : (a b : Term) ->
            Deriv hyp (eqn (ap2 IfLf O (ap2 Pair a b)) a)

  axIfLfN : (x y a b : Term) ->
            Deriv hyp (eqn (ap2 IfLf (ap2 Pair x y) (ap2 Pair a b)) b)

  -- Tree equality (TreeEq)

  axTreeEqLL : Deriv hyp (eqn (ap2 TreeEq O O) O)

  axTreeEqLN : (a b : Term) ->
               Deriv hyp (eqn (ap2 TreeEq O (ap2 Pair a b)) (ap2 Pair O O))

  axTreeEqNL : (a b : Term) ->
               Deriv hyp (eqn (ap2 TreeEq (ap2 Pair a b) O) (ap2 Pair O O))

  axTreeEqNN : (a1 a2 b1 b2 : Term) ->
               Deriv hyp (eqn (ap2 TreeEq (ap2 Pair a1 a2) (ap2 Pair b1 b2))
                              (ap2 IfLf (ap2 TreeEq a1 b1)
                                        (ap2 Pair (ap2 TreeEq a2 b2)
                                                  (ap2 Pair O O))))

  -- Structural rules

  axRefl : (t : Term) ->
           Deriv hyp (eqn t t)

  ruleSym : {t u : Term} ->
            Deriv hyp (eqn t u) -> Deriv hyp (eqn u t)

  ruleTrans : {t u v : Term} ->
              Deriv hyp (eqn t u) -> Deriv hyp (eqn u v) ->
              Deriv hyp (eqn t v)

  -- Canonical congruence (no var-0 capture!)

  cong1 : (f : Fun1) {t u : Term} ->
          Deriv hyp (eqn t u) ->
          Deriv hyp (eqn (ap1 f t) (ap1 f u))

  congL : (g : Fun2) {t u : Term} (x : Term) ->
          Deriv hyp (eqn t u) ->
          Deriv hyp (eqn (ap2 g t x) (ap2 g u x))

  congR : (g : Fun2) (x : Term) {t u : Term} ->
          Deriv hyp (eqn t u) ->
          Deriv hyp (eqn (ap2 g x t) (ap2 g x u))

  -- Variable instantiation

  ruleInst : (x : Nat) (t : Term) {eq : Equation} ->
             Deriv hyp eq -> Deriv hyp (substEq x t eq)

  -- Hypothesis

  ruleHyp : Deriv hyp hyp

  -- Schema F (uniqueness of tree recursion)
  -- If f and g both satisfy Rec z s (same base, same step),
  -- then f = g on all trees.

  ruleF : (f g : Fun1) (z : Term) (s : Fun2) ->
          Deriv hyp (eqn (ap1 f O) z) ->
          Deriv hyp (eqn (ap1 f (ap2 Pair (var zero) (var (suc zero))))
                         (ap2 s (ap2 Pair (var zero) (var (suc zero)))
                                (ap2 Pair (ap1 f (var zero)) (ap1 f (var (suc zero)))))) ->
          Deriv hyp (eqn (ap1 g O) z) ->
          Deriv hyp (eqn (ap1 g (ap2 Pair (var zero) (var (suc zero))))
                         (ap2 s (ap2 Pair (var zero) (var (suc zero)))
                                (ap2 Pair (ap1 g (var zero)) (ap1 g (var (suc zero)))))) ->
          Deriv hyp (eqn (ap1 f (var zero)) (ap1 g (var zero)))

------------------------------------------------------------------------
-- Consistency

Consistent : Equation -> Set
Consistent hyp = Deriv hyp (eqn O (ap2 Pair O O)) -> Empty
