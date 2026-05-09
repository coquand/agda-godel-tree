{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.UnfoldAtValue -- meta-recursion deriving e[t/0] for any
-- value-shape t from the indBT base case and a step combinator.
--
-- The semantic content of an indBT inference at conclusion
-- atomic e (with var 0 free) :
--
--   base : atomic (substEq 0 O e)              -- proved
--   step : atomic e[v1/0]
--           imp atomic e[v2/0]
--           imp atomic e[Pair v1 v2/0]          -- proved
--   ----------------------------------------------------
--           atomic e                            -- (universal in var 0)
--
-- In the open fragment DerivT0 (no induction), the universal
-- conclusion atomic e is unobtainable for general open e.  However,
-- for any specific  closed (value-shape)  tree  t , we CAN derive
--
--   atomic (substEq 0 t e)
--
-- by a finite mp-chain through  step  with  v1 / v2  instantiated
-- recursively to t's subtrees.  unfoldAtValue is that meta-recursion.
--
-- The step-combinator is supplied as a parameter:  given derivations
-- of  e[a/0]  and  e[b/0] , produce  e[Pair a b/0] .  The full
-- derivation of stepCombiner from the raw  step  premise + freshness
-- of  v1, v2  in  e  requires substitution-composition lemmas
-- (BRA2.SubstCompose plus extensions) and is the next deliverable.
--
-- Plug-in: the stepCombiner can also be supplied directly when the
-- equation  e  is closed (no var 0), in which case
-- substEq 0 t e = e  for any t, and stepCombiner returns the second
-- argument unchanged --- the simplest possible instance, generalising
-- T3 (RankDecrementBotIndBT).

module BRA2.UnfoldAtValue where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
import BRA2.DerivT0 as O

------------------------------------------------------------------------
-- Step-combinator: given derivations of e[a/0] and e[b/0], derive
-- e[Pair a b/0].  This is the abstract content of the indBT step.

StepCombiner : Equation -> Set
StepCombiner e =
  (a b : Term) -> IsValue a -> IsValue b ->
  O.DerivT0 (atomic (substEq zero a e)) ->
  O.DerivT0 (atomic (substEq zero b e)) ->
  O.DerivT0 (atomic (substEq zero (ap2 Pair a b) e))

------------------------------------------------------------------------
-- The unfold.
--
-- Recursion on the value-shape proof  vt :  IsValue t .
--   valO        : t = O .  Result is  base : atomic (substEq 0 O e) .
--   valNd a b   : t = ap2 Pair a b .  Recurse on a and b ; combine
--                 via stepCombiner.

unfoldAtValue :
  (e : Equation) ->
  StepCombiner e ->
  O.DerivT0 (atomic (substEq zero O e)) ->
  (t : Term) (vt : IsValue t) ->
  O.DerivT0 (atomic (substEq zero t e))
unfoldAtValue _ _    base .O                 valO              = base
unfoldAtValue e step base .(ap2 Pair a b)    (valNd a b va vb) =
  let ih_a = unfoldAtValue e step base a va
      ih_b = unfoldAtValue e step base b vb
  in step a b va vb ih_a ih_b

------------------------------------------------------------------------
-- The trivial stepCombiner for closed equations.
--
-- If  e  has no free var 0 , then  substEq 0 t e = e  for any t,
-- and stepCombiner is "ignore inputs and return any DerivT0 atomic e ":
-- but we do not directly express this without freshness machinery.
--
-- Instead, the cleanest closed-equation case is simpler still:
-- if the equation is closed, the indBT base IS the derivation of
-- atomic e (T3's observation).  Then unfoldAtValue is unnecessary
-- because every  e[t/0]  is just  e  itself.
--
-- We expose a concrete witness for the bot-conclusion case (T3):
-- substEq 0 t bot's-equation = bot's-equation, by computation.

botEqn : Equation
botEqn = eqn O (ap2 Pair O O)

substEq_botEqn_inert :
  (x : Nat) (t : Term) ->
  Eq (substEq x t botEqn) botEqn
substEq_botEqn_inert _ _ = refl

-- Trivial step combinator at botEqn: the type-level reduction
-- collapses the conclusion to atomic botEqn, so the second argument
-- already has the desired type; just return it.

botEqn_stepCombiner : StepCombiner botEqn
botEqn_stepCombiner _ _ _ _ _ d_b = d_b
