{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.IndBTElimDemo -- end-to-end demonstration of indBT-elimination
-- for a closed-by-demand-equation conclusion.
--
-- Tests the chain
--
--   WellFormedIndBT + base + step + (t : Term) + IsValue t
--                  + Eq (substEq 0 t e) botEqn  (demand equation)
--   -->  DerivT0 bot
--
-- using only the existing infrastructure:
--   BRA2.UnfoldAtValue        (unfoldAtValue)
--   BRA2.StepCombinerFromStep (stepCombinerFromStep)
--   BRA2.WellFormedIndBT      (record fields)
--
-- The demand equation  Eq (substEq 0 t e) botEqn  is the single-frame
-- proxy for a future  IndBTContext0 (atomic e) bot  argument.  Once
-- IndBTContext0  is built, the demand equation will be EXTRACTED by
-- evaluating the context, and this demo upgrades to consume contexts
-- directly.
--
-- This file does NOT solve the find-and-extract problem (locating an
-- indBT inside a DerivTBounded tree).  It validates the mathematical
-- core: given an indBT premises in DerivT0 + freshness + a value t
-- whose substitution into  e  yields  botEqn , we can derive
-- DerivT0 bot.

module BRA2.IndBTElimDemo where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
import BRA2.DerivT0 as O
open import BRA2.DerivT0 using (bot)
open import BRA2.WellFormedIndBT
open import BRA2.UnfoldAtValue using (botEqn ; unfoldAtValue)
open import BRA2.StepCombinerFromStep using (stepCombinerFromStep)

------------------------------------------------------------------------
-- The demand equation.
--
-- DemandEq e t :  substituting  t  for  var 0  in  e  yields bot's
-- equation.  When this holds and  t  is value-shape, the indBT-step
-- can be unfolded along  t  to produce a DerivT0 of bot.

DemandEq : Equation -> Term -> Set
DemandEq e t = Eq (substEq zero t e) botEqn

------------------------------------------------------------------------
-- The demo handler signature.
--
-- Given an indBT instance with well-formedness side conditions, its
-- premises in DerivT0, a value t closing e to bot's equation, produce
-- DerivT0 bot.

IndBTBotHandlerDemand : Set
IndBTBotHandlerDemand =
  (e : Equation) (v1 v2 : Nat) ->
  WellFormedIndBT e v1 v2 ->
  O.DerivT0 (atomic (substEq zero O e)) ->
  O.DerivT0 ((atomic (substEq zero (var v1) e))
             imp ((atomic (substEq zero (var v2) e))
                  imp (atomic (substEq zero (ap2 Pair (var v1) (var v2)) e)))) ->
  (t : Term) -> IsValue t ->
  DemandEq e t ->
  O.DerivT0 bot

------------------------------------------------------------------------
-- The demo implementation.
--
-- Construction:
--   1. From step + WellFormedIndBT, get StepCombiner via stepCombinerFromStep.
--   2. From base + StepCombiner + (t, vt), get DerivT0 (atomic (substEq 0 t e))
--      via unfoldAtValue.
--   3. Use the demand equation to coerce  atomic (substEq 0 t e)  to
--      atomic botEqn = bot  (definitionally), then eqSubst.

indBTElimDemo : IndBTBotHandlerDemand
indBTElimDemo e v1 v2 wf base step t vt eqDemand =
  let stepC = stepCombinerFromStep e v1 v2
                (fresh1 wf) (fresh2 wf) (distinct wf) step
      d_at_t : O.DerivT0 (atomic (substEq zero t e))
      d_at_t = unfoldAtValue e stepC base t vt
  in eqSubst (\ E -> O.DerivT0 (atomic E)) eqDemand d_at_t
