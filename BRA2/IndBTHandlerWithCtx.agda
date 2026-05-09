{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.IndBTHandlerWithCtx -- end-to-end certified pipeline composing
-- extractDemandSimple with indBTElimDemo.
--
-- Given:
--   * an indBT instance with WellFormedIndBT side conditions,
--   * its premises (base, step) lifted to DerivT0,
--   * an IndBTContext0 (atomic e) bot capturing the structural-rule
--     path from the indBT's conclusion to bot,
--
-- produce a  Maybe (DerivT0 bot) :  `just` when the path is one
-- ExtractDemand can solve (currently only the `hole` shape -- e is
-- forced to botEqn);  `nothing`  when the path uses constructors
-- ExtractDemand has not yet implemented (sym, transL/R, mpL/R, inst,
-- pending the (P1)/(P2) refactor of IndBTContext0).
--
-- This file is the closing of the loop:  WellFormedIndBT +
-- IndBTContext0 + extractDemandSimple + indBTElimDemo  composed into
-- a single end-to-end function.  The internal certified-by-Agda chain
-- now spans from "raw indBT premises in DerivTBounded" all the way
-- down to "DerivT0 bot", parametric in the path's structure but
-- complete for the trivial path.

module BRA2.IndBTHandlerWithCtx where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
import BRA2.DerivT0 as O
open import BRA2.DerivT0 using (bot)
open import BRA2.WellFormedIndBT
open import BRA2.IndBTContext0
open import BRA2.IndBTElimDemo using (DemandEq ; indBTElimDemo)
open import BRA2.ExtractDemand using
  (Maybe ; nothing ; just ; ExtractedDemand ; extractDemandSimple)

------------------------------------------------------------------------
-- helper: dispatch on the result of extractDemandSimple.

indBTHandlerStep :
  (e : Equation) (v1 v2 : Nat) ->
  WellFormedIndBT e v1 v2 ->
  O.DerivT0 (atomic (substEq zero O e)) ->
  O.DerivT0 ((atomic (substEq zero (var v1) e))
             imp ((atomic (substEq zero (var v2) e))
                  imp (atomic (substEq zero (ap2 Pair (var v1) (var v2)) e)))) ->
  Maybe (ExtractedDemand e) ->
  Maybe (O.DerivT0 bot)
indBTHandlerStep _ _ _ _ _ _ nothing = nothing
indBTHandlerStep e v1 v2 wf base step (just (mkSigma t (mkSigma vt eqDemand))) =
  just (indBTElimDemo e v1 v2 wf base step t vt eqDemand)

------------------------------------------------------------------------
-- The end-to-end pipeline.

indBTHandlerWithCtx :
  (e : Equation) (v1 v2 : Nat) ->
  WellFormedIndBT e v1 v2 ->
  O.DerivT0 (atomic (substEq zero O e)) ->
  O.DerivT0 ((atomic (substEq zero (var v1) e))
             imp ((atomic (substEq zero (var v2) e))
                  imp (atomic (substEq zero (ap2 Pair (var v1) (var v2)) e)))) ->
  IndBTContext0 (atomic e) bot ->
  Maybe (O.DerivT0 bot)
indBTHandlerWithCtx e v1 v2 wf base step ctx =
  indBTHandlerStep e v1 v2 wf base step (extractDemandSimple e ctx)
