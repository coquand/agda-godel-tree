{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.ClosedPipeline -- end-to-end certified transformation
--   IndBTPackageAt Target  +  Eq (substEq zero O pkgE) pkgE  -->  DerivT0 Target
--
-- For any indBTB package whose underlying equation is closed in
-- var 0  (i.e.  substEq zero O pkgE = pkgE  by computation), the
-- premise  pkgBase : DerivT0 (atomic (substEq zero O pkgE))  IS
-- already a derivation of  atomic pkgE .  The eliminator's step
-- machinery is unnecessary: the indBT collapses to its base case,
-- which is plugged through the structural-rule path  pkgCtx  to
-- reach the eventual target.
--
-- This is the Case-B-finishing companion to BRA2.FindIndBT: every
-- pkg produced by  findIndBT  on a wrapped indBTB whose pkgE
-- happens to be closed (which is the typical configuration when
-- the wrapping eventually produces  bot  via paths that don't
-- introduce free variables) reduces to  DerivT0 bot  via this
-- handler.
--
-- For our two synthetic smoke-test scenarios:
--
--   * (C/E) input pkgE = botEqn = eqn O (Pair O O) — closed; refl
--           witnesses substEq zero O botEqn = botEqn.
--   * (D)   input pkgE = swappedBotEqn = eqn (Pair O O) O — closed;
--           refl witnesses substEq zero O swappedBotEqn = swappedBotEqn.
--
-- Both witnesses hold by computation.  The handler thus completes
-- the pipeline for these scenarios without invoking the demand-
-- equation extractor at all.
--
-- Open: pkgE with var 0 free.  Then substEq zero O pkgE != pkgE
-- (in general); the eliminator's step machinery is needed to
-- derive  DerivT0 (atomic (substEq zero t pkgE))  for some chosen
-- value t  whose substitution composes with pkgCtx to give the
-- target.  That's the doc's Case C territory and is deferred.

module BRA2.ClosedPipeline where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
import BRA2.DerivT0       as O
import BRA2.DerivTBounded as B
open import BRA2.DerivT0 using (bot)
open import BRA2.DerivTBounded using (DerivTBounded)
open import BRA2.IndBTContext0 using (IndBTContext0 ; plug0)
open import BRA2.FindIndBT using
  (IndBTPackageAt ; pkgE ; pkgV1 ; pkgV2 ; pkgWF
  ; pkgBase ; pkgStep ; pkgCtx
  ; IndBTPackage ; Or ; inl ; inr ; findIndBT)
open import BRA2.ExtractDemand using (Maybe ; just ; nothing)

------------------------------------------------------------------------
-- The core transform.

closedPipeline :
  {Target : Formula} ->
  (pkg : IndBTPackageAt Target) ->
  Eq (substEq zero O (pkgE pkg)) (pkgE pkg) ->
  O.DerivT0 Target
closedPipeline pkg inert =
  plug0 (pkgCtx pkg)
         (eqSubst (\ E -> O.DerivT0 (atomic E)) inert (pkgBase pkg))

------------------------------------------------------------------------
-- ClosedOracle: a partial decision procedure recognising those
-- equations on which we know  substEq zero O e = e .  Returns the
-- propositional witness when it does, nothing otherwise.

ClosedOracle : Set
ClosedOracle =
  (e : Equation) -> Maybe (Eq (substEq zero O e) e)

------------------------------------------------------------------------
-- Bot-target finalizer driven by a ClosedOracle.

closedFinalize :
  ClosedOracle ->
  Maybe (Or (O.DerivT0 bot) IndBTPackage) ->
  Maybe (O.DerivT0 bot)
closedFinalize _      nothing             = nothing
closedFinalize _      (just (inl d0))     = just d0
closedFinalize oracle (just (inr pkg))    =
  closedFinalizeStep oracle pkg (oracle (pkgE pkg))
  where
    closedFinalizeStep :
      ClosedOracle ->
      (pkg : IndBTPackage) ->
      Maybe (Eq (substEq zero O (pkgE pkg)) (pkgE pkg)) ->
      Maybe (O.DerivT0 bot)
    closedFinalizeStep _ _   nothing      = nothing
    closedFinalizeStep _ pkg (just inert) = just (closedPipeline pkg inert)

------------------------------------------------------------------------
-- Top-level pipeline:  DerivTBounded 1 l bot --> Maybe (DerivT0 bot)
-- driven by a ClosedOracle.  Composes  findIndBT  with
-- closedFinalize.

closedPipelineFromBounded :
  ClosedOracle ->
  {l : Nat} -> DerivTBounded (suc zero) l bot ->
  Maybe (O.DerivT0 bot)
closedPipelineFromBounded oracle d = closedFinalize oracle (findIndBT d)
