{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.UnifiedPipeline -- top-level dispatcher combining the closed
-- and open pipelines.
--
-- Given a  DerivTBounded 1 l bot  proof tree, we run  findIndBT  to
-- locate the topmost indBTB and accumulate its  IndBTContext0  path
-- to bot.  Two orthogonal strategies then dispatch on the package:
--
--   * Closed strategy (BRA2.ClosedPipeline): when  pkgE  is closed
--     in  var 0 , the indBT collapses to its base case ; we plug
--     pkgBase  through  pkgCtx  via plug0.  Driven by a ClosedOracle
--     that decides  Eq (substEq zero O e) e .
--
--   * Open strategy (BRA2.OpenPipeline): when  pkgCtx  contains an
--     extractable  inst zero t (hole _)  frame, the indBT step
--     machinery produces  DerivT0 (atomic (substEq zero t pkgE))
--     and we plug it through the remaining outer path.  Driven by
--     stripInstZeroHole.
--
-- The unified strategy: try CLOSED first (cheaper -- no step
-- machinery), fall back to OPEN if the oracle rejects pkgE.
-- Returns  nothing  only when both routes fail.
--
-- Coverage at this stage:
--   * Closed pkgE + ANY pkgCtx path                 : closed succeeds
--   * Open pkgE + pkgCtx with reachable inst-zero-hole : open succeeds
--   * Open pkgE + pkgCtx without inst-zero-hole       : both fail (nothing)
--
-- The third case is genuinely unsoundness-relevant: an open pkgE
-- whose path to bot contains no  inst zero  cannot be closed (an
-- open eqn cannot equal bot via structural rules alone).  So
-- "nothing" here is correct -- the input shape is incoherent.
-- (Modulo that ill-formed indBTBs may still slip through; see
-- BRA2.WellFormedIndBT and the doc's Case A.)

module BRA2.UnifiedPipeline where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
import BRA2.DerivT0       as O
import BRA2.DerivTBounded as B
open import BRA2.DerivT0 using (bot)
open import BRA2.DerivTBounded using (DerivTBounded)
open import BRA2.FindIndBT using
  (IndBTPackageAt ; pkgE ; pkgCtx
  ; IndBTPackage ; Or ; inl ; inr ; findIndBT)
open import BRA2.ClosedPipeline using (ClosedOracle ; closedPipeline)
open import BRA2.OpenPipeline   using (openPipeline)
open import BRA2.ExtractDemand  using (Maybe ; just ; nothing)

------------------------------------------------------------------------
-- Closed-then-open dispatcher on a single package.

unifiedFromPkg :
  ClosedOracle ->
  {Target : Formula} ->
  IndBTPackageAt Target ->
  Maybe (O.DerivT0 Target)
unifiedFromPkg oracle pkg =
  unifiedHelp oracle pkg (oracle (pkgE pkg))
  where
    unifiedHelp :
      ClosedOracle ->
      {Target : Formula} ->
      (pkg : IndBTPackageAt Target) ->
      Maybe (Eq (substEq zero O (pkgE pkg)) (pkgE pkg)) ->
      Maybe (O.DerivT0 Target)
    unifiedHelp _ pkg (just inert) = just (closedPipeline pkg inert)
    unifiedHelp _ pkg nothing      = openPipeline pkg

------------------------------------------------------------------------
-- Bot-target finalizer.

unifiedFinalize :
  ClosedOracle ->
  Maybe (Or (O.DerivT0 bot) IndBTPackage) ->
  Maybe (O.DerivT0 bot)
unifiedFinalize _      nothing             = nothing
unifiedFinalize _      (just (inl d0))     = just d0
unifiedFinalize oracle (just (inr pkg))    = unifiedFromPkg oracle pkg

------------------------------------------------------------------------
-- Top-level pipeline:  DerivTBounded 1 l bot --> Maybe (DerivT0 bot).

unifiedPipelineFromBounded :
  ClosedOracle ->
  {l : Nat} -> DerivTBounded (suc zero) l bot ->
  Maybe (O.DerivT0 bot)
unifiedPipelineFromBounded oracle d = unifiedFinalize oracle (findIndBT d)
