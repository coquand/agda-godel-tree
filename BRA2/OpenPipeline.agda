{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.OpenPipeline -- end-to-end pipeline for indBT-elimination
-- when  pkgE  has  var 0  free.
--
-- The closed-pkgE pipeline (BRA2.ClosedPipeline) suffices when the
-- indBT's underlying equation is closed in  var 0  -- pkgBase is
-- already a derivation of  atomic pkgE  (definitionally), and we
-- plug it through  pkgCtx  to reach Target.
--
-- For pkgE with  var 0  free, pkgBase only proves  atomic
-- (substEq zero O pkgE) , which is NOT atomic pkgE.  We need the
-- indBT step machinery (BRA2.StepCombinerFromStep + BRA2.UnfoldAtValue)
-- to derive  atomic (substEq zero t pkgE)  for some chosen value t .
-- This  t  is the closing term for the universal indBT claim;
-- pkgCtx must contain an  inst zero t  frame that closes the
-- equation by substituting  var 0 := t .
--
-- Strategy: locate an  inst zero t (hole _) refl  frame somewhere
-- in pkgCtx via  BRA2.StripInstZero.stripInstZeroHole .  When found,
-- the extracted  t  is the closing value, and the remaining outer
-- path (everything outside the inst, reindexed at  substF zero t P )
-- is the path from the eliminated equation to Target.
--
-- The pipeline:
--
--     unfoldAtValue (stepCombinerFromStep ... pkgStep) pkgBase t vt
--       :  DerivT0 (atomic (substEq zero t pkgE))
--       =  DerivT0 (substF zero t (atomic pkgE))
--
--     plug0 remainingCtx (above)  :  DerivT0 Target
--
-- Conservative restrictions inherited from  StripInstZero :
--   * Only an  inst zero t  frame whose inner is  hole _  is
--     extractable.  Wrapped inst (sym (inst _ _ ...)  etc. NOT here:
--     those are handled by the OUTER wrappers, not the inner).
--     The inst's inner being a non-hole context (an inner wrapper)
--     would require substEq composition reasoning -- deferred.

module BRA2.OpenPipeline where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
import BRA2.DerivT0       as O
import BRA2.DerivTBounded as B
open import BRA2.DerivT0 using (bot)
open import BRA2.DerivTBounded using (DerivTBounded)
open import BRA2.IndBTContext0 using (IndBTContext0 ; plug0)
open import BRA2.WellFormedIndBT
open import BRA2.UnfoldAtValue using (unfoldAtValue ; StepCombiner)
open import BRA2.StepCombinerFromStep using (stepCombinerFromStep)
open import BRA2.StripInstZero
  using (InstZeroExtract ; mkInstZeroExtract
        ; extractedT ; extractedTValue ; remainingCtx
        ; stripInstZeroHole)
open import BRA2.FindIndBT using
  (IndBTPackageAt ; pkgE ; pkgV1 ; pkgV2 ; pkgWF
  ; pkgBase ; pkgStep ; pkgCtx
  ; IndBTPackage ; Or ; inl ; inr ; findIndBT)
open import BRA2.ExtractDemand using (Maybe ; just ; nothing)

------------------------------------------------------------------------
-- Core: given a pkg whose pkgCtx has an extractable  inst zero t hole
-- frame, derive  DerivT0 Target  via indBT step machinery + plug0
-- on the remaining outer path.

openPipelineWithExtract :
  {Target : Formula} ->
  (pkg : IndBTPackageAt Target) ->
  InstZeroExtract (atomic (pkgE pkg)) Target ->
  O.DerivT0 Target
openPipelineWithExtract pkg ext =
  let stepC   : StepCombiner (pkgE pkg)
      stepC   = stepCombinerFromStep (pkgE pkg) (pkgV1 pkg) (pkgV2 pkg)
                  (fresh1 (pkgWF pkg)) (fresh2 (pkgWF pkg)) (distinct (pkgWF pkg))
                  (pkgStep pkg)
      elimAt  : O.DerivT0 (atomic (substEq zero (extractedT ext) (pkgE pkg)))
      elimAt  = unfoldAtValue (pkgE pkg) stepC (pkgBase pkg)
                                (extractedT ext) (extractedTValue ext)
  in plug0 (remainingCtx ext) elimAt

------------------------------------------------------------------------
-- Maybe-returning pipeline: stripInstZeroHole + openPipelineWithExtract.

openPipeline :
  {Target : Formula} ->
  (pkg : IndBTPackageAt Target) ->
  Maybe (O.DerivT0 Target)
openPipeline pkg = openPipelineHelp pkg (stripInstZeroHole (pkgCtx pkg))
  where
    openPipelineHelp :
      {Target : Formula} ->
      (pkg : IndBTPackageAt Target) ->
      Maybe (InstZeroExtract (atomic (pkgE pkg)) Target) ->
      Maybe (O.DerivT0 Target)
    openPipelineHelp _   nothing    = nothing
    openPipelineHelp pkg (just ext) = just (openPipelineWithExtract pkg ext)

------------------------------------------------------------------------
-- Bot-target finalizer driven by the open-pipeline strategy.

openFinalize :
  Maybe (Or (O.DerivT0 bot) IndBTPackage) ->
  Maybe (O.DerivT0 bot)
openFinalize nothing             = nothing
openFinalize (just (inl d0))     = just d0
openFinalize (just (inr pkg))    = openPipeline pkg

------------------------------------------------------------------------
-- Top-level pipeline:  DerivTBounded 1 l bot --> Maybe (DerivT0 bot)
-- via findIndBT + openFinalize.

openPipelineFromBounded :
  {l : Nat} -> DerivTBounded (suc zero) l bot ->
  Maybe (O.DerivT0 bot)
openPipelineFromBounded d = openFinalize (findIndBT d)
