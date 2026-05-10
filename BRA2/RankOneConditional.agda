{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.RankOneConditional -- conditional rank-1 decrement, the
-- partial fragment of  BoundedReduction.RankDecrement  at  r = 0 .
--
-- BoundedReduction.RankDecrement is the rank-induction step in the
-- bounded cut-elimination programme:
--
--   RankDecrement = (r : Nat) {l : Nat} ->
--                    DerivTBounded (suc r) l bot ->
--                    Sigma Nat (\ l' -> DerivTBounded r l' bot)
--
-- For the rank-1 case  (r = 0) , this file delivers a CONDITIONAL
-- version that returns  Maybe (Sigma Nat ...)  -- when the unified
-- find-and-extract pipeline finds and resolves a topmost indBT,
-- the rank-1 input reduces to a rank-0 output ; otherwise the
-- pipeline yields  nothing  and we propagate.
--
-- The conditional aspect captures the doc's three "nothing" sources:
--   (Case A) ill-formed indBTB instances (alpha-renaming deferred).
--   (Case C-extension) inst frames with non-hole inner.
--   (indBT2B) the binary-tree-2 induction case.
--
-- Composition:
--     unifiedPipelineFromBounded oracle d  :  Maybe (DerivT0 bot)
--     map (embedDerivT0)           ......   :  Maybe (Sigma Nat (... DerivTBounded 0 l' bot))

module BRA2.RankOneConditional where

open import BRA2.Base
open import BRA2.DerivT0       using (DerivT0 ; bot)
open import BRA2.DerivTBounded using (DerivTBounded)
open import BRA2.UnifiedPipeline using (unifiedPipelineFromBounded)
open import BRA2.ClosedPipeline  using (ClosedOracle ; defaultClosedOracle)
open import BRA2.EmbedDerivT0    using (embedDerivT0)
open import BRA2.ExtractDemand   using (Maybe ; just ; nothing)

------------------------------------------------------------------------
-- Conditional rank-1 decrement signature.

RankOneConditional : Set
RankOneConditional =
  ClosedOracle ->
  {l : Nat} ->
  DerivTBounded (suc zero) l bot ->
  Maybe (Sigma Nat (\ l' -> DerivTBounded zero l' bot))

------------------------------------------------------------------------
-- Implementation: pipeline + embed.

rankOneConditional : RankOneConditional
rankOneConditional oracle d =
  rankOneFromMaybe (unifiedPipelineFromBounded oracle d)
  where
    rankOneFromMaybe :
      Maybe (DerivT0 bot) ->
      Maybe (Sigma Nat (\ l' -> DerivTBounded zero l' bot))
    rankOneFromMaybe nothing   = nothing
    rankOneFromMaybe (just d0) = just (embedDerivT0 d0)

------------------------------------------------------------------------
-- Default-oracle specialisation: the most useful concrete instance.

rankOneConditionalDefault :
  {l : Nat} ->
  DerivTBounded (suc zero) l bot ->
  Maybe (Sigma Nat (\ l' -> DerivTBounded zero l' bot))
rankOneConditionalDefault d = rankOneConditional defaultClosedOracle d
