{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.FromBaseAndPair -- the user's case-split rule, derived from
-- ruleIndBT + axK + mp.
--
-- Given:
--    Deriv P[var 0 := O]                        -- the lf case
--    Deriv P[var 0 := ap2 Pair (var v1) (var v2)]  -- the Pair case
-- conclude:
--    Deriv P                                     -- with var 0 free.
--
-- This is ruleIndBT specialized to the case where the inductive step
-- doesn't actually depend on the IHs.  The two IHs are discarded via
-- two axK applications, leaving the bare Pair-case Deriv as the
-- conclusion under both implications.
--
-- Useful for shape-dispatched primitives like Fst/Snd whose Theorem 12
-- naturally splits into "lf-input" and "Pair-input" sub-proofs.

module BRA.FromBaseAndPair where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv

------------------------------------------------------------------------
-- fromBaseAndPair :
--   Given lf-case  Deriv P[0 := O]  and Pair-case  Deriv P[0 := nd v1 v2],
--   derive  Deriv P  by wrapping the Pair-case in two axK applications
--   to build the implication that ruleIndBT requires, then applying
--   ruleIndBT.
--
-- Type signature mirrors ruleIndBT's: P with var 0 free, fresh v1, v2.

fromBaseAndPair :
  (P : Formula) (v1 v2 : Nat) ->
  Deriv (substF zero O P) ->
  Deriv (substF zero (ap2 Pair (var v1) (var v2)) P) ->
  Deriv P
fromBaseAndPair P v1 v2 baseLf basePair =
  let
    -- The three substituted formulas appearing in ruleIndBT's step.
    Pv1 : Formula
    Pv1 = substF zero (var v1) P

    Pv2 : Formula
    Pv2 = substF zero (var v2) P

    Ppair : Formula
    Ppair = substF zero (ap2 Pair (var v1) (var v2)) P

    -- axK at (Ppair, Pv2):
    --   Deriv (Ppair imp (Pv2 imp Ppair))
    -- mp applied to basePair gives:
    --   Deriv (Pv2 imp Ppair)
    stepV2 : Deriv (Pv2 imp Ppair)
    stepV2 = mp (axK Ppair Pv2) basePair

    -- axK at (Pv2 imp Ppair, Pv1):
    --   Deriv ((Pv2 imp Ppair) imp (Pv1 imp (Pv2 imp Ppair)))
    -- mp applied to stepV2 gives:
    --   Deriv (Pv1 imp (Pv2 imp Ppair))
    stepFull : Deriv (Pv1 imp (Pv2 imp Ppair))
    stepFull = mp (axK (Pv2 imp Ppair) Pv1) stepV2

    -- ruleIndBT closes:
    --   Deriv (P[0 := O])
    --   Deriv (Pv1 imp (Pv2 imp Ppair))
    -- ⊢ Deriv P.
  in ruleIndBT P v1 v2 baseLf stepFull
