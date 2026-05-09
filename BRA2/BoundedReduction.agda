{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.BoundedReduction -- Step-3 signature stub for bounded
-- cut-elimination on the threshold derivation type.
--
-- This file pins the *signature* of the bounded-reflection theorem
-- without yet committing to a proof.  The signature itself is the
-- publishable artifact:
--
--   "Any bounded-rank threshold derivation of bot can be reduced to
--    an open-fragment (induction-free) derivation of bot."
--
-- Equivalently, taking contrapositives:
--
--   "Open-fragment consistency  OpenCon0  implies  ConBounded r l
--    for every r, l."
--
-- We deliberately avoid  postulate  (the codebase is postulate-free).
-- Instead, we expose the bounded-reduction theorem as a Sigma type
-- (BoundedReductionTheorem) and parameterise the headline corollary
-- on it.  Filling in BoundedSoundBot is the goal of Step 3 in
-- BRA2/BOUNDED-REFLECTION-PLAN.md.
--
-- The intended structure is structural recursion on the bounded
-- derivation:
--   * leaf cases (axioms)            : same axiom in DerivT0;
--   * mp / ruleInst                  : recurse on premises;
--   * indBT / indBT2 (the only       : unfold induction up to depth r
--     non-trivial case)                via case-split on trees + mp.
--
-- The complexity measure is induction rank by default (per
-- BOUNDED-REFLECTION-PLAN Section 2); switch to checker rank or
-- reflection rank if the indBT case fails to go through.
--
-- Open technical questions (see plan Section 5):
--   Q1: What does "unfold indBT to depth r" produce in DerivT0?
--   Q2: Does the reduction commute with ruleInst and mp?
--   Q3: What is the size blow-up?  (Stays inside epsilon_3?)
--   Q4: Is the level index l necessary, or does r suffice?
--   Q5: What is the right base case (r=0, l=0)?

module BRA2.BoundedReduction where

open import BRA2.Base
open import BRA2.Formula
open import BRA2.DerivT0   using (DerivT0 ; bot)
open import BRA2.DerivTBounded using (DerivTBounded ; ConBounded)

------------------------------------------------------------------------
-- The Step-3 proof obligation, as a (curried) type.
--
-- "BoundedReductionTheorem" reads:
--   for every rank r, level l, every bounded-rank threshold derivation
--   of bot can be normalised to an induction-free DerivT0 derivation
--   of bot.

BoundedReductionTheorem : Set
BoundedReductionTheorem =
  (r l : Nat) -> DerivTBounded r l bot -> DerivT0 bot

------------------------------------------------------------------------
-- Open consistency.

OpenCon0 : Set
OpenCon0 = DerivT0 bot -> Empty

------------------------------------------------------------------------
-- Headline corollary.  Once BoundedSoundBot is supplied, open-fragment
-- consistency entails bounded consistency at every rank/level.
--
--   OpenCon0 -> forall r l, ConBounded r l .
--
-- Proof: contrapose BoundedSoundBot.

openCon0ToConBounded :
  BoundedReductionTheorem ->
  OpenCon0 -> (r l : Nat) -> ConBounded r l
openCon0ToConBounded reduce openCon r l dB =
  openCon (reduce r l dB)
