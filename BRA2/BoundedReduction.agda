{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.BoundedReduction -- Step-3 signatures and decompositions for
-- bounded cut-elimination on the threshold derivation type.
--
-- The publishable claim is:
--
--   "Any bounded-rank threshold derivation of bot can be reduced to
--    an open-fragment (induction-free) derivation of bot."
--
-- We pin this claim as a Sigma type (BoundedReductionTheorem) so the
-- file remains  --safe  and postulate-free.  The body of the theorem
-- (the technical heart of Step 3 in BRA2/BOUNDED-REFLECTION-PLAN.md)
-- is decomposed into two pieces:
--
--   (1)  RankDecrement   : (r : Nat) -> ... -> rank-(suc r) -> rank-r
--        the *single indBT-elimination step* --- the actual hard part
--   (2)  rankZero        : rank-0 -> DerivT0
--        the trivial base case (already proved in
--        BRA2.BoundedReductionRankZero)
--
-- Composing (1) by induction on r and discharging the base via (2)
-- produces  BoundedReductionTheorem .  This decomposition is the
-- main constructive content of this file.
--
-- Open technical questions (see plan Section 5):
--   Q1: What does "unfold indBT to depth r" produce in DerivT0?
--   Q2: Does the reduction commute with ruleInst and mp?
--   Q3: What is the size blow-up?  (Stays inside epsilon_3?)
--   Q4: Is the level index l necessary, or does r suffice?
--   Q5: What is the right base case (r=0, l=0)?  -- ANSWERED:
--       see BRA2.BoundedReductionRankZero.

module BRA2.BoundedReduction where

open import BRA2.Base
open import BRA2.Formula
open import BRA2.DerivT0       using (DerivT0 ; bot)
open import BRA2.DerivTBounded using (DerivTBounded ; ConBounded)
import BRA2.DerivTBounded as B
open import BRA2.BoundedReductionRankZero using (rankZero)

------------------------------------------------------------------------
-- The Step-3 proof obligation, as a curried type.

BoundedReductionTheorem : Set
BoundedReductionTheorem =
  (r l : Nat) -> DerivTBounded r l bot -> DerivT0 bot

------------------------------------------------------------------------
-- The single rank-decrement obligation.
--
-- "Eliminate one layer of  indBT  /  indBT2  in a bounded-rank proof
--  of bot, producing a strictly-smaller-rank proof of bot at some
--  (possibly larger) level."
--
-- This is the genuine bounded-cut-elimination step.  Strategy in
-- BRA2/BOUNDED-REFLECTION-PLAN.md Section 3 Step 3: identify the
-- topmost  indBT  in the proof tree and unfold it via a finite
-- case-split on trees, combined with mp-chains, all in
-- DerivTBounded r l' bot for some l'.

RankDecrement : Set
RankDecrement =
  (r : Nat) {l : Nat} ->
  DerivTBounded (suc r) l bot ->
  Sigma Nat (\ l' -> DerivTBounded r l' bot)

------------------------------------------------------------------------
-- Composition: RankDecrement implies the full BoundedReductionTheorem.
--
-- Proof: structural induction on the rank index r.
--   r = 0:        directly apply rankZero (BoundedReductionRankZero).
--   r = suc r':   apply the decrement once, recurse on the smaller
--                 rank.

boundedReductionFromRankDecrement :
  RankDecrement -> BoundedReductionTheorem
boundedReductionFromRankDecrement decr = go
  where
    go : (r l : Nat) -> DerivTBounded r l bot -> DerivT0 bot
    go zero    l d = rankZero d
    go (suc r) l d =
      let pair = decr r d
      in go r (fst pair) (snd pair)

------------------------------------------------------------------------
-- Open consistency.

OpenCon0 : Set
OpenCon0 = DerivT0 bot -> Empty

------------------------------------------------------------------------
-- Headline corollary.  Open-fragment consistency entails bounded
-- consistency at every rank/level, modulo the rank-decrement
-- obligation.

openCon0ToConBounded :
  BoundedReductionTheorem ->
  OpenCon0 -> (r l : Nat) -> ConBounded r l
openCon0ToConBounded reduce openCon r l dB =
  openCon (reduce r l dB)

-- Convenience composition: rank-decrement directly implies the
-- bounded-consistency-from-open-consistency corollary.

openCon0ToConBoundedFromDecrement :
  RankDecrement ->
  OpenCon0 -> (r l : Nat) -> ConBounded r l
openCon0ToConBoundedFromDecrement decr =
  openCon0ToConBounded (boundedReductionFromRankDecrement decr)
