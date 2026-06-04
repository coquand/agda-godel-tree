{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SurpriseG2.StagePredFormula --
--
-- FORMULA-LEVEL  S(r)  per [[feedback_no_meta_to_imp_primitive_needed]]
-- and T4/clos lines 11-15 .
--
-- =====================================================================
-- WHAT THIS FILE SHIPS.
-- =====================================================================
--
-- *  `Picks = Nat -> Nat`            -- the per-day program-index choice .
-- *  `PicksBound consts picks`       -- bound  picks d <= M  for  d <= N .
-- *  `StagePredF consts r`           -- the FORMULA-LEVEL per-stage Deriv :
--
--      StagePredF consts r =
--        (picks : Picks) (bound : PicksBound consts picks) ->
--        Deriv (neg (BigConjFormula consts r picks))
--
--   This is the "S(r)" of clos lines 11-15 :  an UNCONDITIONAL Deriv of
--   the negated big-conjunction , parameterized over the (META) choice
--   of programs at each day .
--
-- =====================================================================
-- WHY THIS IS THE RIGHT SHAPE.
-- =====================================================================
--
-- A meta function `family -> Deriv 0=1`  would require a primitive
-- transforming meta `Deriv A -> Deriv B`  to formula-level `Deriv (imp A B)` ,
-- which BRA does NOT have  ( see [[feedback_no_meta_to_imp_primitive_needed]] ) .
-- The FORMULA-LEVEL shape avoids this : `S(r)` is itself a Deriv of an
-- implication ( unfolded via the And-encoding `A /\ B = neg (imp A (neg B))` ) ,
-- so the classical And-laws ( T4.SurpriseG2.AndLemmas ) give the
-- per-program negs directly , and the inductive step body composes via
-- Hilbert combinators + encoded_mp + lifted CGI .

module T4.SurpriseG2.StagePredFormula where

open import T4.Base
open import BRA3.RuleInst2          using ( NatLe )

open import T4.SurpriseG2.ConstantsConj   using ( SurpriseConstsConj )
open import T4.SurpriseG2.BigConjFormula  using ( BigConjFormula )

------------------------------------------------------------------------
-- The per-day picks function and its bound .

Picks : Set
Picks = Nat -> Nat

PicksBound : SurpriseConstsConj -> Picks -> Set
PicksBound consts picks =
  (d : Nat) -> NatLe d (SurpriseConstsConj.N consts) ->
    NatLe (picks d) (SurpriseConstsConj.M consts)

------------------------------------------------------------------------
-- The formula-level S(r) :  Deriv (neg BigConj) for any (picks, bound) .

StagePredF : SurpriseConstsConj -> Nat -> Set
StagePredF consts r =
  (picks : Picks) (bound : PicksBound consts picks) ->
    Deriv (neg (BigConjFormula consts r picks))

------------------------------------------------------------------------
-- The abstract inductive-step spec at the FORMULA-LEVEL hypothesis .

StageStepSpecF : SurpriseConstsConj -> Set
StageStepSpecF consts =
  (r : Nat) -> StagePredF consts r -> StagePredF consts (suc r)
