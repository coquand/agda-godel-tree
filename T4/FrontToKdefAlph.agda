{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.FrontToKdefAlph -- Task B of  T4/SURPRISE-GII-FINISH-HANDOFF.md , at the
-- concrete  CKMargin  constants.   Composes the IH-free fuel shift
-- ( T4.MonoShift.monoShift , clos "by monotonicity of run" ) with the
-- front-end -> Chaitin-core junction ( T4.CoverBridgeAlph.coverBridgeKdefAlph )
-- to turn the day- r  frontEnd output that  kdefClash  receives into the open
-- checkAlphN -guarded K-formula  KdefAlph (natCode r)  the Chaitin closer
-- ( T4.CgFalseImpAlph ) diagonalises:
--
--   frontToKdefAlph r picks dComp :
--     Deriv (imp (BigConjFormula consts (suc r) picks) (KdefAlph (natCode r)))
--
-- IH-free ( no  StagePredF , no  bound ) -- exactly the hypotheses  kdefClash
-- has in hand.

open import T4.Base
open import BRA3.ChurchLeq      using ( leq )
open import T4.KGodel1BridgeDef using ( Lstar )

module T4.FrontToKdefAlph
  (Lstar_meta : Nat)
  (lstarLe    : Deriv (leq (natCode Lstar_meta) Lstar))
  where

open import T4.CKMargin Lstar_meta lstarLe using ( N ; M ; enum ; Bnat ; Bpos ; predEq )
open import T4.SurpriseG2.ConstantsConj    using ( SurpriseConstsConj )
open import T4.SurpriseG2.BigConjFormula   using ( BigConjFormula )
open import T4.SurpriseG2.StagePredFormula using ( Picks )
open import T4.SurpriseG2.KdefBigConj      using ( KdefBigConj )
open import T4.MonoShift                   using ( monoShift )
open import T4.KdefAlph Lstar_meta         using ( KdefAlph )
open import T4.CoverBridgeAlph Lstar_meta  using ( coverBridgeKdefAlph )
open import BRA3.Contrapositive            using ( compI )

------------------------------------------------------------------------
-- The concrete surprise-G2 constants ( N := Bnat , M := Bnat-1 , enum ).

consts : SurpriseConstsConj
consts = record { N = N ; M = M ; enum = enum }

------------------------------------------------------------------------
-- Task B :  frontEnd output ( fuel var 0 )  ==>  open  KdefAlph (natCode r) .

frontToKdefAlph :
  (r : Nat) (picks : Picks) ->
  Deriv (imp (BigConjFormula consts (suc r) picks)
             (KdefBigConj M enum (natCode r))) ->
  Deriv (imp (BigConjFormula consts (suc r) picks) (KdefAlph (natCode r)))
frontToKdefAlph r picks dComp =
  compI (monoShift consts r picks dComp)
        (coverBridgeKdefAlph M r (predEq Bnat Bpos))
