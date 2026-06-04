{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SurpriseG2.DayClash --
--
-- Wires the SHIPPED  StepFrontEnd.frontEnd  into the day-r clash, so the
-- IH  S(r)  is consumed HERE and the remaining residual is IH-free.
--
-- =====================================================================
-- WHAT THIS FILE SHIPS.
-- =====================================================================
--
--   dayClash :
--     (r : Nat) -> NatLe r N -> StagePredF consts r ->
--     (picks : Picks) -> PicksBound consts picks ->
--     Deriv (imp (BigConjFormula consts (suc r) picks) falseF)
--
-- given the single typed (IH-free) hypothesis
--
--   kdefClash :
--     (r : Nat) -> NatLe r N -> (picks : Picks) -> PicksBound consts picks ->
--     Deriv (imp K_rest (KdefBigConj M enum (natCode r))) ->   -- frontEnd output
--     Deriv (imp K_rest falseF)
--
-- where  K_rest = BigConjFormula consts (suc r) picks .
--
-- Construction:  dayClash r rleN IH picks bound =
--   kdefClash r rleN picks bound (frontEnd consts r rleN IH picks bound) .
--
-- =====================================================================
-- WHY THIS CUT.
-- =====================================================================
--
-- `frontEnd` (SHIPPED) turns the inductive hypothesis  S(r)  into the
-- OBJECT implication  "if days [r+1..N] are jointly describable then no
-- enumerated short program describes day r"  ( the per-program /
-- pigeonhole content of Kritchman-Raz step 3 ).   Threading it here
-- leaves  kdefClash  free of the IH and of  StagePredF , parametric only
-- in that object implication :  the pure "encoded clash" residual.
--
-- `kdefClash` IS dischargeable (it is the Chaitin core, à la the
-- shipped-but-unwired  StageStepCGI.cgiClashImpRf ) : encode the object
-- implication ( thmT_complete_rec ), Sigma1-lift the provability of the
-- Sigma1 antecedent  K_rest , push provability through to
-- KdefBigConj(r) via  encoded_mp , clash via the Chaitin diagonal, and
-- reflect inconsistency via  ConOpenInt .   See
-- T4/SURPRISE-GII-DAYCLASH-HANDOFF.md.

open import T4.Base
open import BRA3.RuleInst2          using ( NatLe )
open import T4.Code               using ( falseF )
open import T4.SurpriseG2.ConstantsConj   using ( SurpriseConstsConj )
open import T4.SurpriseG2.BigConjFormula  using ( BigConjFormula )
open import T4.SurpriseG2.KdefBigConj     using ( KdefBigConj )
open import T4.SurpriseG2.StepFrontEnd    using ( frontEnd )
open import T4.SurpriseG2.StagePredFormula using ( StagePredF ; Picks ; PicksBound )

module T4.SurpriseG2.DayClash
  (consts : SurpriseConstsConj)
  (kdefClash :
    (r : Nat) ->
    NatLe r (SurpriseConstsConj.N consts) ->
    (picks : Picks) -> PicksBound consts picks ->
    Deriv (imp (BigConjFormula consts (suc r) picks)
               (KdefBigConj (SurpriseConstsConj.M consts)
                            (SurpriseConstsConj.enum consts)
                            (natCode r))) ->
    Deriv (imp (BigConjFormula consts (suc r) picks) falseF))
  where

dayClash :
  (r : Nat) ->
  NatLe r (SurpriseConstsConj.N consts) ->
  StagePredF consts r ->
  (picks : Picks) -> PicksBound consts picks ->
  Deriv (imp (BigConjFormula consts (suc r) picks) falseF)
dayClash r rleN IH picks bound =
  kdefClash r rleN picks bound (frontEnd consts r rleN IH picks bound)
