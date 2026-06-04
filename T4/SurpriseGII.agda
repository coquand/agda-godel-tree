{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SurpriseGII -- the TOP-LEVEL surprise-Goedel-II headline.
--
-- =====================================================================
-- GOAL (see T4/SURPRISE-GII-HANDOFF.md section 0).
-- =====================================================================
--
--   surpriseGII : ConOpenInt -> Deriv (eqF O (ap1 s O))
--
-- "from open-interval consistency, T proves 0 = 1" -- the formalized
-- Goedel II / Chaitin surprise-exam descent, on Track A (the shipped
-- BigConjFormula / count-m framework, faithful to Kritchman-Raz).
--
-- =====================================================================
-- STATUS / STRUCTURE (this file = MILESTONE 1 of task (d)).
-- =====================================================================
--
-- Per the repo STOP-rule (hypothesis-first; cf. the old BerryDataConj /
-- DescFamConj), the genuine long pole -- the per-step Chaitin clash and
-- its enum-identification -- is isolated as a TYPED hypothesis
--
--   stageStepF : ConOpenInt -> StageStepSpecF consts
--
-- (a module parameter), so the headline TYPECHECKS against it via the
-- shipped  surpriseG2F  before the body is built.  Subsequent milestones
-- replace this parameter with the real construction
-- ( T4.SurpriseG2.StageStepF , built from cgiClashConj + KR p.5 items
-- 1-7 ) and discharge it last.
--
-- The CONCRETE constants are instantiated from  T4.CKMargin :
--   N := Bnat ,  M := Bnat - 1 ,  enum := T4.EnumProg.enum ,
--   ltMN := CKMargin.ltMN .
-- The  Lstar_meta <-> Lstar  bridge ( ENUM-SHIPPED.md residual #1 ) is
-- carried as the explicit parameter  lstarLe , discharged at the
-- concrete  Lstar_meta  in the final wireup.

open import T4.Base
open import BRA3.ChurchLeq        using ( leq )
open import T4.KGodel1BridgeDef   using ( Lstar )

-- Lstar_meta : the abstract size budget ; lstarLe : the residual-#1 bridge.
module T4.SurpriseGII
  (Lstar_meta : Nat)
  (lstarLe    : Deriv (leq (natCode Lstar_meta) Lstar))
  where

open import BRA3.RuleInst2          using ( NatLe )
open import T4.Code               using ( falseF )
open import T4.SurpriseG2.ConstantsConj   using ( SurpriseConstsConj )
open import T4.SurpriseG2.ConOpenIntDef    using ( ConOpenInt )
open import T4.SurpriseG2.BigConjFormula  using ( BigConjFormula )
open import T4.SurpriseG2.KdefBigConj     using ( KdefBigConj )
open import T4.SurpriseG2.StagePredFormula using ( StagePredF ; Picks ; PicksBound )
import T4.SurpriseG2.StageStepF
import T4.SurpriseG2.DayClash
open import T4.SurpriseG2.SurpriseG2FinalFormula using ( surpriseG2F )
open import T4.SurpriseG2.MetaPigeonhole as MP using ( Lt )

-- The concrete margin + enumerator ( N := Bnat , M := Bnat-1 , ltMN ).
open import T4.CKMargin Lstar_meta lstarLe
  using ( N ; M ; enum ; ltMN )

------------------------------------------------------------------------
-- The concrete surprise-G2 constants.

consts : SurpriseConstsConj
consts = record { N = N ; M = M ; enum = enum }

------------------------------------------------------------------------
-- The remaining residual, isolated as a typed hypothesis : the day-r
-- Chaitin clash ( KR p.5 items 1-7 distilled to an implication ).
-- Built ( with the enum-identification ) + discharged in later milestones.

-- The IH-free "encoded clash" residual : given  frontEnd 's object
-- implication  imp K_rest (KdefBigConj M enum (natCode r)) , derive
-- imp K_rest falseF  ( = the Chaitin diagonal + Sigma1 lift + ConOpenInt
-- reflection ).   This is the genuine long pole ;  see
-- T4/SURPRISE-GII-DAYCLASH-HANDOFF.md.
KdefClash : Set
KdefClash =
  ConOpenInt ->
  (r : Nat) -> NatLe r N ->
  (picks : Picks) -> PicksBound consts picks ->
  Deriv (imp (BigConjFormula consts (suc r) picks) (KdefBigConj M enum (natCode r))) ->
  Deriv (imp (BigConjFormula consts (suc r) picks) falseF)

------------------------------------------------------------------------
-- The headline, parametric in the (IH-free) encoded-clash hypothesis.
-- frontEnd is wired in by  T4.SurpriseG2.DayClash ;  the inductive
-- scaffold by  T4.SurpriseG2.StageStepF .

module _ (kdefClash : KdefClash) where

  surpriseGII : ConOpenInt -> Deriv (eqF O (ap1 s O))
  surpriseGII con =
    surpriseG2F consts ltMN
      (T4.SurpriseG2.StageStepF.stageStepF consts
        (T4.SurpriseG2.DayClash.dayClash consts (kdefClash con)))
