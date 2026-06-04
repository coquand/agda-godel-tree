{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SurpriseG2.SurpriseG2Final --
--
-- The headline theorem of the external-induction reformulation per
-- T4/clos .
--
-- =====================================================================
-- WHAT THIS FILE SHIPS.
-- =====================================================================
--
--   surpriseG2 :
--     (consts : SurpriseConstsConj) ->
--     Lt M N ->
--     StageStepSpec consts ->          -- the abstract inductive step
--     Deriv (eqF O (ap1 s O))           -- T |- 0 = 1
--
-- I.e., given the pigeonhole margin  M < N  and the abstract inductive
-- step  S(r) -> S(r+1) , derive  Deriv (0 = 1) .   The inductive step
-- is the principal mathematical residual ( see  T4.SurpriseG2.StageStepSpec
-- for the construction recipe per T4/clos ) .
--
-- =====================================================================
-- BODY.
-- =====================================================================
--
-- Apply  stageInd  at  r := suc N  to obtain  StagePred consts (suc N) ,
-- then apply at the EMPTY family ( the antecedent is vacuous since the
-- range  [suc N..N]  is empty ;  any  d  with  Lt (suc N) (suc d)  and
-- NatLe d N  is contradictory ) .

module T4.SurpriseG2.SurpriseG2Final where

open import T4.Base
open import BRA3.RuleInst2                  using ( NatLe )

open import T4.SurpriseG2.ConstantsConj   using ( SurpriseConstsConj )
open import T4.SurpriseG2.StagePred       using ( StagePred ; ProgPack ; DescribingFamily )
open import T4.SurpriseG2.StageBase       using ( natLe_lt_contra )
open import T4.SurpriseG2.StageStepSpec   using ( StageStepSpec )
open import T4.SurpriseG2.StageInd        using ( stageInd )
open import T4.SurpriseG2.MetaPigeonhole  as MP using ( Lt ; ltPred )

------------------------------------------------------------------------
-- The empty family at  r := suc N .

emptyFamily :
  (consts : SurpriseConstsConj) ->
  DescribingFamily consts (suc (SurpriseConstsConj.N consts))
emptyFamily consts d ltSNsd leDN =
  emptyElim (natLe_lt_contra d N leDN (ltPred ltSNsd))
  where
    N : Nat
    N = SurpriseConstsConj.N consts

------------------------------------------------------------------------
-- The headline theorem .

surpriseG2 :
  (consts : SurpriseConstsConj) ->
  Lt (SurpriseConstsConj.M consts) (SurpriseConstsConj.N consts) ->
  StageStepSpec consts ->
  Deriv (eqF O (ap1 s O))
surpriseG2 consts ltMN stepSpec =
  stageInd consts ltMN stepSpec (suc (SurpriseConstsConj.N consts))
           (emptyFamily consts)
