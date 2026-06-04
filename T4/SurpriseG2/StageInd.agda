{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SurpriseG2.StageInd --
--
-- External induction in Agda Nat.rec from S(0) up to S(suc N) ,
-- threading the abstract  StageStepSpec  at each step .
--
-- =====================================================================
-- STATEMENT.
-- =====================================================================
--
--   stageInd :
--     (consts : SurpriseConstsConj) ->
--     Lt M N ->
--     StageStepSpec consts ->
--     (r : Nat) -> StagePred consts r
--
-- Given the base case ingredient ( pigeonhole ltMN ) and the abstract
-- inductive-step spec , produce  StagePred consts r  for every meta-Nat
-- r .   Used by  SurpriseG2Final  at  r := suc N  to apply at the
-- empty family .
--
-- =====================================================================
-- HOW IT IS BUILT.
-- =====================================================================
--
-- Straightforward Nat.rec  :
--   * r = 0     :  stageBase consts ltMN .
--   * r = suc r':  stepSpec r' (stageInd consts ltMN stepSpec r') .

module T4.SurpriseG2.StageInd where

open import T4.Base
open import T4.SurpriseG2.ConstantsConj   using ( SurpriseConstsConj )
open import T4.SurpriseG2.StagePred       using ( StagePred )
open import T4.SurpriseG2.StageBase       using ( stageBase )
open import T4.SurpriseG2.StageStepSpec   using ( StageStepSpec )
open import T4.SurpriseG2.MetaPigeonhole  as MP using ( Lt )

------------------------------------------------------------------------
-- The external induction .

stageInd :
  (consts : SurpriseConstsConj) ->
  Lt (SurpriseConstsConj.M consts) (SurpriseConstsConj.N consts) ->
  StageStepSpec consts ->
  (r : Nat) -> StagePred consts r
stageInd consts ltMN stepSpec zero    = stageBase consts ltMN
stageInd consts ltMN stepSpec (suc r) =
  stepSpec r (stageInd consts ltMN stepSpec r)
