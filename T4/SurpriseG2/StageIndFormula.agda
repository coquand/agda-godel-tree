{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SurpriseG2.StageIndFormula --
--
-- External Nat-rec induction lifting the formula-level base case
-- (T4.SurpriseG2.StageBaseFormula.stageBaseF) up to  S(suc N)  via
-- the abstract  StageStepSpecF .   Mirrors  T4.SurpriseG2.StageInd
-- but at the FORMULA-LEVEL  StagePredF .

module T4.SurpriseG2.StageIndFormula where

open import T4.Base

open import T4.SurpriseG2.ConstantsConj   using ( SurpriseConstsConj )
open import T4.SurpriseG2.StagePredFormula
  using ( StagePredF ; StageStepSpecF )
open import T4.SurpriseG2.StageBaseFormula using ( stageBaseF )
open import T4.SurpriseG2.MetaPigeonhole as MP using ( Lt )

------------------------------------------------------------------------
-- stageIndF :  the external induction climbing  S(0) → S(1) → ... → S(r) .

stageIndF :
  (consts : SurpriseConstsConj) ->
  Lt (SurpriseConstsConj.M consts) (SurpriseConstsConj.N consts) ->
  StageStepSpecF consts ->
  (r : Nat) -> StagePredF consts r
stageIndF consts ltMN stepSpec zero    = stageBaseF consts ltMN
stageIndF consts ltMN stepSpec (suc r) =
  stepSpec r (stageIndF consts ltMN stepSpec r)
