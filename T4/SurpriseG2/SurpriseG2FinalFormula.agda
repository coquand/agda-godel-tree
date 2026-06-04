{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SurpriseG2.SurpriseG2FinalFormula --
--
-- The TOP-LEVEL theorem at the FORMULA-LEVEL  StagePredF .
--
-- =====================================================================
-- HEADLINE.
-- =====================================================================
--
--   surpriseG2F :
--     (consts : SurpriseConstsConj) ->
--     Lt (SurpriseConstsConj.M consts) (SurpriseConstsConj.N consts) ->
--     StageStepSpecF consts ->
--     Deriv (eqF O (ap1 s O))
--
-- Note : ConOpenInt is NOT a parameter here -- it lives INSIDE the
-- StageStepSpecF body ( per T4/clos lines 27-46 :  ConOpenInt is used
-- after the encoded_mp chain in the inductive step ) .
--
-- =====================================================================
-- BODY.
-- =====================================================================
--
-- Apply  stageIndF  at  r := suc N  to obtain  StagePredF consts (suc N) ;
-- the BigConjFormula at  r := suc N  has count = 0 (= empty conjunction
-- = trueF) via  countDays N (suc N) = 0 .   Apply at any picks ; the
-- result  Deriv (neg trueF)  combined with  axRefl O ( = Deriv trueF )
-- + axExFalso  gives  Deriv falseF = Deriv (eqF O (ap1 s O)) .

module T4.SurpriseG2.SurpriseG2FinalFormula where

open import T4.Base
open import BRA3.RuleInst2          using ( NatLe ; le-zero )
open import BRA3.Equational         using ( axRefl )
open import BRA3.Contrapositive     using ( axExFalso )
open import T4.Code               using ( falseF )

open import T4.SurpriseG2.ConstantsConj   using ( SurpriseConstsConj )
open import T4.SurpriseG2.BigConjFormula
  using ( BigConjFormula ; bigConjCount ; trueF ; countDays ; countAux )
open import T4.SurpriseG2.StagePredFormula
  using ( StagePredF ; StageStepSpecF ; Picks ; PicksBound )
open import T4.SurpriseG2.StageIndFormula using ( stageIndF )
open import T4.SurpriseG2.MetaPigeonhole as MP using ( Lt )

------------------------------------------------------------------------
-- Bridge :  countAux n n = zero  ( for any  n : Nat ) , and hence
-- countDays N (suc N) = 0 .

countAux_n_n : (n : Nat) -> Eq (countAux n n) zero
countAux_n_n zero    = refl
countAux_n_n (suc n) = countAux_n_n n

countDays_atSucN : (N : Nat) -> Eq (countDays N (suc N)) zero
countDays_atSucN N = countAux_n_n N

------------------------------------------------------------------------
-- Empty picks + trivial bound .

emptyPicks : Nat -> Nat
emptyPicks _ = zero

emptyBound : (consts : SurpriseConstsConj) -> PicksBound consts emptyPicks
emptyBound consts d _ = le-zero (SurpriseConstsConj.M consts)

------------------------------------------------------------------------
-- The headline .

surpriseG2F :
  (consts : SurpriseConstsConj) ->
  Lt (SurpriseConstsConj.M consts) (SurpriseConstsConj.N consts) ->
  StageStepSpecF consts ->
  Deriv (eqF O (ap1 s O))
surpriseG2F consts ltMN stepSpec =
  let N : Nat
      N = SurpriseConstsConj.N consts

      -- S(suc N) at any picks/bound .
      S_sN : StagePredF consts (suc N)
      S_sN = stageIndF consts ltMN stepSpec (suc N)

      -- Deriv (neg BigConjFormula consts (suc N) emptyPicks) .
      neg_bigConj_at_sN : Deriv (neg (BigConjFormula consts (suc N) emptyPicks))
      neg_bigConj_at_sN = S_sN emptyPicks (emptyBound consts)

      -- Bridge :  BigConjFormula consts (suc N) emptyPicks = bigConjCount enum (countDays N (suc N)) (suc N) emptyPicks .
      -- countDays N (suc N) = 0 ( via countDays_atSucN ) ;  bigConjCount enum 0 ... = trueF .
      -- So  BigConjFormula consts (suc N) emptyPicks = trueF  modulo the count bridge .

      enum : Fun1
      enum = SurpriseConstsConj.enum consts

      bridge : Eq (BigConjFormula consts (suc N) emptyPicks) trueF
      bridge =
        eqCong (\ c -> bigConjCount enum c (suc N) emptyPicks)
               (countDays_atSucN N)

      neg_trueF : Deriv (neg trueF)
      neg_trueF =
        eqSubst (\ F -> Deriv (neg F)) bridge neg_bigConj_at_sN

      -- Deriv trueF  via  axRefl O  ( trueF = eqF O O ) .
      trueD : Deriv trueF
      trueD = axRefl O

      -- axExFalso trueF falseF + trueD + neg_trueF  →  Deriv falseF .
      step1 : Deriv (imp (neg trueF) falseF)
      step1 = mp (axExFalso trueF falseF) trueD

      result : Deriv falseF
      result = mp step1 neg_trueF
  in result
