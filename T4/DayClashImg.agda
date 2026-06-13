{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.DayClashImg -- the day-r clash, refactored onto IMAGE consistency.
--
-- Verbatim mirror of  T4.DayClashN  except that the consistency hypothesis is
-- the WEAKER  ConImage  ( T4.ConImageDef ) instead of  ConOpenInt , and the
-- single use
--     conH = ruleInst 0 (gFunN (vChaitin ...)) con
-- is replaced by the matching image instance
--     conH = conImg (vChaitin ...)            -- gFunN applied internally.
--
-- This is the machine-checked witness that the day clash NEVER needs global
-- consistency : only consistency of the diagonal program it itself builds.

open import T4.Base
open import BRA3.RuleInst2 using ( NatLe )
open import BRA3.Contrapositive using ( compI )
open import T4.ThmT using ( thmT )
open import T4.Code using ( codeFalse ; falseF )
open import T4.PHP using ( impFalseToNeg )
open import T4.Counting using ( negToImpFalse )
open import T4.ChaitinNumGIAbs using ( gFunN )
open import T4.ConImageDef using ( ConImage )
open import T4.SurpriseG2.BigConjFormula using ( countDays )
open import T4.StagePredFN using ( BigConjFormulaN ; StagePredFN ; PicksBound )

module T4.DayClashImg (Lstar : Nat) (picks : Nat -> Nat) where

open import T4.StageBase0N Lstar using ( N ; M )
open import T4.Step5bN  Lstar picks using ( vChaitin )
open import T4.KToFalseN Lstar picks using ( kToFalse )

dayClashImg :
  ConImage ->
  (r k : Nat) -> (kEq : Eq (suc k) (countDays N (suc r))) ->
  (rleN : NatLe r N) -> (Sr : StagePredFN N M r) -> (bound : PicksBound N M picks) ->
  Deriv (neg (BigConjFormulaN N (suc r) picks))
dayClashImg conImg r k kEq rleN Sr bound =
  let w : Term
      w = vChaitin r k kEq rleN Sr bound
      conH : Deriv (neg (eqF (ap1 thmT (gFunN w)) codeFalse))
      conH = conImg w
      conImp : Deriv (imp (eqF (ap1 thmT (gFunN w)) codeFalse) falseF)
      conImp = negToImpFalse (eqF (ap1 thmT (gFunN w)) codeFalse) conH
      impKfalse : Deriv (imp (BigConjFormulaN N (suc r) picks) falseF)
      impKfalse = compI (kToFalse r k kEq rleN Sr bound) conImp
  in impFalseToNeg (BigConjFormulaN N (suc r) picks) impKfalse
