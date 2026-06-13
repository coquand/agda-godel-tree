{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.StageReachImg -- the external induction up to  S(N) , refactored onto
-- IMAGE consistency  ( T4.ConImageDef.ConImage ) .   Verbatim mirror of
-- T4.StageReachN , threading  conImg : ConImage  instead of  con : ConOpenInt
-- into each day clash  ( T4.DayClashImg.dayClashImg ) .

open import T4.Base
open import BRA3.RuleInst2 using ( NatLe ; le-refl ; le-suc-right )
open import T4.ConImageDef using ( ConImage )
open import T4.SurpriseG2.BigConjFormula using ( countDays )
open import T4.CountDaysLemmas using ( countDays_suc_step ; natLeSuc_to_Lt ; natLe_pred_left )
open import T4.StagePredFN using ( StagePredFN ; Picks ; PicksBound )
import T4.DayClashImg

module T4.StageReachImg (Lstar : Nat) (conImg : ConImage) where

open import T4.StageBase0N Lstar using ( N ; M ; stageBase0 )

------------------------------------------------------------------------
-- The inductive step  S(r) -> S(r+1)  for  r < N  ( i.e. suc r <= N ).

stageStepImg :
  (r : Nat) -> NatLe (suc r) N ->
  StagePredFN N M r -> StagePredFN N M (suc r)
stageStepImg r sucle Sr picks bound =
  T4.DayClashImg.dayClashImg Lstar picks conImg r (countDays N (suc (suc r)))
    (countDays_suc_step N r (natLeSuc_to_Lt r N sucle))
    (natLe_pred_left r N sucle) Sr bound

------------------------------------------------------------------------
-- Reach  S(j)  for every  j <= N , by meta-induction on  j .

reach : (j : Nat) -> NatLe j N -> StagePredFN N M j
reach zero     le = stageBase0
reach (suc j') le = stageStepImg j' le (reach j' (natLe_pred_left j' N le))

------------------------------------------------------------------------
-- S(N) .

stageN : StagePredFN N M N
stageN = reach N (le-refl N)
