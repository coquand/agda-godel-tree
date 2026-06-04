{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.StageReachN -- the external induction up to  S(N)  ( clos "by EXTERNAL
-- induction we prove S(r) for all r" ).
--
--   stageN : StagePredFN N M N         ( = S(N) )
--
-- Built from  S(0) ( T4.StageBase0N.stageBase0 )  by applying the day-r clash
-- ( T4.DayClashN.dayClashN ) for  r = 0,1,...,N-1 .   Every such  r  satisfies
-- r < N  ( the remaining conjunction  [r+1..N]  is non-empty ), so the clash's
-- index condition  suc k = countDays N (suc r)  is met by
-- k := countDays N (suc (suc r))  via  countDays_step .   The empty boundary
-- r = N  is NOT visited ( we only STEP up to  N , never past it ).
--
-- ConOpenInt is the single hypothesis ( consumed in each day's clash ).

open import T4.Base
open import BRA3.RuleInst2 using ( NatLe ; le-refl ; le-suc-right )
open import T4.SurpriseG2.ConOpenIntDef using ( ConOpenInt )
open import T4.SurpriseG2.BigConjFormula using ( countDays )
open import T4.CountDaysLemmas using ( countDays_suc_step ; natLeSuc_to_Lt ; natLe_pred_left )
open import T4.StagePredFN using ( StagePredFN ; Picks ; PicksBound )
import T4.DayClashN

module T4.StageReachN (Lstar : Nat) (con : ConOpenInt) where

open import T4.StageBase0N Lstar using ( N ; M ; stageBase0 )

------------------------------------------------------------------------
-- The inductive step  S(r) -> S(r+1)  for  r < N  ( i.e. suc r <= N ).

stageStepN :
  (r : Nat) -> NatLe (suc r) N ->
  StagePredFN N M r -> StagePredFN N M (suc r)
stageStepN r sucle Sr picks bound =
  T4.DayClashN.dayClashN Lstar picks con r (countDays N (suc (suc r)))
    (countDays_suc_step N r (natLeSuc_to_Lt r N sucle))
    (natLe_pred_left r N sucle) Sr bound

------------------------------------------------------------------------
-- Reach  S(j)  for every  j <= N , by meta-induction on  j .

reach : (j : Nat) -> NatLe j N -> StagePredFN N M j
reach zero     le = stageBase0
reach (suc j') le = stageStepN j' le (reach j' (natLe_pred_left j' N le))

------------------------------------------------------------------------
-- S(N) .

stageN : StagePredFN N M N
stageN = reach N (le-refl N)
