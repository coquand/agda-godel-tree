{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.KrToQ0N -- clos Step 1 with the day-count  N  and program-margin  M
-- INSTANTIATED from  L*  ( N := Bnat = #programs of size <= L* ,  M := Bnat - 1 ;
-- T4.StageBase0N ).
--
--   krToQ0 : (r k) -> Eq (suc k) (countDays N (suc r)) -> NatLe r N ->
--            StagePredFN N M r -> (bound) ->
--     Deriv (imp (eqF (ap1 (Kr r k) (var zero)) O) (KdefBigConjNF F1 M r))
--
-- = T4.KrToQN.krToQN  specialised at the concrete  (N, M) , so the surprise count
-- is tied to  L*  and  S(0)  ( T4.StageBase0N.stageBase0 ) needs no  Lt M N
-- hypothesis.

open import T4.Base
open import BRA3.RuleInst2 using ( NatLe )
open import T4.SurpriseG2.BigConjFormula using ( countDays )
open import T4.StagePredFN using ( StagePredFN ; PicksBound )
open import T4.StepFrontEnd2N using ( KdefBigConjNF ; F1 )

module T4.KrToQ0N (Lstar : Nat) (picks : Nat -> Nat) where

open import T4.StageBase0N Lstar using ( N ; M )
open import T4.KrFoldN picks using ( Kr )
open import T4.KrToQN  picks using ( krToQN )

krToQ0 :
  (r k : Nat) -> Eq (suc k) (countDays N (suc r)) ->
  NatLe r N -> StagePredFN N M r ->
  (bound : PicksBound N M picks) ->
  Deriv (imp (eqF (ap1 (Kr r k) (var zero)) O) (KdefBigConjNF F1 M r))
krToQ0 r k kEq rleN Sr bound = krToQN N M r k kEq rleN Sr bound
