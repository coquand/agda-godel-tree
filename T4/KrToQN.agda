{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.KrToQN -- the TWO-FUEL clos Step 1 with the clean atom antecedent :
--
--   krToQN : (N M r k) -> Eq (suc k) (countDays N (suc r)) ->
--            NatLe r N -> StagePredFN N M r -> (bound) ->
--     Deriv (imp (eqF (ap1 (Kr r k) (var zero)) O)     -- Kr x0 = O  ( x0 = var 0 )
--                (KdefBigConjNF F1 M r))                -- Q(x1)      ( x1 = var 1 = F1 )
--
-- "from  S(r) :  Kr x0 = O  =>  K(r) > L*  at the INDEPENDENT free fuel  x1 ".
-- = the conj-bridge  T4.KrBridgeN.krBridgeN  ( Kr x0=O => K_rest @ x0 ) precomposed
-- with the two-fuel  T4.StepFrontEnd2N.frontEnd2N  ( K_rest @ x0 => Q @ x1 ).

open import T4.Base
open import BRA3.RuleInst2 using ( NatLe )
open import BRA3.Contrapositive using ( compI )
open import T4.SurpriseG2.BigConjFormula using ( countDays )
open import T4.StagePredFN
  using ( bigConjCountN ; openFuel ; BigConjFormulaN ; StagePredFN ; PicksBound )
open import T4.StepFrontEnd2N using ( frontEnd2N ; KdefBigConjNF ; F1 )

module T4.KrToQN (picks : Nat -> Nat) where

open import T4.KrFoldN   picks using ( Kr )
open import T4.KrBridgeN picks using ( krBridgeN )

krToQN :
  (N M r k : Nat) -> Eq (suc k) (countDays N (suc r)) ->
  NatLe r N -> StagePredFN N M r ->
  (bound : PicksBound N M picks) ->
  Deriv (imp (eqF (ap1 (Kr r k) (var zero)) O) (KdefBigConjNF F1 M r))
krToQN N M r k kEq rleN Sr bound =
  let br : Deriv (imp (eqF (ap1 (Kr r k) (var zero)) O)
                      (bigConjCountN (suc k) (suc r) picks openFuel))
      br = krBridgeN (suc r) k
      br' : Deriv (imp (eqF (ap1 (Kr r k) (var zero)) O)
                       (BigConjFormulaN N (suc r) picks))
      br' = eqSubst
              (\ c -> Deriv (imp (eqF (ap1 (Kr r k) (var zero)) O)
                                 (bigConjCountN c (suc r) picks openFuel)))
              kEq br
      fe : Deriv (imp (BigConjFormulaN N (suc r) picks) (KdefBigConjNF F1 M r))
      fe = frontEnd2N picks N M r rleN Sr bound
  in compI br' fe
