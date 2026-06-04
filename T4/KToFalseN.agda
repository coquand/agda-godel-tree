{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.KToFalseN -- clos Steps 5-6 at the big-conjunction antecedent :
--
--   kToFalse r k ... :
--     Deriv (imp (BigConjFormulaN N (suc r) picks)        -- K(x0, p(r+1),...,pN)
--                (eqF (ap1 thmT (gFunN (vChaitin ...)))    -- thmT( h x0 )
--                     codeFalse))                           -- = code( 0 = 1 )
--
-- = the reverse characterisation  K => Kr x0=O  ( T4.KrBridgeRevN.krBridgeRev )
-- precomposed with  T4.Step5bN.step5b  ( Kr x0=O => thmT(h x0)=code(0=1) ).
-- "if all of days [r+1..N] are jointly describable then  T  proves  0 = 1".

open import T4.Base
open import BRA3.RuleInst2 using ( NatLe )
open import BRA3.Contrapositive using ( compI )
open import T4.ThmT using ( thmT )
open import T4.Code using ( codeFalse )
open import T4.ChaitinNumGIAbs using ( gFunN )
open import T4.SurpriseG2.BigConjFormula using ( countDays )
open import T4.StagePredFN
  using ( bigConjCountN ; openFuel ; BigConjFormulaN ; StagePredFN ; PicksBound )

module T4.KToFalseN (Lstar : Nat) (picks : Nat -> Nat) where

open import T4.StageBase0N Lstar using ( N ; M )
open import T4.KrFoldN     picks using ( Kr )
open import T4.KrBridgeRevN picks using ( krBridgeRev )
open import T4.Step5bN     Lstar picks using ( vChaitin ; step5b )

kToFalse :
  (r k : Nat) -> (kEq : Eq (suc k) (countDays N (suc r))) ->
  (rleN : NatLe r N) -> (Sr : StagePredFN N M r) -> (bound : PicksBound N M picks) ->
  Deriv (imp (BigConjFormulaN N (suc r) picks)
             (eqF (ap1 thmT (gFunN (vChaitin r k kEq rleN Sr bound))) codeFalse))
kToFalse r k kEq rleN Sr bound =
  let br : Deriv (imp (bigConjCountN (suc k) (suc r) picks openFuel)
                      (eqF (ap1 (Kr r k) (var zero)) O))
      br = krBridgeRev (suc r) k
      br' : Deriv (imp (BigConjFormulaN N (suc r) picks)
                       (eqF (ap1 (Kr r k) (var zero)) O))
      br' = eqSubst
              (\ c -> Deriv (imp (bigConjCountN c (suc r) picks openFuel)
                                 (eqF (ap1 (Kr r k) (var zero)) O)))
              kEq br
  in compI br' (step5b r k kEq rleN Sr bound)
