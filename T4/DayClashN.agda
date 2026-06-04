{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.DayClashN -- clos STEP 6 :  consistency reflection  =>  not K .
--
--   dayClashN con r k ... :
--     Deriv (neg (BigConjFormulaN N (suc r) picks))      -- ~ K(x0, p(r+1),...,pN)
--
-- "if  T  were consistent ( ConOpenInt :  T  does not prove  0=1 ) and the days
-- [r+1..N] were jointly describable, then  T  proves  0=1  ( T4.KToFalseN.kToFalse )
-- -- contradiction ; hence not all describable".   This is the body of  S(r+1)
-- for the given  (picks, bound) ;  the inductive step  StageStepSpecFN  wraps it
-- with the  r > N  trueF-collapse ( totality ).   ConOpenInt is consumed HERE
-- ONCE ( clos's Eq.2 / the only undischarged hypothesis ).

open import T4.Base
open import BRA3.RuleInst2 using ( NatLe )
open import BRA3.Contrapositive using ( compI )
open import T4.ThmT using ( thmT )
open import T4.Code using ( codeFalse ; falseF )
open import T4.PHP using ( impFalseToNeg )
open import T4.Counting using ( negToImpFalse )
open import T4.ChaitinNumGIAbs using ( gFunN )
open import T4.SurpriseG2.ConOpenIntDef using ( ConOpenInt )
open import T4.SurpriseG2.BigConjFormula using ( countDays )
open import T4.StagePredFN using ( BigConjFormulaN ; StagePredFN ; PicksBound )

module T4.DayClashN (Lstar : Nat) (picks : Nat -> Nat) where

open import T4.StageBase0N Lstar using ( N ; M )
open import T4.Step5bN  Lstar picks using ( vChaitin )
open import T4.KToFalseN Lstar picks using ( kToFalse )

dayClashN :
  ConOpenInt ->
  (r k : Nat) -> (kEq : Eq (suc k) (countDays N (suc r))) ->
  (rleN : NatLe r N) -> (Sr : StagePredFN N M r) -> (bound : PicksBound N M picks) ->
  Deriv (neg (BigConjFormulaN N (suc r) picks))
dayClashN con r k kEq rleN Sr bound =
  let h : Term
      h = gFunN (vChaitin r k kEq rleN Sr bound)
      conH : Deriv (neg (eqF (ap1 thmT h) codeFalse))
      conH = ruleInst 0 h con
      conImp : Deriv (imp (eqF (ap1 thmT h) codeFalse) falseF)
      conImp = negToImpFalse (eqF (ap1 thmT h) codeFalse) conH
      impKfalse : Deriv (imp (BigConjFormulaN N (suc r) picks) falseF)
      impKfalse = compI (kToFalse r k kEq rleN Sr bound) conImp
  in impFalseToNeg (BigConjFormulaN N (suc r) picks) impKfalse
