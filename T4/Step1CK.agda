{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.Step1CK -- clos Step 1 + the enum-correctness bridge ( clos lines 33-40 ),
-- composed :  S(r)  =>  "K_rest  =>  K(r) > L*"  ( the single CK-atom ).
--
--   frontEndCK :
--     S(r) -> (picks,bound) ->
--     Deriv (imp (BigConjFormula consts (suc r) picks)            -- K_rest @ x0
--                (neg (eqF (ap2 (CK enum M) (natCode r) (var 1)) O)))   -- K(r) > L*  @ x1
--
-- = impTrans  frontEnd2  ( clos Step 1, the run-monotone front end )  with
-- incBridge  ( clos lines 38-40, "by enum correctness" ).   This is the input
-- to clos Steps 2-6 ( encode + num at x0, mp, thm13, Chaitin G on the CK-atom,
-- consistency ).

module T4.Step1CK where

open import T4.Base
open import BRA3.RuleInst2 using ( NatLe )
open import BRA3.Logic     using ( impTrans )
open import T4.CKProg      using ( CK )
open import T4.SurpriseG2.ConstantsConj    using ( SurpriseConstsConj )
open import T4.SurpriseG2.BigConjFormula   using ( BigConjFormula )
open import T4.SurpriseG2.StagePredFormula using ( StagePredF ; Picks ; PicksBound )
open import T4.StepFrontEnd2 using ( frontEnd2 )
open import T4.EnumCorrBridge using ( incBridge )

frontEndCK :
  (consts : SurpriseConstsConj) (r : Nat) ->
  NatLe r (SurpriseConstsConj.N consts) ->
  StagePredF consts r ->
  (picks : Picks) (bound : PicksBound consts picks) ->
  Deriv (imp (BigConjFormula consts (suc r) picks)
             (neg (eqF (ap2 (CK (SurpriseConstsConj.enum consts) (SurpriseConstsConj.M consts))
                            (natCode r) (var (suc zero))) O)))
frontEndCK consts r rleN Sr picks bound =
  impTrans (frontEnd2 consts r rleN Sr picks bound)
           (incBridge (SurpriseConstsConj.enum consts) (SurpriseConstsConj.M consts) r)
