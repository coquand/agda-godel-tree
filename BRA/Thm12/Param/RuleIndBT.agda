{-# OPTIONS --safe --without-K --exact-split #-}

module BRA.Thm12.Param.RuleIndBT where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Thm.ThmT
  using ( thmT ; tagCode_ruleIndBT ; thmTDispRuleIndBT_param )

parEncRuleIndBT : Formula -> Nat -> Nat -> Term -> Term -> Term
parEncRuleIndBT P v1 v2 y_base_T y_step_T =
  ap2 Pair tagCode_ruleIndBT
    (ap2 Pair (reify (codeFormula P))
      (ap2 Pair (reify (code (var v1)))
        (ap2 Pair (reify (code (var v2)))
          (ap2 Pair y_base_T y_step_T))))

parOutRuleIndBT : Formula -> Term
parOutRuleIndBT P = reify (codeFormula P)

parDispRuleIndBT : (P : Formula) (v1 v2 : Nat) (y_base_T y_step_T : Term) ->
  Deriv (atomic (eqn (ap1 thmT (parEncRuleIndBT P v1 v2 y_base_T y_step_T))
                     (parOutRuleIndBT P)))
parDispRuleIndBT P v1 v2 y_base_T y_step_T =
  thmTDispRuleIndBT_param P v1 v2 y_base_T y_step_T
