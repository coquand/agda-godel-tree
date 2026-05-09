{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm.Parts.AxIfLfLL
--
-- Proof-code vocabulary for safe-default axiom
--   axIfLfLL : Deriv (ap2 IfLf O O = O) .

module BRA2.Thm.Parts.AxIfLfLL where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.DerivThreshold
open import BRA2.Thm.Tag using (tagAxIfLfLL)
open import BRA2.Thm.TagCodes
open import BRA2.Thm.EvalHelpers

encAxIfLfLL : Tree
encAxIfLfLL = nd (natCode tagAxIfLfLL) lf

outAxIfLfLL : Tree
outAxIfLfLL = codeFormula (atomic (eqn (ap2 IfLf O O) O))

body_axIfLfLL : Fun2
body_axIfLfLL = Lift (KT (reify outAxIfLfLL))

abstract

  body_axIfLfLL_eval : (b : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axIfLfLL (ap2 Pair tagCode_axIfLfLL O) b)
      (reify outAxIfLfLL)))
  body_axIfLfLL_eval b =
    liftKT_eval outAxIfLfLL
                (codeFormula_isValue (atomic (eqn (ap2 IfLf O O) O)))
                (ap2 Pair tagCode_axIfLfLL O) b
