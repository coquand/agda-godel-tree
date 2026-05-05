{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.Parts.AxIfLfLL
--
-- Proof-code vocabulary for safe-default axiom
--   axIfLfLL : Deriv (ap2 IfLf O O = O) .

module BRA.Thm.Parts.AxIfLfLL where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Thm.Tag using (tagAxIfLfLL)
open import BRA.Thm.TagCodes
open import BRA.Thm.EvalHelpers

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
    liftKT_eval outAxIfLfLL (ap2 Pair tagCode_axIfLfLL O) b
