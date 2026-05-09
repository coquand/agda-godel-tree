{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm.Parts.AxTreeEqLL
--
-- Self-contained dispatch material for the 0-arg primitive
--   axTreeEqLL : Deriv (ap2 TreeEq O O = O) .
--
-- Encoding has no payload (the primitive takes no arguments).

module BRA2.Thm.Parts.AxTreeEqLL where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.DerivThreshold
open import BRA2.Thm.Tag using (tagAxTreeEqLL)
open import BRA2.Thm.TagCodes
open import BRA2.Thm.EvalHelpers

------------------------------------------------------------------------
-- Encoded proof-tree input and intended Tree output.

encAxTreeEqLL : Tree
encAxTreeEqLL = nd (natCode tagAxTreeEqLL) lf

outAxTreeEqLL : Tree
outAxTreeEqLL = codeFormula (atomic (eqn (ap2 TreeEq O O) O))

------------------------------------------------------------------------
-- body_axTreeEqLL: 0 args; output = reify(outAxTreeEqLL), a closed constant.

body_axTreeEqLL : Fun2
body_axTreeEqLL = Lift (KT (reify outAxTreeEqLL))

------------------------------------------------------------------------
-- body_axTreeEqLL_eval.

abstract

  body_axTreeEqLL_eval : (b : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axTreeEqLL (ap2 Pair tagCode_axTreeEqLL O) b)
      (reify outAxTreeEqLL)))
  body_axTreeEqLL_eval b =
    liftKT_eval outAxTreeEqLL
                (codeFormula_isValue (atomic (eqn (ap2 TreeEq O O) O)))
                (ap2 Pair tagCode_axTreeEqLL O) b
