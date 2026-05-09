{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm.Parts.AxFstLf
--
-- Self-contained dispatch material for safe-default axiom
--   axFstLf : Deriv (ap1 Fst O = O) .
--
-- Contents: encAxFstLf, outAxFstLf, body_axFstLf, body_axFstLf_eval.

module BRA2.Thm.Parts.AxFstLf where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.DerivThreshold
open import BRA2.Thm.Tag using (tagAxFstLf)
open import BRA2.Thm.TagCodes
open import BRA2.Thm.EvalHelpers

------------------------------------------------------------------------
-- Encoded proof-tree input and intended Tree output.

encAxFstLf : Tree
encAxFstLf = nd (natCode tagAxFstLf) lf

outAxFstLf : Tree
outAxFstLf = codeFormula (atomic (eqn (ap1 Fst O) O))

------------------------------------------------------------------------
-- body_axFstLf: 0 args; output = reify outAxFstLf, closed constant.

body_axFstLf : Fun2
body_axFstLf = Lift (KT (reify outAxFstLf))

------------------------------------------------------------------------
-- body_axFstLf_eval.

abstract

  body_axFstLf_eval : (b : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axFstLf (ap2 Pair tagCode_axFstLf O) b)
      (reify outAxFstLf)))
  body_axFstLf_eval b =
    liftKT_eval outAxFstLf
                (codeFormula_isValue (atomic (eqn (ap1 Fst O) O)))
                (ap2 Pair tagCode_axFstLf O) b
