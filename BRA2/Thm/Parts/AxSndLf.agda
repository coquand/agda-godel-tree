{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm.Parts.AxSndLf
--
-- Self-contained dispatch material for safe-default axiom
--   axSndLf : Deriv (ap1 Snd O = O) .
--
-- Contents: encAxSndLf, outAxSndLf, body_axSndLf, body_axSndLf_eval.

module BRA2.Thm.Parts.AxSndLf where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Deriv
open import BRA2.Thm.Tag using (tagAxSndLf)
open import BRA2.Thm.TagCodes
open import BRA2.Thm.EvalHelpers

------------------------------------------------------------------------
-- Encoded proof-tree input and intended Tree output.

encAxSndLf : Tree
encAxSndLf = nd (natCode tagAxSndLf) lf

outAxSndLf : Tree
outAxSndLf = codeFormula (atomic (eqn (ap1 Snd O) O))

------------------------------------------------------------------------
-- body_axSndLf: 0 args; closed output.

body_axSndLf : Fun2
body_axSndLf = Lift (KT (reify outAxSndLf))

------------------------------------------------------------------------
-- body_axSndLf_eval.

abstract

  body_axSndLf_eval : (b : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axSndLf (ap2 Pair tagCode_axSndLf O) b)
      (reify outAxSndLf)))
  body_axSndLf_eval b =
    liftKT_eval outAxSndLf
                (codeFormula_isValue (atomic (eqn (ap1 Snd O) O)))
                (ap2 Pair tagCode_axSndLf O) b
