{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.Parts.AxSndLf
--
-- Self-contained dispatch material for safe-default axiom
--   axSndLf : Deriv (ap1 Snd O = O) .
--
-- Contents: encAxSndLf, outAxSndLf, body_axSndLf, body_axSndLf_eval.

module BRA.Thm.Parts.AxSndLf where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Thm.Tag using (tagAxSndLf)
open import BRA.Thm.TagCodes
open import BRA.Thm.EvalHelpers

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
    liftKT_eval outAxSndLf (ap2 Pair tagCode_axSndLf O) b
