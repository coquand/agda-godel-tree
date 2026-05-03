{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.Parts.AxRefl
--
-- Self-contained dispatch material for safe-default
--   axRefl : Deriv (atomic (eqn t t)) .
--
-- Contents: encAxRefl, outAxRefl, body_axRefl, body_axRefl_eval.

module BRA.Thm.Parts.AxRefl where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Thm.Tag using (tagAxRefl)
open import BRA.Thm.TagCodes
open import BRA.Thm.EvalHelpers

------------------------------------------------------------------------
-- Encoded proof-tree input and intended Tree output.

encAxRefl : Term -> Tree
encAxRefl t = nd (natCode tagAxRefl) (code t)

outAxRefl : Term -> Tree
outAxRefl t = codeFormula (atomic (eqn t t))

------------------------------------------------------------------------
-- body_axRefl.
--
-- axRefl t : conclusion = atomic (eqn t t).
--   payT = code t reified.
--   reify(out) = Pair payT payT.

body_axRefl : Fun2
body_axRefl = Fan (Lift Snd) (Lift Snd) Pair

------------------------------------------------------------------------
-- body_axRefl_eval.

abstract

  -- axRefl t : 1 arg; depth-1 payload (just code t reified).
  body_axRefl_eval : (t bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axRefl (ap2 Pair tagCode_axRefl (reify (code t))) bb)
      (reify (outAxRefl t))))
  body_axRefl_eval t bb =
    let payT  = reify (code t)
        a     = ap2 Pair tagCode_axRefl payT
        snd_a = bodyLiftSndPair tagCode_axRefl payT bb
    in pairOfFan_eval (Lift Snd) (Lift Snd) a bb payT payT snd_a snd_a
