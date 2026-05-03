{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.Parts.AxKT
--
-- Encoding for axZ (the new primitive replacing axKT in the 2026-04-26
-- refactor).  Filename retained for git-history continuity; the file
-- now contains encAxZ / outAxZ plus body_axZ / body_axZ_eval.
--
--   axZ x : Deriv (ap1 Z x = O)
--
-- Tag tagAxKT is reused for axZ.

module BRA.Thm.Parts.AxKT where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Thm.Tag using (tagAxKT)
open import BRA.Thm.TagCodes
open import BRA.Thm.EvalHelpers

------------------------------------------------------------------------
-- Encoded proof-tree input and intended Tree output.

encAxZ : Term -> Tree
encAxZ x = nd (natCode tagAxKT) (nd (codeF1 Z) (code x))

outAxZ : Term -> Tree
outAxZ x = codeFormula (atomic (eqn (ap1 Z x) O))

------------------------------------------------------------------------
-- body_axZ.
--
-- axZ x : LHS = ap1 Z x , RHS = O .
--   payT depth 2: Pair payZTagged payXT
--     where payZTagged = reify (codeF1 Z), payXT = reify (code x).
--   reify(LHS) = Pair K_a1 (Pair payZTagged payXT) = Pair K_a1 payT
--   reify(RHS) = O (= reify lf, code O = lf after redesign)

body_axZ : Fun2
body_axZ =
  Fan
    -- LHS-build: Pair K_a1 (Snd a) = Pair K_a1 payT
    (Fan (Lift (KT (reify tagAp1)))
         (Lift Snd)
         Pair)
    -- RHS-build: O
    (Lift (KT O))
    Pair

------------------------------------------------------------------------
-- body_axZ_eval.

abstract

  -- For axZ x: body_axZ a b = Pair (Pair K_a1 payT) O
  --   where a = Pair tagCode_axKT payT, payT = Pair payZTagged payXT.
  --   This equals reify(outAxZ x) = reify(codeFormula (atomic (eqn (ap1 Z x) O))).
  body_axZ_eval : (x bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axZ
            (ap2 Pair tagCode_axKT (reify (nd (codeF1 Z) (code x)))) bb)
      (reify (outAxZ x))))
  body_axZ_eval x bb =
    let payZTagged = reify (codeF1 Z)
        payXT      = reify (code x)
        payT       = ap2 Pair payZTagged payXT
        a          = ap2 Pair tagCode_axKT payT
        K1V        = tagAp1
        K1         = reify K1V
        sndA       : Deriv (atomic (eqn (ap2 (Lift Snd) a bb) payT))
        sndA       = bodyLiftSndPair tagCode_axKT payT bb
        lhsBuild   = pairOfConst_eval K1V (Lift Snd) a bb payT sndA
        rhsKO      = liftKT_eval lf a bb           -- liftKT_eval Tree-indexed; lf gives O
    in pairOfFan_eval
         (Fan (Lift (KT K1)) (Lift Snd) Pair)
         (Lift (KT O)) a bb
         (ap2 Pair K1 payT) O
         lhsBuild rhsKO
