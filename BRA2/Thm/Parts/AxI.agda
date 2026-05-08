{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm.Parts.AxI
--
-- Self-contained dispatch material for
--   axI : Deriv (ap1 I t = t) .
--
-- Contents: encAxI, outAxI, body_axI, body_axI_eval.

module BRA2.Thm.Parts.AxI where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Deriv
open import BRA2.Thm.Tag using (tagAxI)
open import BRA2.Thm.TagCodes
open import BRA2.Thm.EvalHelpers

------------------------------------------------------------------------
-- Encoded proof-tree input and intended Tree output.

encAxI : Term -> Tree
encAxI t = nd (natCode tagAxI) (code t)

outAxI : Term -> Tree
outAxI t = codeFormula (atomic (eqn (ap1 I t) t))

------------------------------------------------------------------------
-- body_axI : Fun2 dispatcher.
--
-- body_axI computes reify(outAxI t) = Pair (Pair KAp1 (Pair KCodeF1_I payT)) payT
-- where KAp1 = reify tagAp1, KCodeF1_I = reify (codeF1 I), payT = Snd a.

body_axI : Fun2
body_axI =
  Fan (Fan (Lift (KT (reify tagAp1)))
           (Fan (Lift (KT (reify (codeF1 I))))
                (Lift Snd)
                Pair)
           Pair)
      (Lift Snd)
      Pair

------------------------------------------------------------------------
-- body_axI_eval (proof in abstract block).

abstract

  body_axI_eval : (t b : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axI (ap2 Pair tagCode_axI (reify (code t))) b)
      (reify (outAxI t))))
  body_axI_eval t b =
    let payT  = reify (code t)
        a     = ap2 Pair tagCode_axI payT
        K1V   = tagAp1               -- Tree
        K1V_isValue = tagAp1_isValue
        K2V   = codeF1 I             -- Tree
        K2V_isValue = codeF1_isValue I
        K1    = reify K1V            -- Term form
        K2    = reify K2V            -- Term form
        snd_a = bodyLiftSndPair tagCode_axI payT b
        innerKT_red = pairOfConst_eval K2V K2V_isValue (Lift Snd) a b payT snd_a
        outerKT_red = pairOfConst_eval K1V K1V_isValue
                        (Fan (Lift (KT K2)) (Lift Snd) Pair)
                        a b (ap2 Pair K2 payT) innerKT_red
    in pairOfFan_eval
         (Fan (Lift (KT K1))
              (Fan (Lift (KT K2)) (Lift Snd) Pair)
              Pair)
         (Lift Snd) a b
         (ap2 Pair K1 (ap2 Pair K2 payT)) payT
         outerKT_red snd_a
