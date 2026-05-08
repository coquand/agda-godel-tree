{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm.Parts.AxSnd
--
-- Self-contained dispatch material for
--   axSnd : Deriv (ap1 Snd (ap2 Pair a b) = b) .
--
-- Contents: encAxSnd, outAxSnd, body_axSnd, body_axSnd_eval.

module BRA2.Thm.Parts.AxSnd where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Deriv
open import BRA2.Thm.Tag using (tagAxSnd)
open import BRA2.Thm.TagCodes
open import BRA2.Thm.EvalHelpers

------------------------------------------------------------------------
-- Encoded proof-tree input and intended Tree output.

encAxSnd : Term -> Term -> Tree
encAxSnd a b = nd (natCode tagAxSnd) (nd (code a) (code b))

outAxSnd : Term -> Term -> Tree
outAxSnd a b = codeFormula (atomic (eqn (ap1 Snd (ap2 Pair a b)) b))

------------------------------------------------------------------------
-- body_axSnd : mirror of body_axFst with Comp Snd Snd extractor.

body_axSnd : Fun2
body_axSnd =
  Fan (Fan (Lift (KT (reify tagAp1)))
           (Fan (Lift (KT (reify (codeF1 Snd))))
                (Fan (Lift (KT (reify tagAp2)))
                     (Fan (Lift (KT (reify (codeF2 Pair))))
                          (Lift Snd)
                          Pair)
                     Pair)
                Pair)
           Pair)
      (Lift (Comp Snd Snd))
      Pair

------------------------------------------------------------------------
-- body_axSnd_eval (proof in abstract block).

abstract

  body_axSnd_eval : (a' b' bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axSnd
            (ap2 Pair tagCode_axSnd (reify (nd (code a') (code b')))) bb)
      (reify (outAxSnd a' b'))))
  body_axSnd_eval a' b' bb =
    let payAT  = reify (code a')
        payBT  = reify (code b')
        payT   = ap2 Pair payAT payBT
        a      = ap2 Pair tagCode_axSnd payT
        K1V    = tagAp1
        K1V_isValue = tagAp1_isValue
        K2V    = codeF1 Snd
        K2V_isValue = codeF1_isValue Snd
        K3V    = tagAp2
        K3V_isValue = tagAp2_isValue
        K4V    = codeF2 Pair
        K4V_isValue = codeF2_isValue Pair
        K1     = reify K1V
        K2     = reify K2V
        K3     = reify K3V
        K4     = reify K4V
        snd_a  = bodyLiftSndPair tagCode_axSnd payT bb
        sndSnd_a : Deriv (atomic (eqn
                            (ap2 (Lift (Comp Snd Snd)) a bb) payBT))
        sndSnd_a = liftCompSndSnd_evalPair tagCode_axSnd payAT payBT bb
        l4 = pairOfConst_eval K4V K4V_isValue (Lift Snd) a bb payT snd_a
        l3 = pairOfConst_eval K3V K3V_isValue
                 (Fan (Lift (KT K4)) (Lift Snd) Pair) a bb
                 (ap2 Pair K4 payT) l4
        l2 = pairOfConst_eval K2V K2V_isValue
                 (Fan (Lift (KT K3))
                      (Fan (Lift (KT K4)) (Lift Snd) Pair) Pair) a bb
                 (ap2 Pair K3 (ap2 Pair K4 payT)) l3
        l1 = pairOfConst_eval K1V K1V_isValue
                 (Fan (Lift (KT K2))
                      (Fan (Lift (KT K3))
                           (Fan (Lift (KT K4)) (Lift Snd) Pair) Pair) Pair) a bb
                 (ap2 Pair K2 (ap2 Pair K3 (ap2 Pair K4 payT))) l2
    in pairOfFan_eval
         (Fan (Lift (KT K1))
              (Fan (Lift (KT K2))
                   (Fan (Lift (KT K3))
                        (Fan (Lift (KT K4)) (Lift Snd) Pair) Pair) Pair) Pair)
         (Lift (Comp Snd Snd)) a bb
         (ap2 Pair K1 (ap2 Pair K2 (ap2 Pair K3 (ap2 Pair K4 payT)))) payBT
         l1 sndSnd_a
