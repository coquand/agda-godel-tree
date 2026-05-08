{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm.Parts.AxConst
--
-- Self-contained dispatch material for
--   axConst : Deriv (ap2 Const a b = a) .
--
-- Contents: encAxConst, outAxConst, body_axConst, body_axConst_eval.

module BRA2.Thm.Parts.AxConst where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Deriv
open import BRA2.Thm.Tag using (tagAxConst)
open import BRA2.Thm.TagCodes
open import BRA2.Thm.EvalHelpers

------------------------------------------------------------------------
-- Encoded proof-tree input and intended Tree output.

encAxConst : Term -> Term -> Tree
encAxConst a b = nd (natCode tagAxConst) (nd (code a) (code b))

outAxConst : Term -> Term -> Tree
outAxConst a b = codeFormula (atomic (eqn (ap2 Const a b) a))

------------------------------------------------------------------------
-- body_axConst.

body_axConst : Fun2
body_axConst =
  Fan (Fan (Lift (KT (reify tagAp2)))
           (Fan (Lift (KT (reify (codeF2 Const))))
                (Lift Snd)
                Pair)
           Pair)
      (Lift (Comp Fst Snd))
      Pair

------------------------------------------------------------------------
-- body_axConst_eval.

abstract

  body_axConst_eval : (a' b' bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axConst
            (ap2 Pair tagCode_axConst (reify (nd (code a') (code b')))) bb)
      (reify (outAxConst a' b'))))
  body_axConst_eval a' b' bb =
    let payAT  = reify (code a')
        payBT  = reify (code b')
        payT   = ap2 Pair payAT payBT
        a      = ap2 Pair tagCode_axConst payT
        K1V    = tagAp2
        K1V_isValue = tagAp2_isValue
        K2V    = codeF2 Const
        K2V_isValue = codeF2_isValue Const
        K1     = reify K1V
        K2     = reify K2V
        snd_a  = bodyLiftSndPair tagCode_axConst payT bb
        fstSnd_a = liftCompFstSnd_evalPair tagCode_axConst payAT payBT bb
        l2 = pairOfConst_eval K2V K2V_isValue (Lift Snd) a bb payT snd_a
        l1 = pairOfConst_eval K1V K1V_isValue
                 (Fan (Lift (KT K2)) (Lift Snd) Pair) a bb
                 (ap2 Pair K2 payT) l2
    in pairOfFan_eval
         (Fan (Lift (KT K1))
              (Fan (Lift (KT K2)) (Lift Snd) Pair) Pair)
         (Lift (Comp Fst Snd)) a bb
         (ap2 Pair K1 (ap2 Pair K2 payT)) payAT
         l1 fstSnd_a
