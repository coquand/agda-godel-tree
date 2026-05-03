{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.Parts.AxFst
--
-- Self-contained dispatch material for
--   axFst : Deriv (ap1 Fst (ap2 Pair a b) = a) .
--
-- Contents: encAxFst, outAxFst, body_axFst, body_axFst_eval.

module BRA.Thm.Parts.AxFst where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Thm.Tag using (tagAxFst)
open import BRA.Thm.TagCodes
open import BRA.Thm.EvalHelpers

------------------------------------------------------------------------
-- Encoded proof-tree input and intended Tree output.

encAxFst : Term -> Term -> Tree
encAxFst a b = nd (natCode tagAxFst) (nd (code a) (code b))

outAxFst : Term -> Term -> Tree
outAxFst a b = codeFormula (atomic (eqn (ap1 Fst (ap2 Pair a b)) a))

------------------------------------------------------------------------
-- body_axFst computes reify(outAxFst a' b') =
--   Pair (Pair K_a1 (Pair K_cf1F (Pair K_a2 (Pair K_cf2P payT)))) payAT
-- where payT = Pair payAT payBT, payAT = Fst payT, K* are codeF1/codeF2 constants.

body_axFst : Fun2
body_axFst =
  Fan (Fan (Lift (KT (reify tagAp1)))
           (Fan (Lift (KT (reify (codeF1 Fst))))
                (Fan (Lift (KT (reify tagAp2)))
                     (Fan (Lift (KT (reify (codeF2 Pair))))
                          (Lift Snd)
                          Pair)
                     Pair)
                Pair)
           Pair)
      (Lift (Comp Fst Snd))
      Pair

------------------------------------------------------------------------
-- body_axFst_eval (proof in abstract block).

abstract

  body_axFst_eval : (a' b' bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axFst
            (ap2 Pair tagCode_axFst (reify (nd (code a') (code b')))) bb)
      (reify (outAxFst a' b'))))
  body_axFst_eval a' b' bb =
    let payAT  = reify (code a')
        payBT  = reify (code b')
        payT   = ap2 Pair payAT payBT
        a      = ap2 Pair tagCode_axFst payT
        K1V    = tagAp1                            -- Tree
        K2V    = codeF1 Fst                        -- Tree
        K3V    = tagAp2                            -- Tree
        K4V    = codeF2 Pair                       -- Tree
        K1     = reify K1V                         -- Term form
        K2     = reify K2V
        K3     = reify K3V
        K4     = reify K4V
        snd_a  = bodyLiftSndPair tagCode_axFst payT bb
        fstSnd_a : Deriv (atomic (eqn
                            (ap2 (Lift (Comp Fst Snd)) a bb) payAT))
        fstSnd_a = liftCompFstSnd_evalPair tagCode_axFst payAT payBT bb
        l4 = pairOfConst_eval K4V (Lift Snd) a bb payT snd_a
        l3 = pairOfConst_eval K3V
                 (Fan (Lift (KT K4)) (Lift Snd) Pair) a bb
                 (ap2 Pair K4 payT) l4
        l2 = pairOfConst_eval K2V
                 (Fan (Lift (KT K3))
                      (Fan (Lift (KT K4)) (Lift Snd) Pair) Pair) a bb
                 (ap2 Pair K3 (ap2 Pair K4 payT)) l3
        l1 = pairOfConst_eval K1V
                 (Fan (Lift (KT K2))
                      (Fan (Lift (KT K3))
                           (Fan (Lift (KT K4)) (Lift Snd) Pair) Pair) Pair) a bb
                 (ap2 Pair K2 (ap2 Pair K3 (ap2 Pair K4 payT))) l2
    in pairOfFan_eval
         (Fan (Lift (KT K1))
              (Fan (Lift (KT K2))
                   (Fan (Lift (KT K3))
                        (Fan (Lift (KT K4)) (Lift Snd) Pair) Pair) Pair) Pair)
         (Lift (Comp Fst Snd)) a bb
         (ap2 Pair K1 (ap2 Pair K2 (ap2 Pair K3 (ap2 Pair K4 payT)))) payAT
         l1 fstSnd_a
