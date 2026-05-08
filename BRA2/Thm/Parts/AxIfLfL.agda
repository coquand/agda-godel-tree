{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm.Parts.AxIfLfL
--
-- Self-contained dispatch material for
--   axIfLfL : Deriv (ap2 IfLf O (ap2 Pair a b) = a) .
--
-- Contents: encAxIfLfL, outAxIfLfL, body_axIfLfL, body_axIfLfL_eval.

module BRA2.Thm.Parts.AxIfLfL where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Deriv
open import BRA2.Thm.Tag using (tagAxIfLfL)
open import BRA2.Thm.TagCodes
open import BRA2.Thm.EvalHelpers

------------------------------------------------------------------------
-- Encoded proof-tree input and intended Tree output.

encAxIfLfL : Term -> Term -> Tree
encAxIfLfL a b = nd (natCode tagAxIfLfL) (nd (code a) (code b))

outAxIfLfL : Term -> Term -> Tree
outAxIfLfL a b = codeFormula (atomic (eqn (ap2 IfLf O (ap2 Pair a b)) a))

------------------------------------------------------------------------
-- body_axIfLfL.
--
-- axIfLfL a b : LHS = ap2 IfLf O (ap2 Pair a b) , RHS = a .
--   payT depth 2: Pair payAT payBT.
--   reify(LHS) = Pair K_a2 (Pair (reify (codeF2 IfLf))
--                  (Pair O                                        -- code O = lf
--                        (Pair K_a2 (Pair (reify (codeF2 Pair)) payT))))
--   reify(RHS) = payAT (= Fst payT)

body_axIfLfL : Fun2
body_axIfLfL =
  Fan
    (Fan (Lift (KT (reify tagAp2)))
         (Fan (Lift (KT (reify (codeF2 IfLf))))
              (Fan (Lift (KT O))
                   (Fan (Lift (KT (reify tagAp2)))
                        (Fan (Lift (KT (reify (codeF2 Pair))))
                             (Lift Snd)
                             Pair)
                        Pair)
                   Pair)
              Pair)
         Pair)
    (Lift (Comp Fst Snd))
    Pair

------------------------------------------------------------------------
-- body_axIfLfL_eval.

abstract

  -- axIfLfL a b : 2 args; depth-2 payload.
  body_axIfLfL_eval : (a' b' bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axIfLfL
            (ap2 Pair tagCode_axIfLfL (reify (nd (code a') (code b')))) bb)
      (reify (outAxIfLfL a' b'))))
  body_axIfLfL_eval a' b' bb =
    let payAT  = reify (code a')
        payBT  = reify (code b')
        payT   = ap2 Pair payAT payBT
        a      = ap2 Pair tagCode_axIfLfL payT
        K_a2V  = tagAp2
        K_a2V_isValue = tagAp2_isValue
        K_a2   = reify K_a2V
        K_ifLfV = codeF2 IfLf
        K_ifLfV_isValue = codeF2_isValue IfLf
        K_ifLf = reify K_ifLfV
        K_ooV  = lf                                -- post-redesign: code O = lf, reify = O

        K_ooV_isValue = valO
        K_oo   = reify K_ooV
        K_pairV = codeF2 Pair
        K_pairV_isValue = codeF2_isValue Pair
        K_pair = reify K_pairV
        snd_a  = bodyLiftSndPair tagCode_axIfLfL payT bb
        ext_a  = liftCompFstSnd_evalPair tagCode_axIfLfL payAT payBT bb
        l5 = pairOfConst_eval K_pairV K_pairV_isValue (Lift Snd) a bb payT snd_a
        l4 = pairOfConst_eval K_a2V K_a2V_isValue
                 (Fan (Lift (KT K_pair)) (Lift Snd) Pair) a bb
                 (ap2 Pair K_pair payT) l5
        l3 = pairOfConst_eval K_ooV K_ooV_isValue
                 (Fan (Lift (KT K_a2))
                      (Fan (Lift (KT K_pair)) (Lift Snd) Pair) Pair)
                 a bb (ap2 Pair K_a2 (ap2 Pair K_pair payT)) l4
        l2 = pairOfConst_eval K_ifLfV K_ifLfV_isValue
                 (Fan (Lift (KT K_oo))
                      (Fan (Lift (KT K_a2))
                           (Fan (Lift (KT K_pair)) (Lift Snd) Pair) Pair) Pair)
                 a bb
                 (ap2 Pair K_oo (ap2 Pair K_a2 (ap2 Pair K_pair payT))) l3
        l1 = pairOfConst_eval K_a2V K_a2V_isValue
                 (Fan (Lift (KT K_ifLf))
                      (Fan (Lift (KT K_oo))
                           (Fan (Lift (KT K_a2))
                                (Fan (Lift (KT K_pair)) (Lift Snd) Pair) Pair)
                           Pair) Pair)
                 a bb
                 (ap2 Pair K_ifLf (ap2 Pair K_oo
                    (ap2 Pair K_a2 (ap2 Pair K_pair payT)))) l2
    in pairOfFan_eval
         (Fan (Lift (KT K_a2))
              (Fan (Lift (KT K_ifLf))
                   (Fan (Lift (KT K_oo))
                        (Fan (Lift (KT K_a2))
                             (Fan (Lift (KT K_pair)) (Lift Snd) Pair) Pair)
                        Pair) Pair) Pair)
         (Lift (Comp Fst Snd)) a bb
         (ap2 Pair K_a2 (ap2 Pair K_ifLf (ap2 Pair K_oo
            (ap2 Pair K_a2 (ap2 Pair K_pair payT))))) payAT
         l1 ext_a
