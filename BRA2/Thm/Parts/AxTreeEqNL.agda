{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm.Parts.AxTreeEqNL
--
-- Self-contained dispatch material for
--   axTreeEqNL : Deriv (ap2 TreeEq (ap2 Pair a b) O = ap2 Pair O O) .
--
-- Contents: encAxTreeEqNL, outAxTreeEqNL, body_axTreeEqNL, body_axTreeEqNL_eval.

module BRA2.Thm.Parts.AxTreeEqNL where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.DerivThreshold
open import BRA2.Thm.Tag using (tagAxTreeEqNL)
open import BRA2.Thm.TagCodes
open import BRA2.Thm.EvalHelpers

------------------------------------------------------------------------
-- Encoded proof-tree input and intended Tree output.

encAxTreeEqNL : Term -> Term -> Tree
encAxTreeEqNL a b = nd (natCode tagAxTreeEqNL) (nd (code a) (code b))

outAxTreeEqNL : Term -> Term -> Tree
outAxTreeEqNL a b =
  codeFormula (atomic (eqn (ap2 TreeEq (ap2 Pair a b) O) (ap2 Pair O O)))

------------------------------------------------------------------------
-- body_axTreeEqNL.
--
-- axTreeEqNL a b : LHS = ap2 TreeEq (ap2 Pair a b) O , RHS = ap2 Pair O O .
--   payT depth 2: Pair payAT payBT.

body_axTreeEqNL : Fun2
body_axTreeEqNL =
  Fan
    (Fan (Lift (KT (reify tagAp2)))
         (Fan (Lift (KT (reify (codeF2 TreeEq))))
              (Fan (Fan (Lift (KT (reify tagAp2)))
                        (Fan (Lift (KT (reify (codeF2 Pair))))
                             (Lift Snd)
                             Pair)
                        Pair)
                   (Lift (KT O))
                   Pair)
              Pair)
         Pair)
    (Lift (KT (reify (code (ap2 Pair O O)))))
    Pair

------------------------------------------------------------------------
-- body_axTreeEqNL_eval.

abstract

  -- axTreeEqNL a b : 2 args; depth-2 payload.  Mirror of axTreeEqLN.
  body_axTreeEqNL_eval : (a' b' bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axTreeEqNL
            (ap2 Pair tagCode_axTreeEqNL (reify (nd (code a') (code b')))) bb)
      (reify (outAxTreeEqNL a' b'))))
  body_axTreeEqNL_eval a' b' bb =
    let payAT  = reify (code a')
        payBT  = reify (code b')
        payT   = ap2 Pair payAT payBT
        a      = ap2 Pair tagCode_axTreeEqNL payT
        K_a2V  = tagAp2
        K_a2V_isValue = tagAp2_isValue
        K_a2   = reify K_a2V
        K_teV  = codeF2 TreeEq
        K_teV_isValue = codeF2_isValue TreeEq
        K_te   = reify K_teV
        K_ooV  = lf                                -- post-redesign: code O = lf, reify = O

        K_ooV_isValue = valO
        K_oo   = reify K_ooV
        K_pairV = codeF2 Pair
        K_pairV_isValue = codeF2_isValue Pair
        K_pair = reify K_pairV
        K_rhsV = code (ap2 Pair O O)
        K_rhsV_isValue = code_isValue (ap2 Pair O O)
        K_rhs  = reify K_rhsV
        snd_a  = bodyLiftSndPair tagCode_axTreeEqNL payT bb
        l5 = pairOfConst_eval K_pairV K_pairV_isValue (Lift Snd) a bb payT snd_a
        l4 = pairOfConst_eval K_a2V K_a2V_isValue
                 (Fan (Lift (KT K_pair)) (Lift Snd) Pair) a bb
                 (ap2 Pair K_pair payT) l5
        kOO = liftKT_eval K_ooV K_ooV_isValue a bb
        l3 = pairOfFan_eval
                 (Fan (Lift (KT K_a2))
                      (Fan (Lift (KT K_pair)) (Lift Snd) Pair) Pair)
                 (Lift (KT K_oo)) a bb
                 (ap2 Pair K_a2 (ap2 Pair K_pair payT)) K_oo
                 l4 kOO
        l2 = pairOfConst_eval K_teV K_teV_isValue
                 (Fan (Fan (Lift (KT K_a2))
                           (Fan (Lift (KT K_pair)) (Lift Snd) Pair) Pair)
                      (Lift (KT K_oo)) Pair)
                 a bb
                 (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_pair payT)) K_oo) l3
        l1 = pairOfConst_eval K_a2V K_a2V_isValue
                 (Fan (Lift (KT K_te))
                      (Fan (Fan (Lift (KT K_a2))
                                (Fan (Lift (KT K_pair)) (Lift Snd) Pair) Pair)
                           (Lift (KT K_oo)) Pair) Pair)
                 a bb
                 (ap2 Pair K_te
                    (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_pair payT)) K_oo)) l2
        rhs = liftKT_eval K_rhsV K_rhsV_isValue a bb
    in pairOfFan_eval
         (Fan (Lift (KT K_a2))
              (Fan (Lift (KT K_te))
                   (Fan (Fan (Lift (KT K_a2))
                             (Fan (Lift (KT K_pair)) (Lift Snd) Pair) Pair)
                        (Lift (KT K_oo)) Pair) Pair) Pair)
         (Lift (KT K_rhs)) a bb
         (ap2 Pair K_a2 (ap2 Pair K_te
            (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_pair payT)) K_oo))) K_rhs
         l1 rhs
