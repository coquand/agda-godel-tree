{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm.Parts.AxTreeEqLN
--
-- Self-contained dispatch material for
--   axTreeEqLN : Deriv (ap2 TreeEq O (ap2 Pair a b) = ap2 Pair O O) .
--
-- Contents: encAxTreeEqLN, outAxTreeEqLN, body_axTreeEqLN, body_axTreeEqLN_eval.

module BRA2.Thm.Parts.AxTreeEqLN where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.DerivThreshold
open import BRA2.Thm.Tag using (tagAxTreeEqLN)
open import BRA2.Thm.TagCodes
open import BRA2.Thm.EvalHelpers

------------------------------------------------------------------------
-- Encoded proof-tree input and intended Tree output.

encAxTreeEqLN : Term -> Term -> Tree
encAxTreeEqLN a b = nd (natCode tagAxTreeEqLN) (nd (code a) (code b))

outAxTreeEqLN : Term -> Term -> Tree
outAxTreeEqLN a b =
  codeFormula (atomic (eqn (ap2 TreeEq O (ap2 Pair a b)) (ap2 Pair O O)))

------------------------------------------------------------------------
-- body_axTreeEqLN.
--
-- axTreeEqLN a b : LHS = ap2 TreeEq O (ap2 Pair a b) , RHS = ap2 Pair O O .
--   payT depth 2: Pair payAT payBT.
--   RHS is a closed Term whose code reifies to the constant
--     reify (code (ap2 Pair O O)) = Pair K_a2 (Pair K_pair (Pair O O))
--   (post-redesign: inner code O = lf, so reify shrinks.)

body_axTreeEqLN : Fun2
body_axTreeEqLN =
  Fan
    (Fan (Lift (KT (reify tagAp2)))
         (Fan (Lift (KT (reify (codeF2 TreeEq))))
              (Fan (Lift (KT O))
                   (Fan (Lift (KT (reify tagAp2)))
                        (Fan (Lift (KT (reify (codeF2 Pair))))
                             (Lift Snd)
                             Pair)
                        Pair)
                   Pair)
              Pair)
         Pair)
    (Lift (KT (reify (code (ap2 Pair O O)))))
    Pair

------------------------------------------------------------------------
-- body_axTreeEqLN_eval.

abstract

  -- axTreeEqLN a b : 2 args; depth-2 payload.
  body_axTreeEqLN_eval : (a' b' bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axTreeEqLN
            (ap2 Pair tagCode_axTreeEqLN (reify (nd (code a') (code b')))) bb)
      (reify (outAxTreeEqLN a' b'))))
  body_axTreeEqLN_eval a' b' bb =
    let payAT  = reify (code a')
        payBT  = reify (code b')
        payT   = ap2 Pair payAT payBT
        a      = ap2 Pair tagCode_axTreeEqLN payT
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
        snd_a  = bodyLiftSndPair tagCode_axTreeEqLN payT bb
        l5 = pairOfConst_eval K_pairV K_pairV_isValue (Lift Snd) a bb payT snd_a
        l4 = pairOfConst_eval K_a2V K_a2V_isValue
                 (Fan (Lift (KT K_pair)) (Lift Snd) Pair) a bb
                 (ap2 Pair K_pair payT) l5
        l3 = pairOfConst_eval K_ooV K_ooV_isValue
                 (Fan (Lift (KT K_a2))
                      (Fan (Lift (KT K_pair)) (Lift Snd) Pair) Pair)
                 a bb (ap2 Pair K_a2 (ap2 Pair K_pair payT)) l4
        l2 = pairOfConst_eval K_teV K_teV_isValue
                 (Fan (Lift (KT K_oo))
                      (Fan (Lift (KT K_a2))
                           (Fan (Lift (KT K_pair)) (Lift Snd) Pair) Pair) Pair)
                 a bb
                 (ap2 Pair K_oo (ap2 Pair K_a2 (ap2 Pair K_pair payT))) l3
        l1 = pairOfConst_eval K_a2V K_a2V_isValue
                 (Fan (Lift (KT K_te))
                      (Fan (Lift (KT K_oo))
                           (Fan (Lift (KT K_a2))
                                (Fan (Lift (KT K_pair)) (Lift Snd) Pair) Pair)
                           Pair) Pair)
                 a bb
                 (ap2 Pair K_te (ap2 Pair K_oo
                    (ap2 Pair K_a2 (ap2 Pair K_pair payT)))) l2
        rhs = liftKT_eval K_rhsV K_rhsV_isValue a bb
    in pairOfFan_eval
         (Fan (Lift (KT K_a2))
              (Fan (Lift (KT K_te))
                   (Fan (Lift (KT K_oo))
                        (Fan (Lift (KT K_a2))
                             (Fan (Lift (KT K_pair)) (Lift Snd) Pair) Pair)
                        Pair) Pair) Pair)
         (Lift (KT K_rhs)) a bb
         (ap2 Pair K_a2 (ap2 Pair K_te (ap2 Pair K_oo
            (ap2 Pair K_a2 (ap2 Pair K_pair payT))))) K_rhs
         l1 rhs
