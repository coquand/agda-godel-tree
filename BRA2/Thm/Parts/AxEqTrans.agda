{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm.Parts.AxEqTrans
--
-- Self-contained dispatch material for the equality transitivity axiom (Guard Ax 4):
--   axEqTrans : Deriv (atomic (eqn a b)
--                       imp ((atomic (eqn a c))
--                             imp (atomic (eqn b c)))) .
--
-- Contents: encAxEqTrans, outAxEqTrans, body_axEqTrans, body_axEqTrans_eval.

module BRA2.Thm.Parts.AxEqTrans where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Deriv
open import BRA2.Thm.Tag using (tagAxEqTrans)
open import BRA2.Thm.TagCodes
open import BRA2.Thm.EvalHelpers

------------------------------------------------------------------------
-- Encoded proof-tree input and intended Tree output.

encAxEqTrans : Term -> Term -> Term -> Tree
encAxEqTrans a b c = nd (natCode tagAxEqTrans)
                        (nd (code a)
                            (nd (code b) (code c)))

outAxEqTrans : Term -> Term -> Term -> Tree
outAxEqTrans a b c = codeFormula ((atomic (eqn a b))
                                    imp ((atomic (eqn a c))
                                          imp (atomic (eqn b c))))

------------------------------------------------------------------------
-- body_axEqTrans.
--
-- axEqTrans a b c : conclusion =
--   (atomic (eqn a b)) imp ((atomic (eqn a c)) imp (atomic (eqn b c)))
--   payT depth 3: Pair payAT (Pair payBT payCT).

body_axEqTrans : Fun2
body_axEqTrans =
  Fan (Lift (KT (reify tagImp)))
      (Fan (Fan (Lift (Comp Fst Snd))
                (Lift (Comp Fst (Comp Snd Snd)))
                Pair)
           (Fan (Lift (KT (reify tagImp)))
                (Fan (Fan (Lift (Comp Fst Snd))
                          (Lift (Comp Snd (Comp Snd Snd)))
                          Pair)
                     (Fan (Lift (Comp Fst (Comp Snd Snd)))
                          (Lift (Comp Snd (Comp Snd Snd)))
                          Pair)
                     Pair)
                Pair)
           Pair)
      Pair

------------------------------------------------------------------------
-- body_axEqTrans_eval.

abstract

  -- axEqTrans a b c : 3 args; depth-3 payload.
  body_axEqTrans_eval : (a' b' c' bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axEqTrans
            (ap2 Pair tagCode_axEqTrans (reify (nd (code a') (nd (code b') (code c'))))) bb)
      (reify (outAxEqTrans a' b' c'))))
  body_axEqTrans_eval a' b' c' bb =
    let payAT  = reify (code a')
        payBT  = reify (code b')
        payCT  = reify (code c')
        payT   = ap2 Pair payAT (ap2 Pair payBT payCT)
        a      = ap2 Pair tagCode_axEqTrans payT
        K_impV = tagImp
        K_impV_isValue = tagImp_isValue
        K_imp  = reify K_impV
        ext_a  = liftCompFstSnd_evalPair tagCode_axEqTrans payAT
                   (ap2 Pair payBT payCT) bb
        ext_b  = liftFstSndSnd_evalPair3 tagCode_axEqTrans payAT payBT payCT bb
        ext_c  = liftSndSndSnd_evalPair3 tagCode_axEqTrans payAT payBT payCT bb
        ab = pairOfFan_eval (Lift (Comp Fst Snd))
               (Lift (Comp Fst (Comp Snd Snd))) a bb payAT payBT ext_a ext_b
        ac = pairOfFan_eval (Lift (Comp Fst Snd))
               (Lift (Comp Snd (Comp Snd Snd))) a bb payAT payCT ext_a ext_c
        bc = pairOfFan_eval (Lift (Comp Fst (Comp Snd Snd)))
               (Lift (Comp Snd (Comp Snd Snd))) a bb payBT payCT ext_b ext_c
        ac_bc = pairOfFan_eval
                  (Fan (Lift (Comp Fst Snd))
                       (Lift (Comp Snd (Comp Snd Snd))) Pair)
                  (Fan (Lift (Comp Fst (Comp Snd Snd)))
                       (Lift (Comp Snd (Comp Snd Snd))) Pair)
                  a bb (ap2 Pair payAT payCT) (ap2 Pair payBT payCT) ac bc
        imp_acbc = pairOfConst_eval K_impV K_impV_isValue
                     (Fan (Fan (Lift (Comp Fst Snd))
                               (Lift (Comp Snd (Comp Snd Snd))) Pair)
                          (Fan (Lift (Comp Fst (Comp Snd Snd)))
                               (Lift (Comp Snd (Comp Snd Snd))) Pair)
                          Pair)
                     a bb
                     (ap2 Pair (ap2 Pair payAT payCT) (ap2 Pair payBT payCT))
                     ac_bc
        ab_imp = pairOfFan_eval
                   (Fan (Lift (Comp Fst Snd))
                        (Lift (Comp Fst (Comp Snd Snd))) Pair)
                   (Fan (Lift (KT K_imp))
                        (Fan (Fan (Lift (Comp Fst Snd))
                                  (Lift (Comp Snd (Comp Snd Snd))) Pair)
                             (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                  (Lift (Comp Snd (Comp Snd Snd))) Pair)
                             Pair) Pair)
                   a bb
                   (ap2 Pair payAT payBT)
                   (ap2 Pair K_imp
                     (ap2 Pair (ap2 Pair payAT payCT) (ap2 Pair payBT payCT)))
                   ab imp_acbc
    in pairOfConst_eval K_impV K_impV_isValue
         (Fan (Fan (Lift (Comp Fst Snd))
                   (Lift (Comp Fst (Comp Snd Snd))) Pair)
              (Fan (Lift (KT K_imp))
                   (Fan (Fan (Lift (Comp Fst Snd))
                             (Lift (Comp Snd (Comp Snd Snd))) Pair)
                        (Fan (Lift (Comp Fst (Comp Snd Snd)))
                             (Lift (Comp Snd (Comp Snd Snd))) Pair)
                        Pair) Pair)
              Pair)
         a bb
         (ap2 Pair (ap2 Pair payAT payBT)
           (ap2 Pair K_imp
             (ap2 Pair (ap2 Pair payAT payCT) (ap2 Pair payBT payCT))))
         ab_imp
