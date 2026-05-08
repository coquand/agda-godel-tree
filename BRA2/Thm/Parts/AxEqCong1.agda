{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm.Parts.AxEqCong1
--
-- Self-contained dispatch material for the unary equality-congruence axiom (Guard Ax 5):
--   axEqCong1 : Deriv ((atomic (eqn a b))
--                        imp (atomic (eqn (ap1 f a) (ap1 f b)))) .
--
-- Contents: encAxEqCong1, outAxEqCong1, body_axEqCong1, body_axEqCong1_eval.

module BRA2.Thm.Parts.AxEqCong1 where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Deriv
open import BRA2.Thm.Tag using (tagAxEqCong1)
open import BRA2.Thm.TagCodes
open import BRA2.Thm.EvalHelpers

------------------------------------------------------------------------
-- Encoded proof-tree input and intended Tree output.

encAxEqCong1 : Fun1 -> Term -> Term -> Tree
encAxEqCong1 f a b = nd (natCode tagAxEqCong1)
                        (nd (codeF1 f)
                            (nd (code a) (code b)))

outAxEqCong1 : Fun1 -> Term -> Term -> Tree
outAxEqCong1 f a b = codeFormula ((atomic (eqn a b))
                                    imp (atomic (eqn (ap1 f a) (ap1 f b))))

------------------------------------------------------------------------
-- body_axEqCong1.
--
-- axEqCong1 f a b : conclusion =
--   (atomic (eqn a b)) imp (atomic (eqn (ap1 f a) (ap1 f b)))
--   payT depth 3: Pair payFT (Pair payAT payBT).

body_axEqCong1 : Fun2
body_axEqCong1 =
  Fan (Lift (KT (reify tagImp)))
      (Fan (Fan (Lift (Comp Fst (Comp Snd Snd)))
                (Lift (Comp Snd (Comp Snd Snd)))
                Pair)
           (Fan (Fan (Lift (KT (reify tagAp1)))
                     (Fan (Lift (Comp Fst Snd))
                          (Lift (Comp Fst (Comp Snd Snd)))
                          Pair)
                     Pair)
                (Fan (Lift (KT (reify tagAp1)))
                     (Fan (Lift (Comp Fst Snd))
                          (Lift (Comp Snd (Comp Snd Snd)))
                          Pair)
                     Pair)
                Pair)
           Pair)
      Pair

------------------------------------------------------------------------
-- body_axEqCong1_eval.

abstract

  -- axEqCong1 f a b : 3 args (f : Fun1, a, b : Term); depth-3 payload.
  body_axEqCong1_eval : (f : Fun1) (a' b' bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axEqCong1
            (ap2 Pair tagCode_axEqCong1 (reify (nd (codeF1 f) (nd (code a') (code b'))))) bb)
      (reify (outAxEqCong1 f a' b'))))
  body_axEqCong1_eval f a' b' bb =
    let payFT  = reify (codeF1 f)
        payAT  = reify (code a')
        payBT  = reify (code b')
        payT   = ap2 Pair payFT (ap2 Pair payAT payBT)
        a      = ap2 Pair tagCode_axEqCong1 payT
        K_impV = tagImp
        K_impV_isValue = tagImp_isValue
        K_imp  = reify K_impV
        K_a1V  = tagAp1
        K_a1V_isValue = tagAp1_isValue
        K_a1   = reify K_a1V
        ext_f  = liftCompFstSnd_evalPair tagCode_axEqCong1 payFT
                   (ap2 Pair payAT payBT) bb
        ext_a  = liftFstSndSnd_evalPair3 tagCode_axEqCong1 payFT payAT payBT bb
        ext_b  = liftSndSndSnd_evalPair3 tagCode_axEqCong1 payFT payAT payBT bb
        ab_pair = pairOfFan_eval (Lift (Comp Fst (Comp Snd Snd)))
                    (Lift (Comp Snd (Comp Snd Snd))) a bb payAT payBT ext_a ext_b
        fa_pair = pairOfFan_eval (Lift (Comp Fst Snd))
                    (Lift (Comp Fst (Comp Snd Snd))) a bb payFT payAT ext_f ext_a
        fb_pair = pairOfFan_eval (Lift (Comp Fst Snd))
                    (Lift (Comp Snd (Comp Snd Snd))) a bb payFT payBT ext_f ext_b
        ka1_fa  = pairOfConst_eval K_a1V K_a1V_isValue
                    (Fan (Lift (Comp Fst Snd))
                         (Lift (Comp Fst (Comp Snd Snd))) Pair)
                    a bb (ap2 Pair payFT payAT) fa_pair
        ka1_fb  = pairOfConst_eval K_a1V K_a1V_isValue
                    (Fan (Lift (Comp Fst Snd))
                         (Lift (Comp Snd (Comp Snd Snd))) Pair)
                    a bb (ap2 Pair payFT payBT) fb_pair
        ka1_pair = pairOfFan_eval
                     (Fan (Lift (KT K_a1))
                          (Fan (Lift (Comp Fst Snd))
                               (Lift (Comp Fst (Comp Snd Snd))) Pair) Pair)
                     (Fan (Lift (KT K_a1))
                          (Fan (Lift (Comp Fst Snd))
                               (Lift (Comp Snd (Comp Snd Snd))) Pair) Pair)
                     a bb
                     (ap2 Pair K_a1 (ap2 Pair payFT payAT))
                     (ap2 Pair K_a1 (ap2 Pair payFT payBT))
                     ka1_fa ka1_fb
        inner = pairOfFan_eval
                  (Fan (Lift (Comp Fst (Comp Snd Snd)))
                       (Lift (Comp Snd (Comp Snd Snd))) Pair)
                  (Fan (Fan (Lift (KT K_a1))
                            (Fan (Lift (Comp Fst Snd))
                                 (Lift (Comp Fst (Comp Snd Snd))) Pair) Pair)
                       (Fan (Lift (KT K_a1))
                            (Fan (Lift (Comp Fst Snd))
                                 (Lift (Comp Snd (Comp Snd Snd))) Pair) Pair)
                       Pair)
                  a bb
                  (ap2 Pair payAT payBT)
                  (ap2 Pair (ap2 Pair K_a1 (ap2 Pair payFT payAT))
                             (ap2 Pair K_a1 (ap2 Pair payFT payBT)))
                  ab_pair ka1_pair
    in pairOfConst_eval K_impV K_impV_isValue
         (Fan (Fan (Lift (Comp Fst (Comp Snd Snd)))
                   (Lift (Comp Snd (Comp Snd Snd))) Pair)
              (Fan (Fan (Lift (KT K_a1))
                        (Fan (Lift (Comp Fst Snd))
                             (Lift (Comp Fst (Comp Snd Snd))) Pair) Pair)
                   (Fan (Lift (KT K_a1))
                        (Fan (Lift (Comp Fst Snd))
                             (Lift (Comp Snd (Comp Snd Snd))) Pair) Pair)
                   Pair)
              Pair)
         a bb
         (ap2 Pair (ap2 Pair payAT payBT)
           (ap2 Pair (ap2 Pair K_a1 (ap2 Pair payFT payAT))
                      (ap2 Pair K_a1 (ap2 Pair payFT payBT))))
         inner
