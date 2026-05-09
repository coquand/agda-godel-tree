{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm.Parts.AxEqCongR
--
-- Self-contained dispatch material for the binary right equality-congruence axiom (Guard Ax 7):
--   axEqCongR : Deriv ((atomic (eqn a b))
--                        imp (atomic (eqn (ap2 g c a) (ap2 g c b)))) .
--
-- Contents: encAxEqCongR, outAxEqCongR, body_axEqCongR, body_axEqCongR_eval.

module BRA2.Thm.Parts.AxEqCongR where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.DerivThreshold
open import BRA2.Thm.Tag using (tagAxEqCongR)
open import BRA2.Thm.TagCodes
open import BRA2.Thm.EvalHelpers

------------------------------------------------------------------------
-- Encoded proof-tree input and intended Tree output.

encAxEqCongR : Fun2 -> Term -> Term -> Term -> Tree
encAxEqCongR g a b c = nd (natCode tagAxEqCongR)
                          (nd (codeF2 g)
                              (nd (code a)
                                  (nd (code b) (code c))))

outAxEqCongR : Fun2 -> Term -> Term -> Term -> Tree
outAxEqCongR g a b c = codeFormula ((atomic (eqn a b))
                                      imp (atomic (eqn (ap2 g c a) (ap2 g c b))))

------------------------------------------------------------------------
-- body_axEqCongR.
--
-- axEqCongR g a b c : conclusion =
--   (atomic (eqn a b)) imp (atomic (eqn (ap2 g c a) (ap2 g c b)))
--   payT depth 4: Pair payGT (Pair payAT (Pair payBT payCT)).
--   (Same encoding as axEqCongL; only the inner ap2's argument order
--    differs in the conclusion: payCT before payAT/payBT.)

body_axEqCongR : Fun2
body_axEqCongR =
  Fan (Lift (KT (reify tagImp)))
      (Fan (Fan (Lift (Comp Fst (Comp Snd Snd)))
                (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                Pair)
           (Fan (Fan (Lift (KT (reify tagAp2)))
                     (Fan (Lift (Comp Fst Snd))
                          (Fan (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                               (Lift (Comp Fst (Comp Snd Snd)))
                               Pair)
                          Pair)
                     Pair)
                (Fan (Lift (KT (reify tagAp2)))
                     (Fan (Lift (Comp Fst Snd))
                          (Fan (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                               (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                               Pair)
                          Pair)
                     Pair)
                Pair)
           Pair)
      Pair

------------------------------------------------------------------------
-- body_axEqCongR_eval.

abstract

  -- axEqCongR g a b c : 4 args; depth-4 payload.  Mirror of axEqCongL
  -- with payCT prepended (instead of appended) to payAT/payBT in the
  -- inner ap2 g _ _ codes.
  body_axEqCongR_eval : (g : Fun2) (a' b' c' bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axEqCongR
            (ap2 Pair tagCode_axEqCongR
              (reify (nd (codeF2 g) (nd (code a') (nd (code b') (code c')))))) bb)
      (reify (outAxEqCongR g a' b' c'))))
  body_axEqCongR_eval g a' b' c' bb =
    let payGT  = reify (codeF2 g)
        payAT  = reify (code a')
        payBT  = reify (code b')
        payCT  = reify (code c')
        payT   = ap2 Pair payGT (ap2 Pair payAT (ap2 Pair payBT payCT))
        a      = ap2 Pair tagCode_axEqCongR payT
        K_impV = tagImp
        K_impV_isValue = tagImp_isValue
        K_imp  = reify K_impV
        K_a2V  = tagAp2
        K_a2V_isValue = tagAp2_isValue
        K_a2   = reify K_a2V
        ext_g  = liftCompFstSnd_evalPair tagCode_axEqCongR payGT
                   (ap2 Pair payAT (ap2 Pair payBT payCT)) bb
        ext_a  = liftFstSndSnd_evalPair3 tagCode_axEqCongR payGT payAT
                   (ap2 Pair payBT payCT) bb
        ext_b  = liftFstSndSndSnd_evalPair4 tagCode_axEqCongR payGT payAT payBT payCT bb
        ext_c  = liftSndSndSndSnd_evalPair4 tagCode_axEqCongR payGT payAT payBT payCT bb
        ab_pair = pairOfFan_eval (Lift (Comp Fst (Comp Snd Snd)))
                    (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) a bb
                    payAT payBT ext_a ext_b
        ca_pair = pairOfFan_eval (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                    (Lift (Comp Fst (Comp Snd Snd))) a bb
                    payCT payAT ext_c ext_a
        cb_pair = pairOfFan_eval (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                    (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) a bb
                    payCT payBT ext_c ext_b
        g_ca = pairOfFan_eval (Lift (Comp Fst Snd))
                 (Fan (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                      (Lift (Comp Fst (Comp Snd Snd))) Pair)
                 a bb payGT (ap2 Pair payCT payAT) ext_g ca_pair
        g_cb = pairOfFan_eval (Lift (Comp Fst Snd))
                 (Fan (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                      (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) Pair)
                 a bb payGT (ap2 Pair payCT payBT) ext_g cb_pair
        ka2_g_ca = pairOfConst_eval K_a2V K_a2V_isValue
                     (Fan (Lift (Comp Fst Snd))
                          (Fan (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                               (Lift (Comp Fst (Comp Snd Snd))) Pair)
                          Pair)
                     a bb (ap2 Pair payGT (ap2 Pair payCT payAT)) g_ca
        ka2_g_cb = pairOfConst_eval K_a2V K_a2V_isValue
                     (Fan (Lift (Comp Fst Snd))
                          (Fan (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                               (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) Pair)
                          Pair)
                     a bb (ap2 Pair payGT (ap2 Pair payCT payBT)) g_cb
        ka2_pair = pairOfFan_eval
                     (Fan (Lift (KT K_a2))
                          (Fan (Lift (Comp Fst Snd))
                               (Fan (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                    (Lift (Comp Fst (Comp Snd Snd))) Pair)
                               Pair) Pair)
                     (Fan (Lift (KT K_a2))
                          (Fan (Lift (Comp Fst Snd))
                               (Fan (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                    (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) Pair)
                               Pair) Pair)
                     a bb
                     (ap2 Pair K_a2 (ap2 Pair payGT (ap2 Pair payCT payAT)))
                     (ap2 Pair K_a2 (ap2 Pair payGT (ap2 Pair payCT payBT)))
                     ka2_g_ca ka2_g_cb
        inner = pairOfFan_eval
                  (Fan (Lift (Comp Fst (Comp Snd Snd)))
                       (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) Pair)
                  (Fan (Fan (Lift (KT K_a2))
                            (Fan (Lift (Comp Fst Snd))
                                 (Fan (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                      (Lift (Comp Fst (Comp Snd Snd))) Pair)
                                 Pair) Pair)
                       (Fan (Lift (KT K_a2))
                            (Fan (Lift (Comp Fst Snd))
                                 (Fan (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                      (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) Pair)
                                 Pair) Pair)
                       Pair)
                  a bb
                  (ap2 Pair payAT payBT)
                  (ap2 Pair (ap2 Pair K_a2 (ap2 Pair payGT (ap2 Pair payCT payAT)))
                             (ap2 Pair K_a2 (ap2 Pair payGT (ap2 Pair payCT payBT))))
                  ab_pair ka2_pair
    in pairOfConst_eval K_impV K_impV_isValue
         (Fan (Fan (Lift (Comp Fst (Comp Snd Snd)))
                   (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) Pair)
              (Fan (Fan (Lift (KT K_a2))
                        (Fan (Lift (Comp Fst Snd))
                             (Fan (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                  (Lift (Comp Fst (Comp Snd Snd))) Pair)
                             Pair) Pair)
                   (Fan (Lift (KT K_a2))
                        (Fan (Lift (Comp Fst Snd))
                             (Fan (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                  (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) Pair)
                             Pair) Pair)
                   Pair)
              Pair)
         a bb
         (ap2 Pair (ap2 Pair payAT payBT)
           (ap2 Pair (ap2 Pair K_a2 (ap2 Pair payGT (ap2 Pair payCT payAT)))
                      (ap2 Pair K_a2 (ap2 Pair payGT (ap2 Pair payCT payBT)))))
         inner
