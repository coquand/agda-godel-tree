{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.Parts.AxEqCongL
--
-- Self-contained dispatch material for the binary left equality-congruence axiom (Guard Ax 6):
--   axEqCongL : Deriv ((atomic (eqn a b))
--                        imp (atomic (eqn (ap2 g a c) (ap2 g b c)))) .
--
-- Contents: encAxEqCongL, outAxEqCongL, body_axEqCongL, body_axEqCongL_eval.

module BRA.Thm.Parts.AxEqCongL where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Thm.Tag using (tagAxEqCongL)
open import BRA.Thm.TagCodes
open import BRA.Thm.EvalHelpers

------------------------------------------------------------------------
-- Encoded proof-tree input and intended Tree output.

encAxEqCongL : Fun2 -> Term -> Term -> Term -> Tree
encAxEqCongL g a b c = nd (natCode tagAxEqCongL)
                          (nd (codeF2 g)
                              (nd (code a)
                                  (nd (code b) (code c))))

outAxEqCongL : Fun2 -> Term -> Term -> Term -> Tree
outAxEqCongL g a b c = codeFormula ((atomic (eqn a b))
                                      imp (atomic (eqn (ap2 g a c) (ap2 g b c))))

------------------------------------------------------------------------
-- body_axEqCongL.
--
-- axEqCongL g a b c : conclusion =
--   (atomic (eqn a b)) imp (atomic (eqn (ap2 g a c) (ap2 g b c)))
--   payT depth 4: Pair payGT (Pair payAT (Pair payBT payCT)).

body_axEqCongL : Fun2
body_axEqCongL =
  Fan (Lift (KT (reify tagImp)))
      (Fan (Fan (Lift (Comp Fst (Comp Snd Snd)))
                (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                Pair)
           (Fan (Fan (Lift (KT (reify tagAp2)))
                     (Fan (Lift (Comp Fst Snd))
                          (Fan (Lift (Comp Fst (Comp Snd Snd)))
                               (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                               Pair)
                          Pair)
                     Pair)
                (Fan (Lift (KT (reify tagAp2)))
                     (Fan (Lift (Comp Fst Snd))
                          (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                               (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                               Pair)
                          Pair)
                     Pair)
                Pair)
           Pair)
      Pair

------------------------------------------------------------------------
-- body_axEqCongL_eval.

abstract

  -- axEqCongL g a b c : 4 args (g : Fun2, a, b, c : Term); depth-4 payload.
  body_axEqCongL_eval : (g : Fun2) (a' b' c' bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axEqCongL
            (ap2 Pair tagCode_axEqCongL
              (reify (nd (codeF2 g) (nd (code a') (nd (code b') (code c')))))) bb)
      (reify (outAxEqCongL g a' b' c'))))
  body_axEqCongL_eval g a' b' c' bb =
    let payGT  = reify (codeF2 g)
        payAT  = reify (code a')
        payBT  = reify (code b')
        payCT  = reify (code c')
        payT   = ap2 Pair payGT (ap2 Pair payAT (ap2 Pair payBT payCT))
        a      = ap2 Pair tagCode_axEqCongL payT
        K_impV = tagImp
        K_imp  = reify K_impV
        K_a2V  = tagAp2
        K_a2   = reify K_a2V
        ext_g  = liftCompFstSnd_evalPair tagCode_axEqCongL payGT
                   (ap2 Pair payAT (ap2 Pair payBT payCT)) bb
        ext_a  = liftFstSndSnd_evalPair3 tagCode_axEqCongL payGT payAT
                   (ap2 Pair payBT payCT) bb
        ext_b  = liftFstSndSndSnd_evalPair4 tagCode_axEqCongL payGT payAT payBT payCT bb
        ext_c  = liftSndSndSndSnd_evalPair4 tagCode_axEqCongL payGT payAT payBT payCT bb
        ab_pair = pairOfFan_eval (Lift (Comp Fst (Comp Snd Snd)))
                    (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) a bb
                    payAT payBT ext_a ext_b
        ac_pair = pairOfFan_eval (Lift (Comp Fst (Comp Snd Snd)))
                    (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) a bb
                    payAT payCT ext_a ext_c
        bc_pair = pairOfFan_eval (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                    (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) a bb
                    payBT payCT ext_b ext_c
        g_ac = pairOfFan_eval (Lift (Comp Fst Snd))
                 (Fan (Lift (Comp Fst (Comp Snd Snd)))
                      (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                 a bb payGT (ap2 Pair payAT payCT) ext_g ac_pair
        g_bc = pairOfFan_eval (Lift (Comp Fst Snd))
                 (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                      (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                 a bb payGT (ap2 Pair payBT payCT) ext_g bc_pair
        ka2_g_ac = pairOfConst_eval K_a2V
                     (Fan (Lift (Comp Fst Snd))
                          (Fan (Lift (Comp Fst (Comp Snd Snd)))
                               (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                          Pair)
                     a bb (ap2 Pair payGT (ap2 Pair payAT payCT)) g_ac
        ka2_g_bc = pairOfConst_eval K_a2V
                     (Fan (Lift (Comp Fst Snd))
                          (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                               (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                          Pair)
                     a bb (ap2 Pair payGT (ap2 Pair payBT payCT)) g_bc
        ka2_pair = pairOfFan_eval
                     (Fan (Lift (KT K_a2))
                          (Fan (Lift (Comp Fst Snd))
                               (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                    (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                               Pair) Pair)
                     (Fan (Lift (KT K_a2))
                          (Fan (Lift (Comp Fst Snd))
                               (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                    (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                               Pair) Pair)
                     a bb
                     (ap2 Pair K_a2 (ap2 Pair payGT (ap2 Pair payAT payCT)))
                     (ap2 Pair K_a2 (ap2 Pair payGT (ap2 Pair payBT payCT)))
                     ka2_g_ac ka2_g_bc
        inner = pairOfFan_eval
                  (Fan (Lift (Comp Fst (Comp Snd Snd)))
                       (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) Pair)
                  (Fan (Fan (Lift (KT K_a2))
                            (Fan (Lift (Comp Fst Snd))
                                 (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                      (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                                 Pair) Pair)
                       (Fan (Lift (KT K_a2))
                            (Fan (Lift (Comp Fst Snd))
                                 (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                      (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                                 Pair) Pair)
                       Pair)
                  a bb
                  (ap2 Pair payAT payBT)
                  (ap2 Pair (ap2 Pair K_a2 (ap2 Pair payGT (ap2 Pair payAT payCT)))
                             (ap2 Pair K_a2 (ap2 Pair payGT (ap2 Pair payBT payCT))))
                  ab_pair ka2_pair
    in pairOfConst_eval K_impV
         (Fan (Fan (Lift (Comp Fst (Comp Snd Snd)))
                   (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) Pair)
              (Fan (Fan (Lift (KT K_a2))
                        (Fan (Lift (Comp Fst Snd))
                             (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                  (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                             Pair) Pair)
                   (Fan (Lift (KT K_a2))
                        (Fan (Lift (Comp Fst Snd))
                             (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                  (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                             Pair) Pair)
                   Pair)
              Pair)
         a bb
         (ap2 Pair (ap2 Pair payAT payBT)
           (ap2 Pair (ap2 Pair K_a2 (ap2 Pair payGT (ap2 Pair payAT payCT)))
                      (ap2 Pair K_a2 (ap2 Pair payGT (ap2 Pair payBT payCT)))))
         inner
