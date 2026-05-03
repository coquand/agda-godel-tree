{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.Parts.AxIfLfN
--
-- Self-contained dispatch material for
--   axIfLfN : Deriv (ap2 IfLf (ap2 Pair x y) (ap2 Pair a b) = b) .
--
-- Contents: encAxIfLfN, outAxIfLfN, body_axIfLfN, body_axIfLfN_eval.

module BRA.Thm.Parts.AxIfLfN where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Thm.Tag using (tagAxIfLfN)
open import BRA.Thm.TagCodes
open import BRA.Thm.EvalHelpers

------------------------------------------------------------------------
-- Encoded proof-tree input and intended Tree output.

encAxIfLfN : Term -> Term -> Term -> Term -> Tree
encAxIfLfN x y a b = nd (natCode tagAxIfLfN)
                        (nd (code x)
                            (nd (code y)
                                (nd (code a) (code b))))

outAxIfLfN : Term -> Term -> Term -> Term -> Tree
outAxIfLfN x y a b = codeFormula (atomic (eqn (ap2 IfLf (ap2 Pair x y)
                                                         (ap2 Pair a b))
                                                b))

------------------------------------------------------------------------
-- body_axIfLfN.
--
-- axIfLfN x y a b : LHS = ap2 IfLf (ap2 Pair x y) (ap2 Pair a b) , RHS = b .
--   payT depth 4: Pair payX (Pair payY (Pair payAT payBT)).

body_axIfLfN : Fun2
body_axIfLfN =
  Fan
    (Fan (Lift (KT (reify tagAp2)))
         (Fan (Lift (KT (reify (codeF2 IfLf))))
              (Fan
                  (Fan (Lift (KT (reify tagAp2)))
                       (Fan (Lift (KT (reify (codeF2 Pair))))
                            (Fan (Lift (Comp Fst Snd))
                                 (Lift (Comp Fst (Comp Snd Snd)))
                                 Pair)
                            Pair)
                       Pair)
                  (Fan (Lift (KT (reify tagAp2)))
                       (Fan (Lift (KT (reify (codeF2 Pair))))
                            (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                 (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                 Pair)
                            Pair)
                       Pair)
                  Pair)
              Pair)
         Pair)
    (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
    Pair

------------------------------------------------------------------------
-- body_axIfLfN_eval.

abstract

  -- axIfLfN x y a b : 4 args; depth-4 payload.
  body_axIfLfN_eval : (x y a' b' bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axIfLfN
            (ap2 Pair tagCode_axIfLfN
              (reify (nd (code x) (nd (code y) (nd (code a') (code b')))))) bb)
      (reify (outAxIfLfN x y a' b'))))
  body_axIfLfN_eval x y a' b' bb =
    let payX   = reify (code x)
        payY   = reify (code y)
        payAT  = reify (code a')
        payBT  = reify (code b')
        payT   = ap2 Pair payX (ap2 Pair payY (ap2 Pair payAT payBT))
        a      = ap2 Pair tagCode_axIfLfN payT
        K_a2V  = tagAp2
        K_a2   = reify K_a2V
        K_ifLfV = codeF2 IfLf
        K_ifLf = reify K_ifLfV
        K_pairV = codeF2 Pair
        K_pair = reify K_pairV
        ext_x  = liftCompFstSnd_evalPair tagCode_axIfLfN payX
                   (ap2 Pair payY (ap2 Pair payAT payBT)) bb
        ext_y  = liftFstSndSnd_evalPair3 tagCode_axIfLfN payX payY
                   (ap2 Pair payAT payBT) bb
        ext_a  = liftFstSndSndSnd_evalPair4 tagCode_axIfLfN payX payY payAT payBT bb
        ext_b  = liftSndSndSndSnd_evalPair4 tagCode_axIfLfN payX payY payAT payBT bb
        -- xy-block: (Pair K_a2 (Pair K_pair (Pair payX payY)))
        xy_pair  = pairOfFan_eval (Lift (Comp Fst Snd))
                     (Lift (Comp Fst (Comp Snd Snd))) a bb
                     payX payY ext_x ext_y
        xy_KP    = pairOfConst_eval K_pairV
                     (Fan (Lift (Comp Fst Snd))
                          (Lift (Comp Fst (Comp Snd Snd))) Pair)
                     a bb (ap2 Pair payX payY) xy_pair
        xy_full  = pairOfConst_eval K_a2V
                     (Fan (Lift (KT K_pair))
                          (Fan (Lift (Comp Fst Snd))
                               (Lift (Comp Fst (Comp Snd Snd))) Pair)
                          Pair)
                     a bb (ap2 Pair K_pair (ap2 Pair payX payY)) xy_KP
        -- ab-block: (Pair K_a2 (Pair K_pair (Pair payAT payBT)))
        ab_pair  = pairOfFan_eval
                     (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                     (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) a bb
                     payAT payBT ext_a ext_b
        ab_KP    = pairOfConst_eval K_pairV
                     (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                          (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                     a bb (ap2 Pair payAT payBT) ab_pair
        ab_full  = pairOfConst_eval K_a2V
                     (Fan (Lift (KT K_pair))
                          (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                               (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                               Pair)
                          Pair)
                     a bb (ap2 Pair K_pair (ap2 Pair payAT payBT)) ab_KP
        -- Combine xy and ab.
        xy_ab    = pairOfFan_eval
                     (Fan (Lift (KT K_a2))
                          (Fan (Lift (KT K_pair))
                               (Fan (Lift (Comp Fst Snd))
                                    (Lift (Comp Fst (Comp Snd Snd))) Pair)
                               Pair) Pair)
                     (Fan (Lift (KT K_a2))
                          (Fan (Lift (KT K_pair))
                               (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                    (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                    Pair)
                               Pair) Pair)
                     a bb
                     (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payX payY)))
                     (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT)))
                     xy_full ab_full
        ifLf_inner = pairOfConst_eval K_ifLfV
                       (Fan (Fan (Lift (KT K_a2))
                                 (Fan (Lift (KT K_pair))
                                      (Fan (Lift (Comp Fst Snd))
                                           (Lift (Comp Fst (Comp Snd Snd)))
                                           Pair)
                                      Pair) Pair)
                            (Fan (Lift (KT K_a2))
                                 (Fan (Lift (KT K_pair))
                                      (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                           (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                           Pair)
                                      Pair) Pair)
                            Pair)
                       a bb
                       (ap2 Pair (ap2 Pair K_a2
                                   (ap2 Pair K_pair (ap2 Pair payX payY)))
                                  (ap2 Pair K_a2
                                   (ap2 Pair K_pair (ap2 Pair payAT payBT))))
                       xy_ab
        lhsBuild = pairOfConst_eval K_a2V
                     (Fan (Lift (KT K_ifLf))
                          (Fan (Fan (Lift (KT K_a2))
                                    (Fan (Lift (KT K_pair))
                                         (Fan (Lift (Comp Fst Snd))
                                              (Lift (Comp Fst (Comp Snd Snd)))
                                              Pair)
                                         Pair) Pair)
                               (Fan (Lift (KT K_a2))
                                    (Fan (Lift (KT K_pair))
                                         (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                              (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                              Pair)
                                         Pair) Pair)
                               Pair) Pair)
                     a bb
                     (ap2 Pair K_ifLf
                       (ap2 Pair (ap2 Pair K_a2
                                   (ap2 Pair K_pair (ap2 Pair payX payY)))
                                  (ap2 Pair K_a2
                                   (ap2 Pair K_pair (ap2 Pair payAT payBT)))))
                     ifLf_inner
    in pairOfFan_eval
         (Fan (Lift (KT K_a2))
              (Fan (Lift (KT K_ifLf))
                   (Fan (Fan (Lift (KT K_a2))
                             (Fan (Lift (KT K_pair))
                                  (Fan (Lift (Comp Fst Snd))
                                       (Lift (Comp Fst (Comp Snd Snd))) Pair)
                                  Pair) Pair)
                        (Fan (Lift (KT K_a2))
                             (Fan (Lift (KT K_pair))
                                  (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                       (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                       Pair)
                                  Pair) Pair)
                        Pair) Pair) Pair)
         (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) a bb
         (ap2 Pair K_a2 (ap2 Pair K_ifLf
            (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payX payY)))
                       (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT))))))
         payBT
         lhsBuild ext_b
