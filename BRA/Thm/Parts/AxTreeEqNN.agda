{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.Parts.AxTreeEqNN
--
-- Self-contained dispatch material for
--   axTreeEqNN : Deriv (ap2 TreeEq (ap2 Pair a1 a2) (ap2 Pair b1 b2)
--                         =  ap2 IfLf (ap2 TreeEq a1 b1)
--                                     (ap2 Pair (ap2 TreeEq a2 b2)
--                                               (ap2 Pair O O))) .
--
-- Contents: encAxTreeEqNN, outAxTreeEqNN, body_axTreeEqNN, body_axTreeEqNN_eval.

module BRA.Thm.Parts.AxTreeEqNN where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Thm.Tag using (tagAxTreeEqNN)
open import BRA.Thm.TagCodes
open import BRA.Thm.EvalHelpers

------------------------------------------------------------------------
-- Encoded proof-tree input and intended Tree output.

encAxTreeEqNN : Term -> Term -> Term -> Term -> Tree
encAxTreeEqNN a1 a2 b1 b2 = nd (natCode tagAxTreeEqNN)
                               (nd (code a1)
                                   (nd (code a2)
                                       (nd (code b1) (code b2))))

outAxTreeEqNN : Term -> Term -> Term -> Term -> Tree
outAxTreeEqNN a1 a2 b1 b2 =
  codeFormula (atomic (eqn (ap2 TreeEq (ap2 Pair a1 a2) (ap2 Pair b1 b2))
                           (ap2 IfLf (ap2 TreeEq a1 b1)
                                     (ap2 Pair (ap2 TreeEq a2 b2)
                                               (ap2 Pair O O)))))

------------------------------------------------------------------------
-- body_axTreeEqNN.
--
-- axTreeEqNN a1 a2 b1 b2 :
--   LHS = ap2 TreeEq (ap2 Pair a1 a2) (ap2 Pair b1 b2)
--   RHS = ap2 IfLf (ap2 TreeEq a1 b1)
--                  (ap2 Pair (ap2 TreeEq a2 b2) (ap2 Pair O O))
--   payT depth 4: Pair payA1 (Pair payA2 (Pair payB1 payB2)).

body_axTreeEqNN : Fun2
body_axTreeEqNN =
  Fan
    -- LHS-build:
    --   Pair K_a2 (Pair K_te (Pair (Pair K_a2 (Pair K_pair (Pair payA1 payA2)))
    --                               (Pair K_a2 (Pair K_pair (Pair payB1 payB2)))))
    (Fan (Lift (KT (reify tagAp2)))
         (Fan (Lift (KT (reify (codeF2 TreeEq))))
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
    -- RHS-build:
    --   Pair K_a2 (Pair K_ifLf
    --     (Pair (Pair K_a2 (Pair K_te (Pair payA1 payB1)))
    --           (Pair K_a2 (Pair K_pair
    --             (Pair (Pair K_a2 (Pair K_te (Pair payA2 payB2)))
    --                   (Pair K_a2 (Pair K_pair (Pair K_oo K_oo))))))))
    (Fan (Lift (KT (reify tagAp2)))
         (Fan (Lift (KT (reify (codeF2 IfLf))))
              (Fan
                  (Fan (Lift (KT (reify tagAp2)))
                       (Fan (Lift (KT (reify (codeF2 TreeEq))))
                            (Fan (Lift (Comp Fst Snd))
                                 (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                 Pair)
                            Pair)
                       Pair)
                  (Fan (Lift (KT (reify tagAp2)))
                       (Fan (Lift (KT (reify (codeF2 Pair))))
                            (Fan
                                (Fan (Lift (KT (reify tagAp2)))
                                     (Fan (Lift (KT (reify (codeF2 TreeEq))))
                                          (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                               (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                               Pair)
                                          Pair)
                                     Pair)
                                (Fan (Lift (KT (reify tagAp2)))
                                     (Fan (Lift (KT (reify (codeF2 Pair))))
                                          (Fan (Lift (KT O))
                                               (Lift (KT O))
                                               Pair)
                                          Pair)
                                     Pair)
                                Pair)
                            Pair)
                       Pair)
                  Pair)
              Pair)
         Pair)
    Pair

------------------------------------------------------------------------
-- body_axTreeEqNN_eval.

abstract

  -- axTreeEqNN a1 a2 b1 b2 : 4 args; depth-4 payload.  Two large branches.
  body_axTreeEqNN_eval : (a1 a2 b1 b2 bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axTreeEqNN
            (ap2 Pair tagCode_axTreeEqNN
              (reify (nd (code a1) (nd (code a2) (nd (code b1) (code b2)))))) bb)
      (reify (outAxTreeEqNN a1 a2 b1 b2))))
  body_axTreeEqNN_eval a1 a2 b1 b2 bb =
    let payA1  = reify (code a1)
        payA2  = reify (code a2)
        payB1  = reify (code b1)
        payB2  = reify (code b2)
        payT   = ap2 Pair payA1 (ap2 Pair payA2 (ap2 Pair payB1 payB2))
        a      = ap2 Pair tagCode_axTreeEqNN payT
        K_a2V  = tagAp2
        K_a2   = reify K_a2V
        K_teV  = codeF2 TreeEq
        K_te   = reify K_teV
        K_ifLfV = codeF2 IfLf
        K_ifLf = reify K_ifLfV
        K_pairV = codeF2 Pair
        K_pair = reify K_pairV
        K_ooV  = lf                                -- post-redesign: code O = lf, reify = O
        K_oo   = reify K_ooV
        ext_a1 = liftCompFstSnd_evalPair tagCode_axTreeEqNN payA1
                   (ap2 Pair payA2 (ap2 Pair payB1 payB2)) bb
        ext_a2 = liftFstSndSnd_evalPair3 tagCode_axTreeEqNN payA1 payA2
                   (ap2 Pair payB1 payB2) bb
        ext_b1 = liftFstSndSndSnd_evalPair4 tagCode_axTreeEqNN payA1 payA2 payB1 payB2 bb
        ext_b2 = liftSndSndSndSnd_evalPair4 tagCode_axTreeEqNN payA1 payA2 payB1 payB2 bb
        kOO    = liftKT_eval K_ooV a bb
        ----------------------------------------------------------------
        -- LHS shape: Pair K_a2 (Pair K_te
        --              (Pair (Pair K_a2 (Pair K_pair (Pair payA1 payA2)))
        --                    (Pair K_a2 (Pair K_pair (Pair payB1 payB2)))))
        a1a2   = pairOfFan_eval (Lift (Comp Fst Snd))
                   (Lift (Comp Fst (Comp Snd Snd))) a bb
                   payA1 payA2 ext_a1 ext_a2
        ka1a2  = pairOfConst_eval K_pairV
                   (Fan (Lift (Comp Fst Snd))
                        (Lift (Comp Fst (Comp Snd Snd))) Pair)
                   a bb (ap2 Pair payA1 payA2) a1a2
        a_full = pairOfConst_eval K_a2V
                   (Fan (Lift (KT K_pair))
                        (Fan (Lift (Comp Fst Snd))
                             (Lift (Comp Fst (Comp Snd Snd))) Pair)
                        Pair)
                   a bb (ap2 Pair K_pair (ap2 Pair payA1 payA2)) ka1a2
        b1b2   = pairOfFan_eval (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                   (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) a bb
                   payB1 payB2 ext_b1 ext_b2
        kb1b2  = pairOfConst_eval K_pairV
                   (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                        (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                   a bb (ap2 Pair payB1 payB2) b1b2
        b_full = pairOfConst_eval K_a2V
                   (Fan (Lift (KT K_pair))
                        (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                             (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                        Pair)
                   a bb (ap2 Pair K_pair (ap2 Pair payB1 payB2)) kb1b2
        l_inner = pairOfFan_eval
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
                    (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payA1 payA2)))
                    (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payB1 payB2)))
                    a_full b_full
        l_te   = pairOfConst_eval K_teV
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
                        Pair)
                   a bb
                   (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payA1 payA2)))
                              (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payB1 payB2))))
                   l_inner
        lhsBuild = pairOfConst_eval K_a2V
                     (Fan (Lift (KT K_te))
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
                     (ap2 Pair K_te
                       (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payA1 payA2)))
                                  (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payB1 payB2)))))
                     l_te
        ----------------------------------------------------------------
        -- RHS shape: Pair K_a2 (Pair K_ifLf
        --              (Pair (Pair K_a2 (Pair K_te (Pair payA1 payB1)))
        --                    (Pair K_a2 (Pair K_pair
        --                      (Pair (Pair K_a2 (Pair K_te (Pair payA2 payB2)))
        --                            (Pair K_a2 (Pair K_pair (Pair K_oo K_oo))))))))
        -- Block A: (Pair K_a2 (Pair K_te (Pair payA1 payB1)))
        a1b1   = pairOfFan_eval (Lift (Comp Fst Snd))
                   (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) a bb
                   payA1 payB1 ext_a1 ext_b1
        kA1B1  = pairOfConst_eval K_teV
                   (Fan (Lift (Comp Fst Snd))
                        (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) Pair)
                   a bb (ap2 Pair payA1 payB1) a1b1
        blkA   = pairOfConst_eval K_a2V
                   (Fan (Lift (KT K_te))
                        (Fan (Lift (Comp Fst Snd))
                             (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) Pair)
                        Pair)
                   a bb (ap2 Pair K_te (ap2 Pair payA1 payB1)) kA1B1
        -- Block B-inner: (Pair K_a2 (Pair K_te (Pair payA2 payB2)))
        a2b2   = pairOfFan_eval (Lift (Comp Fst (Comp Snd Snd)))
                   (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) a bb
                   payA2 payB2 ext_a2 ext_b2
        kA2B2  = pairOfConst_eval K_teV
                   (Fan (Lift (Comp Fst (Comp Snd Snd)))
                        (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                   a bb (ap2 Pair payA2 payB2) a2b2
        blkBin = pairOfConst_eval K_a2V
                   (Fan (Lift (KT K_te))
                        (Fan (Lift (Comp Fst (Comp Snd Snd)))
                             (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                        Pair)
                   a bb (ap2 Pair K_te (ap2 Pair payA2 payB2)) kA2B2
        -- Block PairOO-coded: (Pair K_a2 (Pair K_pair (Pair K_oo K_oo)))
        ooOO   = pairOfFan_eval (Lift (KT K_oo)) (Lift (KT K_oo))
                   a bb K_oo K_oo kOO kOO
        kPOO   = pairOfConst_eval K_pairV
                   (Fan (Lift (KT K_oo)) (Lift (KT K_oo)) Pair)
                   a bb (ap2 Pair K_oo K_oo) ooOO
        blkPOO = pairOfConst_eval K_a2V
                   (Fan (Lift (KT K_pair))
                        (Fan (Lift (KT K_oo)) (Lift (KT K_oo)) Pair) Pair)
                   a bb (ap2 Pair K_pair (ap2 Pair K_oo K_oo)) kPOO
        -- Block C: (Pair K_a2 (Pair K_pair (Pair blkBin blkPOO)))
        binPOO = pairOfFan_eval
                   (Fan (Lift (KT K_a2))
                        (Fan (Lift (KT K_te))
                             (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                  (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                             Pair) Pair)
                   (Fan (Lift (KT K_a2))
                        (Fan (Lift (KT K_pair))
                             (Fan (Lift (KT K_oo)) (Lift (KT K_oo)) Pair) Pair)
                        Pair)
                   a bb
                   (ap2 Pair K_a2 (ap2 Pair K_te (ap2 Pair payA2 payB2)))
                   (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair K_oo K_oo)))
                   blkBin blkPOO
        kBinPOO = pairOfConst_eval K_pairV
                    (Fan (Fan (Lift (KT K_a2))
                              (Fan (Lift (KT K_te))
                                   (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                        (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                        Pair)
                                   Pair) Pair)
                         (Fan (Lift (KT K_a2))
                              (Fan (Lift (KT K_pair))
                                   (Fan (Lift (KT K_oo)) (Lift (KT K_oo)) Pair)
                                   Pair) Pair)
                         Pair)
                    a bb
                    (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_te (ap2 Pair payA2 payB2)))
                               (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair K_oo K_oo))))
                    binPOO
        blkC   = pairOfConst_eval K_a2V
                   (Fan (Lift (KT K_pair))
                        (Fan (Fan (Lift (KT K_a2))
                                  (Fan (Lift (KT K_te))
                                       (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                            (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                            Pair)
                                       Pair) Pair)
                             (Fan (Lift (KT K_a2))
                                  (Fan (Lift (KT K_pair))
                                       (Fan (Lift (KT K_oo)) (Lift (KT K_oo)) Pair)
                                       Pair) Pair)
                             Pair) Pair)
                   a bb
                   (ap2 Pair K_pair
                     (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_te (ap2 Pair payA2 payB2)))
                                (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair K_oo K_oo)))))
                   kBinPOO
        -- Combine blkA and blkC -> inner Pair
        r_inner = pairOfFan_eval
                    (Fan (Lift (KT K_a2))
                         (Fan (Lift (KT K_te))
                              (Fan (Lift (Comp Fst Snd))
                                   (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) Pair)
                              Pair) Pair)
                    (Fan (Lift (KT K_a2))
                         (Fan (Lift (KT K_pair))
                              (Fan (Fan (Lift (KT K_a2))
                                        (Fan (Lift (KT K_te))
                                             (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                                  (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                                  Pair)
                                             Pair) Pair)
                                   (Fan (Lift (KT K_a2))
                                        (Fan (Lift (KT K_pair))
                                             (Fan (Lift (KT K_oo)) (Lift (KT K_oo))
                                                  Pair)
                                             Pair) Pair)
                                   Pair) Pair) Pair)
                    a bb
                    (ap2 Pair K_a2 (ap2 Pair K_te (ap2 Pair payA1 payB1)))
                    (ap2 Pair K_a2
                      (ap2 Pair K_pair
                        (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_te (ap2 Pair payA2 payB2)))
                                   (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair K_oo K_oo))))))
                    blkA blkC
        r_ifLf  = pairOfConst_eval K_ifLfV
                    (Fan (Fan (Lift (KT K_a2))
                              (Fan (Lift (KT K_te))
                                   (Fan (Lift (Comp Fst Snd))
                                        (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) Pair)
                                   Pair) Pair)
                         (Fan (Lift (KT K_a2))
                              (Fan (Lift (KT K_pair))
                                   (Fan (Fan (Lift (KT K_a2))
                                             (Fan (Lift (KT K_te))
                                                  (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                                       (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                                       Pair)
                                                  Pair) Pair)
                                        (Fan (Lift (KT K_a2))
                                             (Fan (Lift (KT K_pair))
                                                  (Fan (Lift (KT K_oo)) (Lift (KT K_oo))
                                                       Pair)
                                                  Pair) Pair)
                                        Pair) Pair) Pair)
                         Pair)
                    a bb
                    (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_te (ap2 Pair payA1 payB1)))
                               (ap2 Pair K_a2
                                 (ap2 Pair K_pair
                                   (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_te (ap2 Pair payA2 payB2)))
                                              (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair K_oo K_oo)))))))
                    r_inner
        rhsBuild = pairOfConst_eval K_a2V
                     (Fan (Lift (KT K_ifLf))
                          (Fan (Fan (Lift (KT K_a2))
                                    (Fan (Lift (KT K_te))
                                         (Fan (Lift (Comp Fst Snd))
                                              (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                              Pair)
                                         Pair) Pair)
                               (Fan (Lift (KT K_a2))
                                    (Fan (Lift (KT K_pair))
                                         (Fan (Fan (Lift (KT K_a2))
                                                   (Fan (Lift (KT K_te))
                                                        (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                                             (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                                             Pair)
                                                        Pair) Pair)
                                              (Fan (Lift (KT K_a2))
                                                   (Fan (Lift (KT K_pair))
                                                        (Fan (Lift (KT K_oo))
                                                             (Lift (KT K_oo))
                                                             Pair)
                                                        Pair) Pair)
                                              Pair) Pair) Pair)
                               Pair) Pair)
                     a bb
                     (ap2 Pair K_ifLf
                       (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_te (ap2 Pair payA1 payB1)))
                                  (ap2 Pair K_a2
                                    (ap2 Pair K_pair
                                      (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_te (ap2 Pair payA2 payB2)))
                                                 (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair K_oo K_oo))))))))
                     r_ifLf
    in pairOfFan_eval
         (Fan (Lift (KT K_a2))
              (Fan (Lift (KT K_te))
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
         (Fan (Lift (KT K_a2))
              (Fan (Lift (KT K_ifLf))
                   (Fan (Fan (Lift (KT K_a2))
                             (Fan (Lift (KT K_te))
                                  (Fan (Lift (Comp Fst Snd))
                                       (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                       Pair)
                                  Pair) Pair)
                        (Fan (Lift (KT K_a2))
                             (Fan (Lift (KT K_pair))
                                  (Fan (Fan (Lift (KT K_a2))
                                            (Fan (Lift (KT K_te))
                                                 (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                                      (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                                      Pair)
                                                 Pair) Pair)
                                       (Fan (Lift (KT K_a2))
                                            (Fan (Lift (KT K_pair))
                                                 (Fan (Lift (KT K_oo))
                                                      (Lift (KT K_oo))
                                                      Pair)
                                                 Pair) Pair)
                                       Pair) Pair) Pair)
                        Pair) Pair) Pair)
         a bb
         (ap2 Pair K_a2
           (ap2 Pair K_te
             (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payA1 payA2)))
                        (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payB1 payB2))))))
         (ap2 Pair K_a2
           (ap2 Pair K_ifLf
             (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_te (ap2 Pair payA1 payB1)))
                        (ap2 Pair K_a2
                          (ap2 Pair K_pair
                            (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_te (ap2 Pair payA2 payB2)))
                                       (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair K_oo K_oo)))))))))
         lhsBuild rhsBuild
