{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.Parts.AxGoodstein
--
-- Self-contained dispatch material for the tree analog of Goodstein's
-- characteristic equation:
--   axGoodstein : Deriv (ap2 IfLf (ap2 TreeEq a b) (ap2 Pair a O)
--                          =  ap2 IfLf (ap2 TreeEq a b) (ap2 Pair b O)) .
--
-- Contents: encAxGoodstein, outAxGoodstein, body_axGoodstein, body_axGoodstein_eval.

module BRA.Thm.Parts.AxGoodstein where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Thm.Tag using (tagAxGoodstein)
open import BRA.Thm.TagCodes
open import BRA.Thm.EvalHelpers

------------------------------------------------------------------------
-- Encoded proof-tree input and intended Tree output.

encAxGoodstein : Term -> Term -> Tree
encAxGoodstein a b = nd (natCode tagAxGoodstein) (nd (code a) (code b))

outAxGoodstein : Term -> Term -> Tree
outAxGoodstein a b =
  codeFormula (atomic (eqn (ap2 IfLf (ap2 TreeEq a b) (ap2 Pair a O))
                           (ap2 IfLf (ap2 TreeEq a b) (ap2 Pair b O))))

------------------------------------------------------------------------
-- body_axGoodstein.
--
-- axGoodstein a b :
--   LHS = ap2 IfLf (ap2 TreeEq a b) (ap2 Pair a O) ,
--   RHS = ap2 IfLf (ap2 TreeEq a b) (ap2 Pair b O) .
--   payT depth 2: Pair payAT payBT.
--   The two sides differ only in one position (payAT vs payBT).

body_axGoodstein : Fun2
body_axGoodstein =
  Fan
    -- LHS-build:
    --   Pair K_a2 (Pair K_ifLf
    --     (Pair (Pair K_a2 (Pair K_te payT))
    --           (Pair K_a2 (Pair K_pair (Pair payAT O)))))   -- code O = lf
    (Fan (Lift (KT (reify tagAp2)))
         (Fan (Lift (KT (reify (codeF2 IfLf))))
              (Fan
                  (Fan (Lift (KT (reify tagAp2)))
                       (Fan (Lift (KT (reify (codeF2 TreeEq))))
                            (Lift Snd)
                            Pair)
                       Pair)
                  (Fan (Lift (KT (reify tagAp2)))
                       (Fan (Lift (KT (reify (codeF2 Pair))))
                            (Fan (Lift (Comp Fst Snd))
                                 (Lift (KT O))
                                 Pair)
                            Pair)
                       Pair)
                  Pair)
              Pair)
         Pair)
    -- RHS-build: same shape as LHS, only payAT replaced by payBT.
    (Fan (Lift (KT (reify tagAp2)))
         (Fan (Lift (KT (reify (codeF2 IfLf))))
              (Fan
                  (Fan (Lift (KT (reify tagAp2)))
                       (Fan (Lift (KT (reify (codeF2 TreeEq))))
                            (Lift Snd)
                            Pair)
                       Pair)
                  (Fan (Lift (KT (reify tagAp2)))
                       (Fan (Lift (KT (reify (codeF2 Pair))))
                            (Fan (Lift (Comp Snd Snd))
                                 (Lift (KT O))
                                 Pair)
                            Pair)
                       Pair)
                  Pair)
              Pair)
         Pair)
    Pair

------------------------------------------------------------------------
-- body_axGoodstein_eval.

abstract

  -- axGoodstein a b : 2 args; depth-2 payload.  LHS and RHS are big.
  body_axGoodstein_eval : (a' b' bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axGoodstein
            (ap2 Pair tagCode_axGoodstein (reify (nd (code a') (code b')))) bb)
      (reify (outAxGoodstein a' b'))))
  body_axGoodstein_eval a' b' bb =
    let payAT  = reify (code a')
        payBT  = reify (code b')
        payT   = ap2 Pair payAT payBT
        a      = ap2 Pair tagCode_axGoodstein payT
        K_a2V  = tagAp2
        K_a2   = reify K_a2V
        K_ifLfV = codeF2 IfLf
        K_ifLf = reify K_ifLfV
        K_teV  = codeF2 TreeEq
        K_te   = reify K_teV
        K_pairV = codeF2 Pair
        K_pair = reify K_pairV
        K_ooV  = lf                                -- post-redesign: code O = lf, reify = O
        K_oo   = reify K_ooV
        snd_a  = bodyLiftSndPair tagCode_axGoodstein payT bb
        ext_a  = liftCompFstSnd_evalPair tagCode_axGoodstein payAT payBT bb
        ext_b  = liftCompSndSnd_evalPair tagCode_axGoodstein payAT payBT bb
        kOO    = liftKT_eval K_ooV a bb
        -- Shared TreeEq-part: (Pair K_a2 (Pair K_te payT))
        teInner = pairOfConst_eval K_teV (Lift Snd) a bb payT snd_a
        teFull  = pairOfConst_eval K_a2V
                    (Fan (Lift (KT K_te)) (Lift Snd) Pair) a bb
                    (ap2 Pair K_te payT) teInner
        -- LHS Pair-part: (Pair K_a2 (Pair K_pair (Pair payAT K_oo)))
        l_aoo  = pairOfFan_eval (Lift (Comp Fst Snd)) (Lift (KT K_oo))
                    a bb payAT K_oo ext_a kOO
        l_pair = pairOfConst_eval K_pairV
                    (Fan (Lift (Comp Fst Snd)) (Lift (KT K_oo)) Pair)
                    a bb (ap2 Pair payAT K_oo) l_aoo
        l_pFull = pairOfConst_eval K_a2V
                    (Fan (Lift (KT K_pair))
                         (Fan (Lift (Comp Fst Snd)) (Lift (KT K_oo)) Pair)
                         Pair)
                    a bb (ap2 Pair K_pair (ap2 Pair payAT K_oo)) l_pair
        -- LHS inner Fan: Pair (te-part) (pair-part)
        lhs_inner = pairOfFan_eval
                      (Fan (Lift (KT K_a2))
                           (Fan (Lift (KT K_te)) (Lift Snd) Pair) Pair)
                      (Fan (Lift (KT K_a2))
                           (Fan (Lift (KT K_pair))
                                (Fan (Lift (Comp Fst Snd)) (Lift (KT K_oo))
                                     Pair) Pair) Pair)
                      a bb
                      (ap2 Pair K_a2 (ap2 Pair K_te payT))
                      (ap2 Pair K_a2
                         (ap2 Pair K_pair (ap2 Pair payAT K_oo)))
                      teFull l_pFull
        lhs_ifLf = pairOfConst_eval K_ifLfV
                     (Fan (Fan (Lift (KT K_a2))
                               (Fan (Lift (KT K_te)) (Lift Snd) Pair) Pair)
                          (Fan (Lift (KT K_a2))
                               (Fan (Lift (KT K_pair))
                                    (Fan (Lift (Comp Fst Snd)) (Lift (KT K_oo))
                                         Pair) Pair) Pair)
                          Pair)
                     a bb
                     (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_te payT))
                                (ap2 Pair K_a2
                                  (ap2 Pair K_pair (ap2 Pair payAT K_oo))))
                     lhs_inner
        lhsBuild = pairOfConst_eval K_a2V
                     (Fan (Lift (KT K_ifLf))
                          (Fan (Fan (Lift (KT K_a2))
                                    (Fan (Lift (KT K_te)) (Lift Snd) Pair)
                                    Pair)
                               (Fan (Lift (KT K_a2))
                                    (Fan (Lift (KT K_pair))
                                         (Fan (Lift (Comp Fst Snd))
                                              (Lift (KT K_oo))
                                              Pair) Pair) Pair)
                               Pair) Pair)
                     a bb
                     (ap2 Pair K_ifLf
                       (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_te payT))
                                  (ap2 Pair K_a2
                                    (ap2 Pair K_pair (ap2 Pair payAT K_oo)))))
                     lhs_ifLf
        -- RHS Pair-part: (Pair K_a2 (Pair K_pair (Pair payBT K_oo)))
        r_boo  = pairOfFan_eval (Lift (Comp Snd Snd)) (Lift (KT K_oo))
                    a bb payBT K_oo ext_b kOO
        r_pair = pairOfConst_eval K_pairV
                    (Fan (Lift (Comp Snd Snd)) (Lift (KT K_oo)) Pair)
                    a bb (ap2 Pair payBT K_oo) r_boo
        r_pFull = pairOfConst_eval K_a2V
                    (Fan (Lift (KT K_pair))
                         (Fan (Lift (Comp Snd Snd)) (Lift (KT K_oo)) Pair)
                         Pair)
                    a bb (ap2 Pair K_pair (ap2 Pair payBT K_oo)) r_pair
        rhs_inner = pairOfFan_eval
                      (Fan (Lift (KT K_a2))
                           (Fan (Lift (KT K_te)) (Lift Snd) Pair) Pair)
                      (Fan (Lift (KT K_a2))
                           (Fan (Lift (KT K_pair))
                                (Fan (Lift (Comp Snd Snd)) (Lift (KT K_oo))
                                     Pair) Pair) Pair)
                      a bb
                      (ap2 Pair K_a2 (ap2 Pair K_te payT))
                      (ap2 Pair K_a2
                         (ap2 Pair K_pair (ap2 Pair payBT K_oo)))
                      teFull r_pFull
        rhs_ifLf = pairOfConst_eval K_ifLfV
                     (Fan (Fan (Lift (KT K_a2))
                               (Fan (Lift (KT K_te)) (Lift Snd) Pair) Pair)
                          (Fan (Lift (KT K_a2))
                               (Fan (Lift (KT K_pair))
                                    (Fan (Lift (Comp Snd Snd)) (Lift (KT K_oo))
                                         Pair) Pair) Pair)
                          Pair)
                     a bb
                     (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_te payT))
                                (ap2 Pair K_a2
                                  (ap2 Pair K_pair (ap2 Pair payBT K_oo))))
                     rhs_inner
        rhsBuild = pairOfConst_eval K_a2V
                     (Fan (Lift (KT K_ifLf))
                          (Fan (Fan (Lift (KT K_a2))
                                    (Fan (Lift (KT K_te)) (Lift Snd) Pair)
                                    Pair)
                               (Fan (Lift (KT K_a2))
                                    (Fan (Lift (KT K_pair))
                                         (Fan (Lift (Comp Snd Snd))
                                              (Lift (KT K_oo))
                                              Pair) Pair) Pair)
                               Pair) Pair)
                     a bb
                     (ap2 Pair K_ifLf
                       (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_te payT))
                                  (ap2 Pair K_a2
                                    (ap2 Pair K_pair (ap2 Pair payBT K_oo)))))
                     rhs_ifLf
    in pairOfFan_eval
         (Fan (Lift (KT K_a2))
              (Fan (Lift (KT K_ifLf))
                   (Fan (Fan (Lift (KT K_a2))
                             (Fan (Lift (KT K_te)) (Lift Snd) Pair) Pair)
                        (Fan (Lift (KT K_a2))
                             (Fan (Lift (KT K_pair))
                                  (Fan (Lift (Comp Fst Snd)) (Lift (KT K_oo))
                                       Pair) Pair) Pair)
                        Pair) Pair) Pair)
         (Fan (Lift (KT K_a2))
              (Fan (Lift (KT K_ifLf))
                   (Fan (Fan (Lift (KT K_a2))
                             (Fan (Lift (KT K_te)) (Lift Snd) Pair) Pair)
                        (Fan (Lift (KT K_a2))
                             (Fan (Lift (KT K_pair))
                                  (Fan (Lift (Comp Snd Snd)) (Lift (KT K_oo))
                                       Pair) Pair) Pair)
                        Pair) Pair) Pair)
         a bb
         (ap2 Pair K_a2 (ap2 Pair K_ifLf
            (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_te payT))
                       (ap2 Pair K_a2
                         (ap2 Pair K_pair (ap2 Pair payAT K_oo))))))
         (ap2 Pair K_a2 (ap2 Pair K_ifLf
            (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_te payT))
                       (ap2 Pair K_a2
                         (ap2 Pair K_pair (ap2 Pair payBT K_oo))))))
         lhsBuild rhsBuild
