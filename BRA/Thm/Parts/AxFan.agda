{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.Parts.AxFan
--
-- Self-contained dispatch material for
--   axFan : Deriv (ap2 (Fan h1 h2 h) a b = ap2 h (ap2 h1 a b) (ap2 h2 a b)) .
--
-- Contents: encAxFan, outAxFan, body_axFan, body_axFan_eval.

module BRA.Thm.Parts.AxFan where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Thm.Tag using (tagAxFan)
open import BRA.Thm.TagCodes
open import BRA.Thm.EvalHelpers

------------------------------------------------------------------------
-- Encoded proof-tree input and intended Tree output.

encAxFan : Fun2 -> Fun2 -> Fun2 -> Term -> Term -> Tree
encAxFan h1 h2 h a b = nd (natCode tagAxFan)
                          (nd (codeF2 h1)
                              (nd (codeF2 h2)
                                  (nd (codeF2 h)
                                      (nd (code a) (code b)))))

outAxFan : Fun2 -> Fun2 -> Fun2 -> Term -> Term -> Tree
outAxFan h1 h2 h a b =
  codeFormula (atomic (eqn (ap2 (Fan h1 h2 h) a b)
                           (ap2 h (ap2 h1 a b) (ap2 h2 a b))))

------------------------------------------------------------------------
-- body_axFan.
--
-- axFan h1 h2 h a' b' : LHS = ap2 (Fan h1 h2 h) a' b' ,
--                       RHS = ap2 h (ap2 h1 a' b') (ap2 h2 a' b').
--   payT depth 5: Pair ch1 (Pair ch2 (Pair ch (Pair payAT payBT))).

body_axFan : Fun2
body_axFan =
  Fan
    -- LHS-build: Pair K_a2 (Pair (Pair K_fanTag (Pair ch1 (Pair ch2 ch))) (Pair payAT payBT))
    (Fan (Lift (KT (reify tagAp2)))
         (Fan (Fan (Lift (KT tagCode_fanFunc))
                   (Fan (Lift (Comp Fst Snd))
                        (Fan (Lift (Comp Fst (Comp Snd Snd)))
                             (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                             Pair)
                        Pair)
                   Pair)
              (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                   (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                   Pair)
              Pair)
         Pair)
    -- RHS-build: Pair K_a2 (Pair ch (Pair LHSh1 LHSh2)) where
    --   LHSh1 = Pair K_a2 (Pair ch1 (Pair payAT payBT))
    --   LHSh2 = Pair K_a2 (Pair ch2 (Pair payAT payBT))
    (Fan (Lift (KT (reify tagAp2)))
         (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
              (Fan
                -- LHSh1 build
                (Fan (Lift (KT (reify tagAp2)))
                     (Fan (Lift (Comp Fst Snd))
                          (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                               (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                               Pair)
                          Pair)
                     Pair)
                -- LHSh2 build
                (Fan (Lift (KT (reify tagAp2)))
                     (Fan (Lift (Comp Fst (Comp Snd Snd)))
                          (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                               (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                               Pair)
                          Pair)
                     Pair)
                Pair)
              Pair)
         Pair)
    Pair

------------------------------------------------------------------------
-- body_axFan_eval.

abstract

  body_axFan_eval : (h1' h2' h' : Fun2) (a' b' bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axFan
            (ap2 Pair tagCode_axFan
              (reify (nd (codeF2 h1')
                          (nd (codeF2 h2')
                              (nd (codeF2 h') (nd (code a') (code b'))))))) bb)
      (reify (outAxFan h1' h2' h' a' b'))))
  body_axFan_eval h1' h2' h' a' b' bb =
    let ch1   = reify (codeF2 h1')
        ch2   = reify (codeF2 h2')
        ch    = reify (codeF2 h')
        payAT = reify (code a')
        payBT = reify (code b')
        payT  = ap2 Pair ch1 (ap2 Pair ch2 (ap2 Pair ch (ap2 Pair payAT payBT)))
        a     = ap2 Pair tagCode_axFan payT
        K_a2V = tagAp2
        K_a2  = reify K_a2V
        K_fV  = leftT (codeF2 (Fan IfLf IfLf IfLf))
        K_f   = reify K_fV
        ext_ch1   = liftCompFstSnd_evalPair tagCode_axFan ch1
                       (ap2 Pair ch2 (ap2 Pair ch (ap2 Pair payAT payBT))) bb
        ext_ch2   = liftFstSndSnd_evalPair3 tagCode_axFan ch1 ch2
                       (ap2 Pair ch (ap2 Pair payAT payBT)) bb
        ext_ch    = liftFstSndSndSnd_evalPair4 tagCode_axFan ch1 ch2 ch
                       (ap2 Pair payAT payBT) bb
        ext_payAT = liftFstSndSndSndSnd_evalPair5 tagCode_axFan ch1 ch2 ch payAT payBT bb
        ext_payBT = liftSndSndSndSndSnd_evalPair5 tagCode_axFan ch1 ch2 ch payAT payBT bb
        -- Re-usable: payATBT = Pair payAT payBT.
        payATBT = pairOfFan_eval
                    (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                    (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                    a bb payAT payBT ext_payAT ext_payBT
        -- LHS: Pair K_a2 (Pair (Pair K_f (Pair ch1 (Pair ch2 ch))) (Pair payAT payBT))
        ch2ch = pairOfFan_eval
                  (Lift (Comp Fst (Comp Snd Snd)))
                  (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                  a bb ch2 ch ext_ch2 ext_ch
        ch1ch2ch = pairOfFan_eval
                     (Lift (Comp Fst Snd))
                     (Fan (Lift (Comp Fst (Comp Snd Snd)))
                          (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) Pair)
                     a bb ch1 (ap2 Pair ch2 ch) ext_ch1 ch2ch
        kfChain = pairOfConst_eval K_fV
                    (Fan (Lift (Comp Fst Snd))
                         (Fan (Lift (Comp Fst (Comp Snd Snd)))
                              (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) Pair)
                         Pair)
                    a bb (ap2 Pair ch1 (ap2 Pair ch2 ch)) ch1ch2ch
        midLHS = pairOfFan_eval
                   (Fan (Lift (KT K_f))
                        (Fan (Lift (Comp Fst Snd))
                             (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                  (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                  Pair) Pair) Pair)
                   (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                        (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                        Pair)
                   a bb
                   (ap2 Pair K_f (ap2 Pair ch1 (ap2 Pair ch2 ch)))
                   (ap2 Pair payAT payBT)
                   kfChain payATBT
        lhsBuild = pairOfConst_eval K_a2V
                     (Fan (Fan (Lift (KT K_f))
                               (Fan (Lift (Comp Fst Snd))
                                    (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                         (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                         Pair) Pair) Pair)
                          (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                               (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                               Pair)
                          Pair)
                     a bb
                     (ap2 Pair (ap2 Pair K_f (ap2 Pair ch1 (ap2 Pair ch2 ch)))
                                (ap2 Pair payAT payBT))
                     midLHS
        -- RHS: Pair K_a2 (Pair ch (Pair LHSh1 LHSh2)) where
        --   LHSh1 = Pair K_a2 (Pair ch1 (Pair payAT payBT))
        --   LHSh2 = Pair K_a2 (Pair ch2 (Pair payAT payBT))
        ch1pATpBT = pairOfFan_eval
                      (Lift (Comp Fst Snd))
                      (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                           (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                           Pair)
                      a bb ch1 (ap2 Pair payAT payBT) ext_ch1 payATBT
        ch2pATpBT = pairOfFan_eval
                      (Lift (Comp Fst (Comp Snd Snd)))
                      (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                           (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                           Pair)
                      a bb ch2 (ap2 Pair payAT payBT) ext_ch2 payATBT
        ka2ch1pATpBT = pairOfConst_eval K_a2V
                         (Fan (Lift (Comp Fst Snd))
                              (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                   (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                   Pair) Pair)
                         a bb (ap2 Pair ch1 (ap2 Pair payAT payBT)) ch1pATpBT
        ka2ch2pATpBT = pairOfConst_eval K_a2V
                         (Fan (Lift (Comp Fst (Comp Snd Snd)))
                              (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                   (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                   Pair) Pair)
                         a bb (ap2 Pair ch2 (ap2 Pair payAT payBT)) ch2pATpBT
        twoLHSs = pairOfFan_eval
                    (Fan (Lift (KT K_a2))
                         (Fan (Lift (Comp Fst Snd))
                              (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                   (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                   Pair) Pair) Pair)
                    (Fan (Lift (KT K_a2))
                         (Fan (Lift (Comp Fst (Comp Snd Snd)))
                              (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                   (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                   Pair) Pair) Pair)
                    a bb
                    (ap2 Pair K_a2 (ap2 Pair ch1 (ap2 Pair payAT payBT)))
                    (ap2 Pair K_a2 (ap2 Pair ch2 (ap2 Pair payAT payBT)))
                    ka2ch1pATpBT ka2ch2pATpBT
        chLHSs = pairOfFan_eval
                   (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                   (Fan (Fan (Lift (KT K_a2))
                             (Fan (Lift (Comp Fst Snd))
                                  (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                       (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                       Pair) Pair) Pair)
                        (Fan (Lift (KT K_a2))
                             (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                  (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                       (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                       Pair) Pair) Pair) Pair)
                   a bb ch
                   (ap2 Pair (ap2 Pair K_a2 (ap2 Pair ch1 (ap2 Pair payAT payBT)))
                              (ap2 Pair K_a2 (ap2 Pair ch2 (ap2 Pair payAT payBT))))
                   ext_ch twoLHSs
        rhsBuild = pairOfConst_eval K_a2V
                     (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                          (Fan (Fan (Lift (KT K_a2))
                                    (Fan (Lift (Comp Fst Snd))
                                         (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                              (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                              Pair) Pair) Pair)
                               (Fan (Lift (KT K_a2))
                                    (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                         (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                              (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                              Pair) Pair) Pair) Pair)
                          Pair)
                     a bb
                     (ap2 Pair ch
                       (ap2 Pair (ap2 Pair K_a2 (ap2 Pair ch1 (ap2 Pair payAT payBT)))
                                  (ap2 Pair K_a2 (ap2 Pair ch2 (ap2 Pair payAT payBT)))))
                     chLHSs
    in pairOfFan_eval
         (Fan (Lift (KT K_a2))
              (Fan (Fan (Lift (KT K_f))
                        (Fan (Lift (Comp Fst Snd))
                             (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                  (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                  Pair) Pair) Pair)
                   (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                        (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                        Pair)
                   Pair) Pair)
         (Fan (Lift (KT K_a2))
              (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                   (Fan (Fan (Lift (KT K_a2))
                             (Fan (Lift (Comp Fst Snd))
                                  (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                       (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                       Pair) Pair) Pair)
                        (Fan (Lift (KT K_a2))
                             (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                  (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                       (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                       Pair) Pair) Pair) Pair) Pair) Pair)
         a bb
         (ap2 Pair K_a2 (ap2 Pair (ap2 Pair K_f (ap2 Pair ch1 (ap2 Pair ch2 ch)))
                                    (ap2 Pair payAT payBT)))
         (ap2 Pair K_a2 (ap2 Pair ch
                           (ap2 Pair (ap2 Pair K_a2 (ap2 Pair ch1 (ap2 Pair payAT payBT)))
                                      (ap2 Pair K_a2 (ap2 Pair ch2 (ap2 Pair payAT payBT))))))
         lhsBuild rhsBuild
