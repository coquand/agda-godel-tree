{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm.Parts.AxS
--
-- Self-contained dispatch material for Guard's Ax 12 (S):
--   axS : Deriv ((P imp (Q imp R)) imp ((P imp Q) imp (P imp R))) .
--
-- Contents: encAxS, outAxS, body_axS, body_axS_eval.

module BRA2.Thm.Parts.AxS where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.DerivThreshold
open import BRA2.Thm.Tag using (tagAxS)
open import BRA2.Thm.TagCodes
open import BRA2.Thm.EvalHelpers

------------------------------------------------------------------------
-- Encoded proof-tree input and intended Tree output.

encAxS : Formula -> Formula -> Formula -> Tree
encAxS P Q R = nd (natCode tagAxS)
                  (nd (codeFormula P)
                      (nd (codeFormula Q) (codeFormula R)))

outAxS : Formula -> Formula -> Formula -> Tree
outAxS P Q R = codeFormula ((P imp (Q imp R)) imp ((P imp Q) imp (P imp R)))

------------------------------------------------------------------------
-- body_axS.
--
-- axS P Q R : conclusion = (P imp (Q imp R)) imp ((P imp Q) imp (P imp R)).
--   payT depth 3: Pair payP (Pair payQ payR).

body_axS : Fun2
body_axS =
  Fan (Lift (KT (reify tagImp)))
      (Fan
          -- A = P imp (Q imp R)
          (Fan (Lift (KT (reify tagImp)))
               (Fan (Lift (Comp Fst Snd))
                    (Fan (Lift (KT (reify tagImp)))
                         (Fan (Lift (Comp Fst (Comp Snd Snd)))
                              (Lift (Comp Snd (Comp Snd Snd)))
                              Pair)
                         Pair)
                    Pair)
               Pair)
          -- B = (P imp Q) imp (P imp R)
          (Fan (Lift (KT (reify tagImp)))
               (Fan (Fan (Lift (KT (reify tagImp)))
                         (Fan (Lift (Comp Fst Snd))
                              (Lift (Comp Fst (Comp Snd Snd)))
                              Pair)
                         Pair)
                    (Fan (Lift (KT (reify tagImp)))
                         (Fan (Lift (Comp Fst Snd))
                              (Lift (Comp Snd (Comp Snd Snd)))
                              Pair)
                         Pair)
                    Pair)
               Pair)
          Pair)
      Pair

------------------------------------------------------------------------
-- body_axS_eval.

abstract

  -- axS P Q R : 3 args; depth-3 payload.
  body_axS_eval : (P Q R : Formula) (bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axS (ap2 Pair tagCode_axS
                       (reify (nd (codeFormula P) (nd (codeFormula Q) (codeFormula R))))) bb)
      (reify (outAxS P Q R))))
  body_axS_eval P Q R bb =
    let payP   = reify (codeFormula P)
        payQ   = reify (codeFormula Q)
        payR   = reify (codeFormula R)
        payT   = ap2 Pair payP (ap2 Pair payQ payR)
        a      = ap2 Pair tagCode_axS payT
        K_impV = tagImp
        K_impV_isValue = tagImp_isValue
        K_imp  = reify K_impV
        ext_p  = liftCompFstSnd_evalPair tagCode_axS payP (ap2 Pair payQ payR) bb
        ext_q  = liftFstSndSnd_evalPair3 tagCode_axS payP payQ payR bb
        ext_r  = liftSndSndSnd_evalPair3 tagCode_axS payP payQ payR bb
        -- A = Pair K_imp (Pair payP (Pair K_imp (Pair payQ payR)))
        qr     = pairOfFan_eval (Lift (Comp Fst (Comp Snd Snd)))
                   (Lift (Comp Snd (Comp Snd Snd))) a bb payQ payR ext_q ext_r
        impQR  = pairOfConst_eval K_impV K_impV_isValue
                   (Fan (Lift (Comp Fst (Comp Snd Snd)))
                        (Lift (Comp Snd (Comp Snd Snd))) Pair)
                   a bb (ap2 Pair payQ payR) qr
        pImpQR = pairOfFan_eval (Lift (Comp Fst Snd))
                   (Fan (Lift (KT K_imp))
                        (Fan (Lift (Comp Fst (Comp Snd Snd)))
                             (Lift (Comp Snd (Comp Snd Snd))) Pair) Pair)
                   a bb payP (ap2 Pair K_imp (ap2 Pair payQ payR))
                   ext_p impQR
        bigA   = pairOfConst_eval K_impV K_impV_isValue
                   (Fan (Lift (Comp Fst Snd))
                        (Fan (Lift (KT K_imp))
                             (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                  (Lift (Comp Snd (Comp Snd Snd))) Pair) Pair) Pair)
                   a bb (ap2 Pair payP (ap2 Pair K_imp (ap2 Pair payQ payR))) pImpQR
        -- B = Pair K_imp (Pair (Pair K_imp (Pair payP payQ)) (Pair K_imp (Pair payP payR)))
        pq     = pairOfFan_eval (Lift (Comp Fst Snd))
                   (Lift (Comp Fst (Comp Snd Snd))) a bb payP payQ ext_p ext_q
        impPQ  = pairOfConst_eval K_impV K_impV_isValue
                   (Fan (Lift (Comp Fst Snd))
                        (Lift (Comp Fst (Comp Snd Snd))) Pair)
                   a bb (ap2 Pair payP payQ) pq
        pr     = pairOfFan_eval (Lift (Comp Fst Snd))
                   (Lift (Comp Snd (Comp Snd Snd))) a bb payP payR ext_p ext_r
        impPR  = pairOfConst_eval K_impV K_impV_isValue
                   (Fan (Lift (Comp Fst Snd))
                        (Lift (Comp Snd (Comp Snd Snd))) Pair)
                   a bb (ap2 Pair payP payR) pr
        impPQ_PR = pairOfFan_eval
                     (Fan (Lift (KT K_imp))
                          (Fan (Lift (Comp Fst Snd))
                               (Lift (Comp Fst (Comp Snd Snd))) Pair) Pair)
                     (Fan (Lift (KT K_imp))
                          (Fan (Lift (Comp Fst Snd))
                               (Lift (Comp Snd (Comp Snd Snd))) Pair) Pair)
                     a bb
                     (ap2 Pair K_imp (ap2 Pair payP payQ))
                     (ap2 Pair K_imp (ap2 Pair payP payR))
                     impPQ impPR
        bigB   = pairOfConst_eval K_impV K_impV_isValue
                   (Fan (Fan (Lift (KT K_imp))
                             (Fan (Lift (Comp Fst Snd))
                                  (Lift (Comp Fst (Comp Snd Snd))) Pair) Pair)
                        (Fan (Lift (KT K_imp))
                             (Fan (Lift (Comp Fst Snd))
                                  (Lift (Comp Snd (Comp Snd Snd))) Pair) Pair)
                        Pair)
                   a bb
                   (ap2 Pair (ap2 Pair K_imp (ap2 Pair payP payQ))
                              (ap2 Pair K_imp (ap2 Pair payP payR)))
                   impPQ_PR
        ab     = pairOfFan_eval
                   (Fan (Lift (KT K_imp))
                        (Fan (Lift (Comp Fst Snd))
                             (Fan (Lift (KT K_imp))
                                  (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                       (Lift (Comp Snd (Comp Snd Snd))) Pair) Pair) Pair) Pair)
                   (Fan (Lift (KT K_imp))
                        (Fan (Fan (Lift (KT K_imp))
                                  (Fan (Lift (Comp Fst Snd))
                                       (Lift (Comp Fst (Comp Snd Snd))) Pair) Pair)
                             (Fan (Lift (KT K_imp))
                                  (Fan (Lift (Comp Fst Snd))
                                       (Lift (Comp Snd (Comp Snd Snd))) Pair) Pair)
                             Pair) Pair)
                   a bb
                   (ap2 Pair K_imp (ap2 Pair payP (ap2 Pair K_imp (ap2 Pair payQ payR))))
                   (ap2 Pair K_imp (ap2 Pair (ap2 Pair K_imp (ap2 Pair payP payQ))
                                              (ap2 Pair K_imp (ap2 Pair payP payR))))
                   bigA bigB
    in pairOfConst_eval K_impV K_impV_isValue
         (Fan (Fan (Lift (KT K_imp))
                   (Fan (Lift (Comp Fst Snd))
                        (Fan (Lift (KT K_imp))
                             (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                  (Lift (Comp Snd (Comp Snd Snd))) Pair) Pair) Pair) Pair)
              (Fan (Lift (KT K_imp))
                   (Fan (Fan (Lift (KT K_imp))
                             (Fan (Lift (Comp Fst Snd))
                                  (Lift (Comp Fst (Comp Snd Snd))) Pair) Pair)
                        (Fan (Lift (KT K_imp))
                             (Fan (Lift (Comp Fst Snd))
                                  (Lift (Comp Snd (Comp Snd Snd))) Pair) Pair)
                        Pair) Pair)
              Pair)
         a bb
         (ap2 Pair (ap2 Pair K_imp (ap2 Pair payP (ap2 Pair K_imp (ap2 Pair payQ payR))))
                    (ap2 Pair K_imp (ap2 Pair (ap2 Pair K_imp (ap2 Pair payP payQ))
                                                (ap2 Pair K_imp (ap2 Pair payP payR)))))
         ab
