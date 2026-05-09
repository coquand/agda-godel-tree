{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm.Parts.AxK
--
-- Self-contained dispatch material for the propositional axiom
--   axK : Deriv (P imp (Q imp P))  (P, Q : Formula).
--
-- Contents: encAxK, outAxK, body_axK, body_axK_eval.

module BRA2.Thm.Parts.AxK where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.DerivThreshold
open import BRA2.Thm.Tag using (tagAxK)
open import BRA2.Thm.TagCodes
open import BRA2.Thm.EvalHelpers

------------------------------------------------------------------------
-- Encoded proof-tree input and intended Tree output.

encAxK : Formula -> Formula -> Tree
encAxK P Q = nd (natCode tagAxK) (nd (codeFormula P) (codeFormula Q))

outAxK : Formula -> Formula -> Tree
outAxK P Q = codeFormula (P imp (Q imp P))

------------------------------------------------------------------------
-- body_axK.
--
-- axK P Q : conclusion = P imp (Q imp P).
--   payT depth 2: Pair payP payQ.

body_axK : Fun2
body_axK =
  Fan (Lift (KT (reify tagImp)))
      (Fan (Lift (Comp Fst Snd))
           (Fan (Lift (KT (reify tagImp)))
                (Fan (Lift (Comp Snd Snd))
                     (Lift (Comp Fst Snd))
                     Pair)
                Pair)
           Pair)
      Pair

------------------------------------------------------------------------
-- body_axK_eval.

abstract

  -- axK P Q : 2 args (P, Q : Formula); depth-2 payload.
  body_axK_eval : (P Q : Formula) (bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axK (ap2 Pair tagCode_axK (reify (nd (codeFormula P) (codeFormula Q)))) bb)
      (reify (outAxK P Q))))
  body_axK_eval P Q bb =
    let payP   = reify (codeFormula P)
        payQ   = reify (codeFormula Q)
        payT   = ap2 Pair payP payQ
        a      = ap2 Pair tagCode_axK payT
        K_impV = tagImp
        K_impV_isValue = tagImp_isValue
        K_imp  = reify K_impV
        ext_p  = liftCompFstSnd_evalPair tagCode_axK payP payQ bb
        ext_q  = liftCompSndSnd_evalPair tagCode_axK payP payQ bb
        qP     = pairOfFan_eval (Lift (Comp Snd Snd)) (Lift (Comp Fst Snd))
                   a bb payQ payP ext_q ext_p
        impQP  = pairOfConst_eval K_impV K_impV_isValue
                   (Fan (Lift (Comp Snd Snd)) (Lift (Comp Fst Snd)) Pair)
                   a bb (ap2 Pair payQ payP) qP
        midRHS = pairOfFan_eval (Lift (Comp Fst Snd))
                   (Fan (Lift (KT K_imp))
                        (Fan (Lift (Comp Snd Snd))
                             (Lift (Comp Fst Snd)) Pair) Pair)
                   a bb payP (ap2 Pair K_imp (ap2 Pair payQ payP))
                   ext_p impQP
    in pairOfConst_eval K_impV K_impV_isValue
         (Fan (Lift (Comp Fst Snd))
              (Fan (Lift (KT K_imp))
                   (Fan (Lift (Comp Snd Snd))
                        (Lift (Comp Fst Snd)) Pair) Pair) Pair)
         a bb
         (ap2 Pair payP (ap2 Pair K_imp (ap2 Pair payQ payP)))
         midRHS
