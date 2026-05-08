{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm.Parts.AxLift
--
-- Self-contained dispatch material for
--   axLift : Deriv (ap2 (Lift f) a b = ap1 f a) .
--
-- Contents: encAxLift, outAxLift, body_axLift, body_axLift_eval.

module BRA2.Thm.Parts.AxLift where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Deriv
open import BRA2.Thm.Tag using (tagAxLift)
open import BRA2.Thm.TagCodes
open import BRA2.Thm.EvalHelpers

------------------------------------------------------------------------
-- Encoded proof-tree input and intended Tree output.

encAxLift : Fun1 -> Term -> Term -> Tree
encAxLift f a b = nd (natCode tagAxLift)
                     (nd (codeF1 f)
                         (nd (code a) (code b)))

outAxLift : Fun1 -> Term -> Term -> Tree
outAxLift f a b = codeFormula (atomic (eqn (ap2 (Lift f) a b) (ap1 f a)))

------------------------------------------------------------------------
-- body_axLift.
--
-- axLift f a' b' : LHS = ap2 (Lift f) a' b' , RHS = ap1 f a'.
--   payT depth 3: Pair cf (Pair payAT payBT).

body_axLift : Fun2
body_axLift =
  Fan
    -- LHS-build: Pair K_a2 (Pair (Pair K_liftTag cf) (Pair payAT payBT))
    (Fan (Lift (KT (reify tagAp2)))
         (Fan (Fan (Lift (KT tagCode_liftFunc))
                   (Lift (Comp Fst Snd))
                   Pair)
              (Fan (Lift (Comp Fst (Comp Snd Snd)))
                   (Lift (Comp Snd (Comp Snd Snd)))
                   Pair)
              Pair)
         Pair)
    -- RHS-build: Pair K_a1 (Pair cf payAT)
    (Fan (Lift (KT (reify tagAp1)))
         (Fan (Lift (Comp Fst Snd))
              (Lift (Comp Fst (Comp Snd Snd)))
              Pair)
         Pair)
    Pair

------------------------------------------------------------------------
-- body_axLift_eval.

abstract

  body_axLift_eval : (f : Fun1) (a' b' bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axLift
            (ap2 Pair tagCode_axLift
                       (reify (nd (codeF1 f) (nd (code a') (code b'))))) bb)
      (reify (outAxLift f a' b'))))
  body_axLift_eval f a' b' bb =
    let cf    = reify (codeF1 f)
        payAT = reify (code a')
        payBT = reify (code b')
        payT  = ap2 Pair cf (ap2 Pair payAT payBT)
        a     = ap2 Pair tagCode_axLift payT
        K1V   = tagAp2
        K1V_isValue = tagAp2_isValue
        K2V   = leftT (codeF2 (Lift I))
        K2V_isValue = leftT_isValue _ (codeF2_isValue (Lift I))
        K3V   = tagAp1
        K3V_isValue = tagAp1_isValue
        K1    = reify K1V
        K2    = reify K2V
        K3    = reify K3V
        ext_cf    = liftCompFstSnd_evalPair tagCode_axLift cf (ap2 Pair payAT payBT) bb
        ext_payAT = liftFstSndSnd_evalPair3 tagCode_axLift cf payAT payBT bb
        ext_payBT = liftSndSndSnd_evalPair3 tagCode_axLift cf payAT payBT bb
        -- LHS: Pair K1 (Pair (Pair K2 cf) (Pair payAT payBT))
        kLiftCf = pairOfConst_eval K2V K2V_isValue (Lift (Comp Fst Snd)) a bb cf ext_cf
        payATBT = pairOfFan_eval
                    (Lift (Comp Fst (Comp Snd Snd)))
                    (Lift (Comp Snd (Comp Snd Snd))) a bb
                    payAT payBT ext_payAT ext_payBT
        midLHS = pairOfFan_eval
                   (Fan (Lift (KT K2)) (Lift (Comp Fst Snd)) Pair)
                   (Fan (Lift (Comp Fst (Comp Snd Snd)))
                        (Lift (Comp Snd (Comp Snd Snd))) Pair)
                   a bb
                   (ap2 Pair K2 cf) (ap2 Pair payAT payBT)
                   kLiftCf payATBT
        lhsBuild = pairOfConst_eval K1V K1V_isValue
                     (Fan (Fan (Lift (KT K2)) (Lift (Comp Fst Snd)) Pair)
                          (Fan (Lift (Comp Fst (Comp Snd Snd)))
                               (Lift (Comp Snd (Comp Snd Snd))) Pair) Pair)
                     a bb
                     (ap2 Pair (ap2 Pair K2 cf) (ap2 Pair payAT payBT))
                     midLHS
        -- RHS: Pair K3 (Pair cf payAT)
        midRHS = pairOfFan_eval
                   (Lift (Comp Fst Snd))
                   (Lift (Comp Fst (Comp Snd Snd)))
                   a bb cf payAT ext_cf ext_payAT
        rhsBuild = pairOfConst_eval K3V K3V_isValue
                     (Fan (Lift (Comp Fst Snd))
                          (Lift (Comp Fst (Comp Snd Snd))) Pair)
                     a bb (ap2 Pair cf payAT) midRHS
    in pairOfFan_eval
         (Fan (Lift (KT K1))
              (Fan (Fan (Lift (KT K2)) (Lift (Comp Fst Snd)) Pair)
                   (Fan (Lift (Comp Fst (Comp Snd Snd)))
                        (Lift (Comp Snd (Comp Snd Snd))) Pair) Pair)
              Pair)
         (Fan (Lift (KT K3))
              (Fan (Lift (Comp Fst Snd))
                   (Lift (Comp Fst (Comp Snd Snd))) Pair)
              Pair)
         a bb
         (ap2 Pair K1 (ap2 Pair (ap2 Pair K2 cf) (ap2 Pair payAT payBT)))
         (ap2 Pair K3 (ap2 Pair cf payAT))
         lhsBuild rhsBuild
