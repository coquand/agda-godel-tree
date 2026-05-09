{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm.Parts.AxPost
--
-- Self-contained dispatch material for
--   axPost : Deriv (ap2 (Post f h) a b = ap1 f (ap2 h a b)) .
--
-- Contents: encAxPost, outAxPost, body_axPost, body_axPost_eval.

module BRA2.Thm.Parts.AxPost where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.DerivThreshold
open import BRA2.Thm.Tag using (tagAxPost)
open import BRA2.Thm.TagCodes
open import BRA2.Thm.EvalHelpers

------------------------------------------------------------------------
-- Encoded proof-tree input and intended Tree output.

encAxPost : Fun1 -> Fun2 -> Term -> Term -> Tree
encAxPost f h a b = nd (natCode tagAxPost)
                       (nd (codeF1 f)
                           (nd (codeF2 h)
                               (nd (code a) (code b))))

outAxPost : Fun1 -> Fun2 -> Term -> Term -> Tree
outAxPost f h a b = codeFormula (atomic (eqn (ap2 (Post f h) a b)
                                             (ap1 f (ap2 h a b))))

------------------------------------------------------------------------
-- body_axPost.
--
-- axPost f h a' b' : LHS = ap2 (Post f h) a' b' , RHS = ap1 f (ap2 h a' b').
--   payT depth 4: Pair cf (Pair ch (Pair payAT payBT)).

body_axPost : Fun2
body_axPost =
  Fan
    -- LHS-build: Pair K_a2 (Pair (Pair K_postTag (Pair cf ch)) (Pair payAT payBT))
    (Fan (Lift (KT (reify tagAp2)))
         (Fan (Fan (Lift (KT tagCode_postFunc))
                   (Fan (Lift (Comp Fst Snd))
                        (Lift (Comp Fst (Comp Snd Snd)))
                        Pair)
                   Pair)
              (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                   (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                   Pair)
              Pair)
         Pair)
    -- RHS-build: Pair K_a1 (Pair cf (Pair K_a2 (Pair ch (Pair payAT payBT))))
    (Fan (Lift (KT (reify tagAp1)))
         (Fan (Lift (Comp Fst Snd))
              (Fan (Lift (KT (reify tagAp2)))
                   (Fan (Lift (Comp Fst (Comp Snd Snd)))
                        (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                             (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                             Pair)
                        Pair)
                   Pair)
              Pair)
         Pair)
    Pair

------------------------------------------------------------------------
-- body_axPost_eval.

abstract

  body_axPost_eval : (f : Fun1) (h' : Fun2) (a' b' bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axPost
            (ap2 Pair tagCode_axPost
              (reify (nd (codeF1 f) (nd (codeF2 h') (nd (code a') (code b')))))) bb)
      (reify (outAxPost f h' a' b'))))
  body_axPost_eval f h' a' b' bb =
    let cf    = reify (codeF1 f)
        ch    = reify (codeF2 h')
        payAT = reify (code a')
        payBT = reify (code b')
        payT  = ap2 Pair cf (ap2 Pair ch (ap2 Pair payAT payBT))
        a     = ap2 Pair tagCode_axPost payT
        K_a1V = tagAp1
        K_a1V_isValue = tagAp1_isValue
        K_a1  = reify K_a1V
        K_a2V = tagAp2
        K_a2V_isValue = tagAp2_isValue
        K_a2  = reify K_a2V
        K_pV  = leftT (codeF2 (Post I IfLf))
        K_pV_isValue = leftT_isValue _ (codeF2_isValue (Post I IfLf))
        K_p   = reify K_pV
        ext_cf    = liftCompFstSnd_evalPair tagCode_axPost cf
                       (ap2 Pair ch (ap2 Pair payAT payBT)) bb
        ext_ch    = liftFstSndSnd_evalPair3 tagCode_axPost cf ch
                       (ap2 Pair payAT payBT) bb
        ext_payAT = liftFstSndSndSnd_evalPair4 tagCode_axPost cf ch payAT payBT bb
        ext_payBT = liftSndSndSndSnd_evalPair4 tagCode_axPost cf ch payAT payBT bb
        -- LHS: Pair K_a2 (Pair (Pair K_p (Pair cf ch)) (Pair payAT payBT))
        cfch = pairOfFan_eval
                 (Lift (Comp Fst Snd))
                 (Lift (Comp Fst (Comp Snd Snd))) a bb cf ch ext_cf ext_ch
        kpCfch = pairOfConst_eval K_pV K_pV_isValue
                   (Fan (Lift (Comp Fst Snd))
                        (Lift (Comp Fst (Comp Snd Snd))) Pair)
                   a bb (ap2 Pair cf ch) cfch
        pATpBT = pairOfFan_eval
                   (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                   (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                   a bb payAT payBT ext_payAT ext_payBT
        midLHS = pairOfFan_eval
                   (Fan (Lift (KT K_p))
                        (Fan (Lift (Comp Fst Snd))
                             (Lift (Comp Fst (Comp Snd Snd))) Pair)
                        Pair)
                   (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                        (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                        Pair)
                   a bb
                   (ap2 Pair K_p (ap2 Pair cf ch))
                   (ap2 Pair payAT payBT)
                   kpCfch pATpBT
        lhsBuild = pairOfConst_eval K_a2V K_a2V_isValue
                     (Fan (Fan (Lift (KT K_p))
                               (Fan (Lift (Comp Fst Snd))
                                    (Lift (Comp Fst (Comp Snd Snd))) Pair)
                               Pair)
                          (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                               (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                               Pair)
                          Pair)
                     a bb
                     (ap2 Pair (ap2 Pair K_p (ap2 Pair cf ch))
                                (ap2 Pair payAT payBT))
                     midLHS
        -- RHS: Pair K_a1 (Pair cf (Pair K_a2 (Pair ch (Pair payAT payBT))))
        chPATpBT = pairOfFan_eval
                     (Lift (Comp Fst (Comp Snd Snd)))
                     (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                          (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                          Pair)
                     a bb ch (ap2 Pair payAT payBT) ext_ch pATpBT
        ka2chPATpBT = pairOfConst_eval K_a2V K_a2V_isValue
                        (Fan (Lift (Comp Fst (Comp Snd Snd)))
                             (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                  (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                  Pair) Pair)
                        a bb (ap2 Pair ch (ap2 Pair payAT payBT)) chPATpBT
        cfKa2 = pairOfFan_eval
                  (Lift (Comp Fst Snd))
                  (Fan (Lift (KT K_a2))
                       (Fan (Lift (Comp Fst (Comp Snd Snd)))
                            (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                 (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                 Pair) Pair) Pair)
                  a bb cf
                  (ap2 Pair K_a2 (ap2 Pair ch (ap2 Pair payAT payBT)))
                  ext_cf ka2chPATpBT
        rhsBuild = pairOfConst_eval K_a1V K_a1V_isValue
                     (Fan (Lift (Comp Fst Snd))
                          (Fan (Lift (KT K_a2))
                               (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                    (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                         (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                         Pair) Pair) Pair)
                          Pair)
                     a bb
                     (ap2 Pair cf (ap2 Pair K_a2
                                      (ap2 Pair ch (ap2 Pair payAT payBT))))
                     cfKa2
    in pairOfFan_eval
         (Fan (Lift (KT K_a2))
              (Fan (Fan (Lift (KT K_p))
                        (Fan (Lift (Comp Fst Snd))
                             (Lift (Comp Fst (Comp Snd Snd))) Pair)
                        Pair)
                   (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                        (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                        Pair)
                   Pair) Pair)
         (Fan (Lift (KT K_a1))
              (Fan (Lift (Comp Fst Snd))
                   (Fan (Lift (KT K_a2))
                        (Fan (Lift (Comp Fst (Comp Snd Snd)))
                             (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                  (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                  Pair) Pair) Pair) Pair) Pair)
         a bb
         (ap2 Pair K_a2 (ap2 Pair (ap2 Pair K_p (ap2 Pair cf ch))
                                    (ap2 Pair payAT payBT)))
         (ap2 Pair K_a1 (ap2 Pair cf
                           (ap2 Pair K_a2
                              (ap2 Pair ch (ap2 Pair payAT payBT)))))
         lhsBuild rhsBuild
