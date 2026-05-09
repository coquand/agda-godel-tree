{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm.Parts.AxComp2
--
-- Self-contained dispatch material for
--   axComp2 : Deriv (ap1 (Comp2 h f g) t  =  ap2 h (ap1 f t) (ap1 g t)) .
--
-- Contents: encAxComp2, outAxComp2, body_axComp2, body_axComp2_eval.

module BRA2.Thm.Parts.AxComp2 where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.DerivThreshold
open import BRA2.Thm.Tag using (tagAxComp2)
open import BRA2.Thm.TagCodes
open import BRA2.Thm.EvalHelpers

------------------------------------------------------------------------
-- Encoded proof-tree input and intended Tree output.

encAxComp2 : Fun2 -> Fun1 -> Fun1 -> Term -> Tree
encAxComp2 h f g t = nd (natCode tagAxComp2)
                        (nd (codeF2 h)
                            (nd (codeF1 f)
                                (nd (codeF1 g) (code t))))

outAxComp2 : Fun2 -> Fun1 -> Fun1 -> Term -> Tree
outAxComp2 h f g t =
  codeFormula (atomic (eqn (ap1 (Comp2 h f g) t)
                           (ap2 h (ap1 f t) (ap1 g t))))

------------------------------------------------------------------------
-- body_axComp2.
--
-- axComp2 h f g t : LHS = ap1 (Comp2 h f g) t , RHS = ap2 h (ap1 f t) (ap1 g t).
--   payT depth 4: Pair ch (Pair cf (Pair cg ct)).

body_axComp2 : Fun2
body_axComp2 =
  Fan
    -- LHS-build: Pair K_a1 (Pair (Pair K_comp2Tag (Pair ch (Pair cf cg))) ct)
    (Fan (Lift (KT (reify tagAp1)))
         (Fan (Fan (Lift (KT tagCode_comp2Func))
                   (Fan (Lift (Comp Fst Snd))
                        (Fan (Lift (Comp Fst (Comp Snd Snd)))
                             (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                             Pair)
                        Pair)
                   Pair)
              (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
              Pair)
         Pair)
    -- RHS-build: Pair K_a2 (Pair ch (Pair (Pair K_a1 (Pair cf ct)) (Pair K_a1 (Pair cg ct))))
    (Fan (Lift (KT (reify tagAp2)))
         (Fan (Lift (Comp Fst Snd))
              (Fan (Fan (Lift (KT (reify tagAp1)))
                        (Fan (Lift (Comp Fst (Comp Snd Snd)))
                             (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                             Pair)
                        Pair)
                   (Fan (Lift (KT (reify tagAp1)))
                        (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                             (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                             Pair)
                        Pair)
                   Pair)
              Pair)
         Pair)
    Pair

------------------------------------------------------------------------
-- body_axComp2_eval.

abstract

  body_axComp2_eval : (h' : Fun2) (f g : Fun1) (t bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axComp2
            (ap2 Pair tagCode_axComp2
              (reify (nd (codeF2 h') (nd (codeF1 f) (nd (codeF1 g) (code t)))))) bb)
      (reify (outAxComp2 h' f g t))))
  body_axComp2_eval h' f g t bb =
    let ch    = reify (codeF2 h')
        cf    = reify (codeF1 f)
        cg    = reify (codeF1 g)
        ct    = reify (code t)
        payT  = ap2 Pair ch (ap2 Pair cf (ap2 Pair cg ct))
        a     = ap2 Pair tagCode_axComp2 payT
        K_a1V = tagAp1
        K_a1  = reify K_a1V
        K_a1V_isValue = tagAp1_isValue
        K_a2V = tagAp2
        K_a2  = reify K_a2V
        K_a2V_isValue = tagAp2_isValue
        K_c2V = leftT (codeF1 (Comp2 IfLf I I))
        K_c2  = reify K_c2V
        K_c2V_isValue = leftT_isValue _ (codeF1_isValue (Comp2 IfLf I I))
        ext_ch = liftCompFstSnd_evalPair tagCode_axComp2 ch (ap2 Pair cf (ap2 Pair cg ct)) bb
        ext_cf = liftFstSndSnd_evalPair3 tagCode_axComp2 ch cf (ap2 Pair cg ct) bb
        ext_cg = liftFstSndSndSnd_evalPair4 tagCode_axComp2 ch cf cg ct bb
        ext_ct = liftSndSndSndSnd_evalPair4 tagCode_axComp2 ch cf cg ct bb
        -- LHS = Pair K_a1 (Pair (Pair K_c2 (Pair ch (Pair cf cg))) ct)
        cfcg = pairOfFan_eval
                 (Lift (Comp Fst (Comp Snd Snd)))
                 (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                 a bb cf cg ext_cf ext_cg
        chCfcg = pairOfFan_eval
                   (Lift (Comp Fst Snd))
                   (Fan (Lift (Comp Fst (Comp Snd Snd)))
                        (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) Pair)
                   a bb ch (ap2 Pair cf cg) ext_ch cfcg
        kc2 = pairOfConst_eval K_c2V K_c2V_isValue
                (Fan (Lift (Comp Fst Snd))
                     (Fan (Lift (Comp Fst (Comp Snd Snd)))
                          (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) Pair) Pair)
                a bb (ap2 Pair ch (ap2 Pair cf cg)) chCfcg
        midLHS = pairOfFan_eval
                   (Fan (Lift (KT K_c2))
                        (Fan (Lift (Comp Fst Snd))
                             (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                  (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                  Pair) Pair) Pair)
                   (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                   a bb (ap2 Pair K_c2 (ap2 Pair ch (ap2 Pair cf cg))) ct
                   kc2 ext_ct
        lhsBuild = pairOfConst_eval K_a1V K_a1V_isValue
                     (Fan (Fan (Lift (KT K_c2))
                               (Fan (Lift (Comp Fst Snd))
                                    (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                         (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                         Pair) Pair) Pair)
                          (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                     a bb
                     (ap2 Pair (ap2 Pair K_c2 (ap2 Pair ch (ap2 Pair cf cg))) ct)
                     midLHS
        -- RHS = Pair K_a2 (Pair ch (Pair (Pair K_a1 (Pair cf ct)) (Pair K_a1 (Pair cg ct))))
        cfct = pairOfFan_eval
                 (Lift (Comp Fst (Comp Snd Snd)))
                 (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                 a bb cf ct ext_cf ext_ct
        cgct = pairOfFan_eval
                 (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                 (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                 a bb cg ct ext_cg ext_ct
        ka1Cfct = pairOfConst_eval K_a1V K_a1V_isValue
                    (Fan (Lift (Comp Fst (Comp Snd Snd)))
                         (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                    a bb (ap2 Pair cf ct) cfct
        ka1Cgct = pairOfConst_eval K_a1V K_a1V_isValue
                    (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                         (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                    a bb (ap2 Pair cg ct) cgct
        innerRHS = pairOfFan_eval
                     (Fan (Lift (KT K_a1))
                          (Fan (Lift (Comp Fst (Comp Snd Snd)))
                               (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                          Pair)
                     (Fan (Lift (KT K_a1))
                          (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                               (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                          Pair)
                     a bb
                     (ap2 Pair K_a1 (ap2 Pair cf ct))
                     (ap2 Pair K_a1 (ap2 Pair cg ct))
                     ka1Cfct ka1Cgct
        midRHS = pairOfFan_eval
                   (Lift (Comp Fst Snd))
                   (Fan
                     (Fan (Lift (KT K_a1))
                          (Fan (Lift (Comp Fst (Comp Snd Snd)))
                               (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                          Pair)
                     (Fan (Lift (KT K_a1))
                          (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                               (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                          Pair)
                     Pair)
                   a bb ch
                   (ap2 Pair (ap2 Pair K_a1 (ap2 Pair cf ct))
                              (ap2 Pair K_a1 (ap2 Pair cg ct)))
                   ext_ch innerRHS
        rhsBuild = pairOfConst_eval K_a2V K_a2V_isValue
                     (Fan (Lift (Comp Fst Snd))
                          (Fan
                            (Fan (Lift (KT K_a1))
                                 (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                      (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                                 Pair)
                            (Fan (Lift (KT K_a1))
                                 (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                      (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                                 Pair)
                            Pair)
                          Pair)
                     a bb
                     (ap2 Pair ch (ap2 Pair (ap2 Pair K_a1 (ap2 Pair cf ct))
                                              (ap2 Pair K_a1 (ap2 Pair cg ct))))
                     midRHS
    in pairOfFan_eval
         (Fan (Lift (KT K_a1))
              (Fan (Fan (Lift (KT K_c2))
                        (Fan (Lift (Comp Fst Snd))
                             (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                  (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                  Pair) Pair) Pair)
                   (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair) Pair)
         (Fan (Lift (KT K_a2))
              (Fan (Lift (Comp Fst Snd))
                   (Fan
                     (Fan (Lift (KT K_a1))
                          (Fan (Lift (Comp Fst (Comp Snd Snd)))
                               (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                          Pair)
                     (Fan (Lift (KT K_a1))
                          (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                               (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                          Pair)
                     Pair)
                   Pair)
              Pair)
         a bb
         (ap2 Pair K_a1 (ap2 Pair (ap2 Pair K_c2 (ap2 Pair ch (ap2 Pair cf cg))) ct))
         (ap2 Pair K_a2 (ap2 Pair ch (ap2 Pair (ap2 Pair K_a1 (ap2 Pair cf ct))
                                                (ap2 Pair K_a1 (ap2 Pair cg ct)))))
         lhsBuild rhsBuild
