{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm.Parts.AxComp
--
-- Self-contained dispatch material for
--   axComp : Deriv (ap1 (Comp f g) t  =  ap1 f (ap1 g t)) .
--
-- Contents: encAxComp, outAxComp, body_axComp, body_axComp_eval.

module BRA2.Thm.Parts.AxComp where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.DerivThreshold
open import BRA2.Thm.Tag using (tagAxComp)
open import BRA2.Thm.TagCodes
open import BRA2.Thm.EvalHelpers

------------------------------------------------------------------------
-- Encoded proof-tree input and intended Tree output.

encAxComp : Fun1 -> Fun1 -> Term -> Tree
encAxComp f g t = nd (natCode tagAxComp)
                     (nd (codeF1 f)
                         (nd (codeF1 g) (code t)))

outAxComp : Fun1 -> Fun1 -> Term -> Tree
outAxComp f g t = codeFormula (atomic (eqn (ap1 (Comp f g) t)
                                           (ap1 f (ap1 g t))))

------------------------------------------------------------------------
-- body_axComp.
--
-- axComp f g t : LHS = ap1 (Comp f g) t , RHS = ap1 f (ap1 g t).
--   payT = Pair cf (Pair cg ct).
--   reify(LHS) = Pair K_a1 (Pair (Pair K_compTag (Pair cf cg)) ct)
--   reify(RHS) = Pair K_a1 (Pair cf (Pair K_a1 (Pair cg ct)))

body_axComp : Fun2
body_axComp =
  Fan
    -- LHS-build
    (Fan (Lift (KT (reify tagAp1)))
         (Fan (Fan (Lift (KT tagCode_compFunc))
                   (Fan (Lift (Comp Fst Snd))
                        (Lift (Comp Fst (Comp Snd Snd)))
                        Pair)
                   Pair)
              (Lift (Comp Snd (Comp Snd Snd)))
              Pair)
         Pair)
    -- RHS-build
    (Fan (Lift (KT (reify tagAp1)))
         (Fan (Lift (Comp Fst Snd))
              (Fan (Lift (KT (reify tagAp1)))
                   (Fan (Lift (Comp Fst (Comp Snd Snd)))
                        (Lift (Comp Snd (Comp Snd Snd)))
                        Pair)
                   Pair)
              Pair)
         Pair)
    Pair

------------------------------------------------------------------------
-- body_axComp_eval.

abstract

  body_axComp_eval : (f g : Fun1) (t bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axComp
            (ap2 Pair tagCode_axComp
                       (reify (nd (codeF1 f) (nd (codeF1 g) (code t))))) bb)
      (reify (outAxComp f g t))))
  body_axComp_eval f g t bb =
    let cf = reify (codeF1 f)
        cg = reify (codeF1 g)
        ct = reify (code t)
        payT = ap2 Pair cf (ap2 Pair cg ct)
        a    = ap2 Pair tagCode_axComp payT
        K1V  = tagAp1
        K1V_isValue = tagAp1_isValue
        K2V  = leftT (codeF1 (Comp I I))
        K2V_isValue = leftT_isValue _ (codeF1_isValue (Comp I I))
        K1   = reify K1V
        K2   = reify K2V
        ext_cf = liftCompFstSnd_evalPair tagCode_axComp cf (ap2 Pair cg ct) bb
        ext_cg = liftFstSndSnd_evalPair3 tagCode_axComp cf cg ct bb
        ext_ct = liftSndSndSnd_evalPair3 tagCode_axComp cf cg ct bb
        -- LHS = Pair K1 (Pair (Pair K2 (Pair cf cg)) ct)
        cfcg = pairOfFan_eval
                 (Lift (Comp Fst Snd))
                 (Lift (Comp Fst (Comp Snd Snd))) a bb cf cg ext_cf ext_cg
        kcfcg = pairOfConst_eval K2V K2V_isValue
                 (Fan (Lift (Comp Fst Snd))
                      (Lift (Comp Fst (Comp Snd Snd))) Pair) a bb
                 (ap2 Pair cf cg) cfcg
        midLHS = pairOfFan_eval
                   (Fan (Lift (KT K2))
                        (Fan (Lift (Comp Fst Snd))
                             (Lift (Comp Fst (Comp Snd Snd))) Pair) Pair)
                   (Lift (Comp Snd (Comp Snd Snd))) a bb
                   (ap2 Pair K2 (ap2 Pair cf cg)) ct kcfcg ext_ct
        lhsBuild = pairOfConst_eval K1V K1V_isValue
                     (Fan (Fan (Lift (KT K2))
                               (Fan (Lift (Comp Fst Snd))
                                    (Lift (Comp Fst (Comp Snd Snd))) Pair) Pair)
                          (Lift (Comp Snd (Comp Snd Snd))) Pair) a bb
                     (ap2 Pair (ap2 Pair K2 (ap2 Pair cf cg)) ct) midLHS
        -- RHS = Pair K1 (Pair cf (Pair K1 (Pair cg ct)))
        cgct = pairOfFan_eval
                 (Lift (Comp Fst (Comp Snd Snd)))
                 (Lift (Comp Snd (Comp Snd Snd))) a bb cg ct ext_cg ext_ct
        kcgct = pairOfConst_eval K1V K1V_isValue
                  (Fan (Lift (Comp Fst (Comp Snd Snd)))
                       (Lift (Comp Snd (Comp Snd Snd))) Pair) a bb
                  (ap2 Pair cg ct) cgct
        midRHS = pairOfFan_eval
                   (Lift (Comp Fst Snd))
                   (Fan (Lift (KT K1))
                        (Fan (Lift (Comp Fst (Comp Snd Snd)))
                             (Lift (Comp Snd (Comp Snd Snd))) Pair) Pair)
                   a bb cf (ap2 Pair K1 (ap2 Pair cg ct)) ext_cf kcgct
        rhsBuild = pairOfConst_eval K1V K1V_isValue
                     (Fan (Lift (Comp Fst Snd))
                          (Fan (Lift (KT K1))
                               (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                    (Lift (Comp Snd (Comp Snd Snd))) Pair) Pair)
                          Pair) a bb
                     (ap2 Pair cf (ap2 Pair K1 (ap2 Pair cg ct))) midRHS
    in pairOfFan_eval
         (Fan (Lift (KT K1))
              (Fan (Fan (Lift (KT K2))
                        (Fan (Lift (Comp Fst Snd))
                             (Lift (Comp Fst (Comp Snd Snd))) Pair) Pair)
                   (Lift (Comp Snd (Comp Snd Snd))) Pair) Pair)
         (Fan (Lift (KT K1))
              (Fan (Lift (Comp Fst Snd))
                   (Fan (Lift (KT K1))
                        (Fan (Lift (Comp Fst (Comp Snd Snd)))
                             (Lift (Comp Snd (Comp Snd Snd))) Pair) Pair) Pair)
              Pair)
         a bb
         (ap2 Pair K1 (ap2 Pair (ap2 Pair K2 (ap2 Pair cf cg)) ct))
         (ap2 Pair K1 (ap2 Pair cf (ap2 Pair K1 (ap2 Pair cg ct))))
         lhsBuild rhsBuild
