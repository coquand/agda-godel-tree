{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm.Parts.AxTreeRecLf
--
-- Self-contained dispatch material for the unified-recursor leaf axiom
--   axTreeRecLf : Deriv (ap2 (treeRec f s) p O = ap1 f p) .
--
-- Replaces the misdesigned axRecLf / axRecPLf split.

module BRA2.Thm.Parts.AxTreeRecLf where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Deriv
open import BRA2.Thm.Tag using (tagAxTreeRecLf)
open import BRA2.Thm.TagCodes
open import BRA2.Thm.EvalHelpers

------------------------------------------------------------------------
-- Encoded proof-tree input and intended Tree output.

encAxTreeRecLf : Fun1 -> Fun2 -> Term -> Tree
encAxTreeRecLf f s p = nd (natCode tagAxTreeRecLf)
                          (nd (codeF1 f) (nd (codeF2 s) (code p)))

outAxTreeRecLf : Fun1 -> Fun2 -> Term -> Tree
outAxTreeRecLf f s p =
  codeFormula (atomic (eqn (ap2 (treeRec f s) p O) (ap1 f p)))

------------------------------------------------------------------------
-- body_axTreeRecLf.
--
-- payT depth 3: Pair payF (Pair payS payP).
-- LHS encoded as: Pair K_a2 (Pair (Pair K_treeRec (Pair payF payS)) (Pair payP O))
-- RHS encoded as: Pair K_a1 (Pair payF payP)

body_axTreeRecLf : Fun2
body_axTreeRecLf =
  Fan
    -- LHS-build
    (Fan (Lift (KT (reify tagAp2)))
         (Fan (Fan (Lift (KT tagCode_treeRecFunc))
                   (Fan (Lift (Comp Fst Snd))
                        (Lift (Comp Fst (Comp Snd Snd)))
                        Pair)
                   Pair)
              (Fan (Lift (Comp Snd (Comp Snd Snd)))
                   (Lift (KT O))
                   Pair)
              Pair)
         Pair)
    -- RHS-build: Pair K_a1 (Pair payF payP)
    (Fan (Lift (KT (reify tagAp1)))
         (Fan (Lift (Comp Fst Snd))
              (Lift (Comp Snd (Comp Snd Snd)))
              Pair)
         Pair)
    Pair

------------------------------------------------------------------------
-- body_axTreeRecLf_eval.

abstract

  body_axTreeRecLf_eval : (f : Fun1) (s : Fun2) (p : Term) (bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axTreeRecLf
            (ap2 Pair tagCode_axTreeRecLf
                  (reify (nd (codeF1 f) (nd (codeF2 s) (code p))))) bb)
      (reify (outAxTreeRecLf f s p))))
  body_axTreeRecLf_eval f s p bb =
    let payFT  = reify (codeF1 f)
        payST  = reify (codeF2 s)
        payPT  = reify (code p)
        payT   = ap2 Pair payFT (ap2 Pair payST payPT)
        a      = ap2 Pair tagCode_axTreeRecLf payT
        K_a1V  = tagAp1
        K_a1V_isValue = tagAp1_isValue
        K_a1   = reify K_a1V
        K_a2V  = tagAp2
        K_a2V_isValue = tagAp2_isValue
        K_a2   = reify K_a2V
        K_trV  = leftT (codeF2 (treeRec I IfLf))
        K_trV_isValue = leftT_isValue _ (codeF2_isValue (treeRec I IfLf))
        K_tr   = reify K_trV
        K_ooV  = lf
        K_ooV_isValue = valO
        K_oo   = reify K_ooV
        ext_f  = liftCompFstSnd_evalPair tagCode_axTreeRecLf payFT
                   (ap2 Pair payST payPT) bb
        ext_s  = liftFstSndSnd_evalPair3 tagCode_axTreeRecLf payFT payST payPT bb
        ext_p  = liftSndSndSnd_evalPair3 tagCode_axTreeRecLf payFT payST payPT bb
        kOO    = liftKT_eval K_ooV K_ooV_isValue a bb
        ----------------------------------------------------------------
        -- LHS shape: Pair K_a2 (Pair (Pair K_tr (Pair payFT payST)) (Pair payPT K_oo))
        fs_pair = pairOfFan_eval (Lift (Comp Fst Snd))
                    (Lift (Comp Fst (Comp Snd Snd))) a bb
                    payFT payST ext_f ext_s
        kTrFs   = pairOfConst_eval K_trV K_trV_isValue
                    (Fan (Lift (Comp Fst Snd))
                         (Lift (Comp Fst (Comp Snd Snd))) Pair)
                    a bb (ap2 Pair payFT payST) fs_pair
        pOO     = pairOfFan_eval (Lift (Comp Snd (Comp Snd Snd)))
                    (Lift (KT K_oo)) a bb
                    payPT K_oo ext_p kOO
        lhs_inner = pairOfFan_eval
                      (Fan (Lift (KT K_tr))
                           (Fan (Lift (Comp Fst Snd))
                                (Lift (Comp Fst (Comp Snd Snd))) Pair) Pair)
                      (Fan (Lift (Comp Snd (Comp Snd Snd)))
                           (Lift (KT K_oo)) Pair)
                      a bb
                      (ap2 Pair K_tr (ap2 Pair payFT payST))
                      (ap2 Pair payPT K_oo)
                      kTrFs pOO
        lhsBuild = pairOfConst_eval K_a2V K_a2V_isValue
                     (Fan (Fan (Lift (KT K_tr))
                               (Fan (Lift (Comp Fst Snd))
                                    (Lift (Comp Fst (Comp Snd Snd))) Pair) Pair)
                          (Fan (Lift (Comp Snd (Comp Snd Snd)))
                               (Lift (KT K_oo)) Pair)
                          Pair)
                     a bb
                     (ap2 Pair (ap2 Pair K_tr (ap2 Pair payFT payST))
                                (ap2 Pair payPT K_oo))
                     lhs_inner
        ----------------------------------------------------------------
        -- RHS shape: Pair K_a1 (Pair payFT payPT)
        fp_pair = pairOfFan_eval (Lift (Comp Fst Snd))
                    (Lift (Comp Snd (Comp Snd Snd))) a bb
                    payFT payPT ext_f ext_p
        rhsBuild = pairOfConst_eval K_a1V K_a1V_isValue
                     (Fan (Lift (Comp Fst Snd))
                          (Lift (Comp Snd (Comp Snd Snd))) Pair)
                     a bb (ap2 Pair payFT payPT) fp_pair
    in pairOfFan_eval
         (Fan (Lift (KT K_a2))
              (Fan (Fan (Lift (KT K_tr))
                        (Fan (Lift (Comp Fst Snd))
                             (Lift (Comp Fst (Comp Snd Snd))) Pair) Pair)
                   (Fan (Lift (Comp Snd (Comp Snd Snd)))
                        (Lift (KT K_oo)) Pair)
                   Pair) Pair)
         (Fan (Lift (KT K_a1))
              (Fan (Lift (Comp Fst Snd))
                   (Lift (Comp Snd (Comp Snd Snd))) Pair)
              Pair)
         a bb
         (ap2 Pair K_a2 (ap2 Pair (ap2 Pair K_tr (ap2 Pair payFT payST))
                                    (ap2 Pair payPT K_oo)))
         (ap2 Pair K_a1 (ap2 Pair payFT payPT))
         lhsBuild rhsBuild

  ------------------------------------------------------------------
  -- Theorem 12 / Parts parametric variant for axTreeRecLf.
  -- Output is the explicit Pair structure with parametric fT, sT, pT
  -- slots so that Theorem 12 can plug arbitrary Term substituents.

  body_axTreeRecLf_eval_param : (fT sT pT bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axTreeRecLf
            (ap2 Pair tagCode_axTreeRecLf (ap2 Pair fT (ap2 Pair sT pT))) bb)
      (ap2 Pair
        (ap2 Pair (reify tagAp2)
          (ap2 Pair (ap2 Pair (reify (leftT (codeF2 (treeRec I IfLf))))
                              (ap2 Pair fT sT))
                    (ap2 Pair pT O)))
        (ap2 Pair (reify tagAp1) (ap2 Pair fT pT)))))
  body_axTreeRecLf_eval_param fT sT pT bb =
    let payFT  = fT
        payST  = sT
        payPT  = pT
        payT   = ap2 Pair payFT (ap2 Pair payST payPT)
        a      = ap2 Pair tagCode_axTreeRecLf payT
        K_a1V  = tagAp1
        K_a1V_isValue = tagAp1_isValue
        K_a1   = reify K_a1V
        K_a2V  = tagAp2
        K_a2V_isValue = tagAp2_isValue
        K_a2   = reify K_a2V
        K_trV  = leftT (codeF2 (treeRec I IfLf))
        K_trV_isValue = leftT_isValue _ (codeF2_isValue (treeRec I IfLf))
        K_tr   = reify K_trV
        K_ooV  = lf
        K_ooV_isValue = valO
        K_oo   = reify K_ooV
        ext_f  = liftCompFstSnd_evalPair tagCode_axTreeRecLf payFT
                   (ap2 Pair payST payPT) bb
        ext_s  = liftFstSndSnd_evalPair3 tagCode_axTreeRecLf payFT payST payPT bb
        ext_p  = liftSndSndSnd_evalPair3 tagCode_axTreeRecLf payFT payST payPT bb
        kOO    = liftKT_eval K_ooV K_ooV_isValue a bb
        ----------------------------------------------------------------
        fs_pair = pairOfFan_eval (Lift (Comp Fst Snd))
                    (Lift (Comp Fst (Comp Snd Snd))) a bb
                    payFT payST ext_f ext_s
        kTrFs   = pairOfConst_eval K_trV K_trV_isValue
                    (Fan (Lift (Comp Fst Snd))
                         (Lift (Comp Fst (Comp Snd Snd))) Pair)
                    a bb (ap2 Pair payFT payST) fs_pair
        pOO     = pairOfFan_eval (Lift (Comp Snd (Comp Snd Snd)))
                    (Lift (KT K_oo)) a bb
                    payPT K_oo ext_p kOO
        lhs_inner = pairOfFan_eval
                      (Fan (Lift (KT K_tr))
                           (Fan (Lift (Comp Fst Snd))
                                (Lift (Comp Fst (Comp Snd Snd))) Pair) Pair)
                      (Fan (Lift (Comp Snd (Comp Snd Snd)))
                           (Lift (KT K_oo)) Pair)
                      a bb
                      (ap2 Pair K_tr (ap2 Pair payFT payST))
                      (ap2 Pair payPT K_oo)
                      kTrFs pOO
        lhsBuild = pairOfConst_eval K_a2V K_a2V_isValue
                     (Fan (Fan (Lift (KT K_tr))
                               (Fan (Lift (Comp Fst Snd))
                                    (Lift (Comp Fst (Comp Snd Snd))) Pair) Pair)
                          (Fan (Lift (Comp Snd (Comp Snd Snd)))
                               (Lift (KT K_oo)) Pair)
                          Pair)
                     a bb
                     (ap2 Pair (ap2 Pair K_tr (ap2 Pair payFT payST))
                                (ap2 Pair payPT K_oo))
                     lhs_inner
        ----------------------------------------------------------------
        fp_pair = pairOfFan_eval (Lift (Comp Fst Snd))
                    (Lift (Comp Snd (Comp Snd Snd))) a bb
                    payFT payPT ext_f ext_p
        rhsBuild = pairOfConst_eval K_a1V K_a1V_isValue
                     (Fan (Lift (Comp Fst Snd))
                          (Lift (Comp Snd (Comp Snd Snd))) Pair)
                     a bb (ap2 Pair payFT payPT) fp_pair
    in pairOfFan_eval
         (Fan (Lift (KT K_a2))
              (Fan (Fan (Lift (KT K_tr))
                        (Fan (Lift (Comp Fst Snd))
                             (Lift (Comp Fst (Comp Snd Snd))) Pair) Pair)
                   (Fan (Lift (Comp Snd (Comp Snd Snd)))
                        (Lift (KT K_oo)) Pair)
                   Pair) Pair)
         (Fan (Lift (KT K_a1))
              (Fan (Lift (Comp Fst Snd))
                   (Lift (Comp Snd (Comp Snd Snd))) Pair)
              Pair)
         a bb
         (ap2 Pair K_a2 (ap2 Pair (ap2 Pair K_tr (ap2 Pair payFT payST))
                                    (ap2 Pair payPT K_oo)))
         (ap2 Pair K_a1 (ap2 Pair payFT payPT))
         lhsBuild rhsBuild
