{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm12AsymCases
--
-- Parametric asymmetric Theorem 12 for primitives whose defining
-- axioms have RHS WITHOUT sub-functor applications.  These admit a
-- single-dispatch construction:
--
--   1. Use thmTDispAxX_param at payload = ap1 cor (var k).
--   2. Bridge RHS via the primitive's defining axiom + cong1 cor + cor
--      reduction (axRecLf for the leaf cases).
--
-- Cases delivered here (10):
--   * thm12_Z_param          : Z   (Fun1, parametric var 0)
--   * thm12_Const_param      : Const (Fun2, parametric, axConst)
--   * thm12_Snd_pair_shape   : Snd at Pair shape (parametric, axSnd)
--   * thm12_FstLf_at_O       : Fst at x = O (closed, axFstLf)
--   * thm12_SndLf_at_O       : Snd at x = O (closed, axSndLf)
--   * thm12_IfLfL_pair_LR    : IfLf at (O, Pair v1 v2) (parametric, axIfLfL)
--   * thm12_IfLfLL_at_OO     : IfLf at (O, O) (closed, axIfLfLL)
--   * thm12_TreeEqLL_at_OO   : TreeEq at (O, O) (closed, axTreeEqLL)
--   * thm12_Pair_param       : Pair (Fun2, parametric, reflexivity via cor)
--   * thm12_IfLfNL_pair_O    : IfLf at (Pair v1 v2, O) (parametric, axIfLfNL)
--
-- Cases in BRA.Thm12AsymParametric (2):
--   * thm12_I_param          : I (Fun1, parametric var 0, axI)
--   * thm12_Fst_pair_shape   : Fst at Pair shape (parametric, axFst)
--
-- Cases in BRA.Thm12AsymBaseCases (3):
--   * thm12_I_at_O           : I at x = O (closed canonical)
--   * thm12_Z_at_O           : Z at x = O (closed canonical)
--   * thm12_Fst_at_PairOO    : Fst at x = Pair O O (closed canonical)
--
-- Cases NOT delivered (require IH composition beyond single dispatch):
--   * Comp, Comp2 (Fun1):    axiom RHS involves sub-functor applications.
--   * Lift, Post, Fan (Fun2): same.
--   * Rec, RecP, TreeEqNN, IfLfN: same.
--   * Full ruleIndBT-dispatched parametric versions: combine per-shape
--     cases via ruleIndBT.  Mechanical given the per-shape proofs.
-- Composing these requires combining Theorem 12 instances of the
-- sub-functors via mp / sb on Df-indices (analogous to Guard's
-- meta-induction step cases).
--
-- No postulates, no holes.

module BRA.Thm12AsymCases where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor
open import BRA.Thm14CodeFTeqAsym
open import BRA.Thm.ThmT using
  ( thmT ; tagCode_axKT ; tagCode_axConst
  ; tagCode_axIfLfL ; tagCode_axIfLfN
  ; tagCode_axIfLfLL ; tagCode_axIfLfNL
  ; tagCode_axSnd ; tagCode_axFstLf ; tagCode_axSndLf
  ; tagCode_axRefl ; tagCode_axTreeEqLL
  ; tagCode_axTreeEqLN ; tagCode_axTreeEqNL
  ; thmTDispAxZ_param ; thmTDispAxConst_param
  ; thmTDispAxIfLfL_param ; thmTDispAxIfLfN_param
  ; thmTDispAxIfLfLL_param ; thmTDispAxIfLfNL_param
  ; thmTDispAxSnd_param ; thmTDispAxFstLf_param ; thmTDispAxSndLf_param
  ; thmTDispAxRefl_param ; thmTDispAxTreeEqLL_param
  ; thmTDispAxTreeEqLN_param ; thmTDispAxTreeEqNL_param )

------------------------------------------------------------------------
-- thm12_Z_param : Theorem 12 for f = Z at variable input.

thm12_Z_param :
  Sigma Term (\ Df_term ->
    Deriv (atomic (eqn (ap1 thmT Df_term) (codeFTeq1Asym Z (var zero)))))
thm12_Z_param =
  let
    -- thmTDispAxZ_param gives:
    --   thmT (Pair tagCode_axKT (Pair (codeF1 Z) xT))
    --     = mkEqT (mkAp1T (codeF1 Z) xT) O
    -- (encoded  Z(xT) = O ).

    Df_term : Term
    Df_term = ap2 Pair tagCode_axKT
                  (ap2 Pair (reify (codeF1 Z)) (ap1 cor (var zero)))

    disp : Deriv (atomic (eqn
            (ap1 thmT Df_term)
            (ap2 Pair (ap2 Pair (reify tagAp1)
                                (ap2 Pair (reify (codeF1 Z))
                                           (ap1 cor (var zero))))
                       O)))
    disp = thmTDispAxZ_param (ap1 cor (var zero))

    -- Bridge RHS subterm:  O  ->  cor (Z (var 0)) .
    --   axZ (var 0)            : Z (var 0) = O
    --   cong1 cor              : cor (Z (var 0)) = cor O
    --   axRecLf O stepCor      : cor O = O
    --   ruleTrans + ruleSym    : O = cor (Z (var 0)) .

    bR_axZ : Deriv (atomic (eqn (ap1 Z (var zero)) O))
    bR_axZ = axZ (var zero)

    bR_cong : Deriv (atomic (eqn (ap1 cor (ap1 Z (var zero))) (ap1 cor O)))
    bR_cong = cong1 cor bR_axZ

    bR_corO : Deriv (atomic (eqn (ap1 cor O) O))
    bR_corO = axRecLf O stepCor

    bR_combined : Deriv (atomic (eqn (ap1 cor (ap1 Z (var zero))) O))
    bR_combined = ruleTrans bR_cong bR_corO

    bR : Deriv (atomic (eqn O (ap1 cor (ap1 Z (var zero)))))
    bR = ruleSym bR_combined

    -- Lift bridge through outer ap2 Pair.
    bridge : Deriv (atomic (eqn
              (ap2 Pair (ap2 Pair (reify tagAp1)
                                  (ap2 Pair (reify (codeF1 Z))
                                             (ap1 cor (var zero))))
                         O)
              (codeFTeq1Asym Z (var zero))))
    bridge = congR Pair
               (ap2 Pair (reify tagAp1)
                          (ap2 Pair (reify (codeF1 Z))
                                     (ap1 cor (var zero))))
               bR

    pf_final : Deriv (atomic (eqn (ap1 thmT Df_term)
                                   (codeFTeq1Asym Z (var zero))))
    pf_final = ruleTrans disp bridge

  in mkSigma Df_term pf_final

------------------------------------------------------------------------
-- thm12_Const_param : Theorem 12 for g = Const at two variable inputs.

module ConstCase (v1 v2 : Nat) where

  thm12_Const_param :
    Sigma Term (\ Df_term ->
      Deriv (atomic (eqn (ap1 thmT Df_term)
                          (codeFTeq2Asym Const (var v1) (var v2)))))
  thm12_Const_param =
    let
      v1T : Term
      v1T = var v1

      v2T : Term
      v2T = var v2

      -- thmTDispAxConst_param at aT = cor v1, bT = cor v2 gives:
      --   thmT (Pair tagCode_axConst (Pair (cor v1) (cor v2)))
      --     = mkEqT (mkAp2T (codeF2 Const) (cor v1) (cor v2)) (cor v1)
      -- (encoded  Const(cor v1, cor v2) = cor v1 ).

      Df_term : Term
      Df_term = ap2 Pair tagCode_axConst
                    (ap2 Pair (ap1 cor v1T) (ap1 cor v2T))

      disp : Deriv (atomic (eqn
              (ap1 thmT Df_term)
              (ap2 Pair (ap2 Pair (reify tagAp2)
                                  (ap2 Pair (reify (codeF2 Const))
                                             (ap2 Pair (ap1 cor v1T)
                                                        (ap1 cor v2T))))
                         (ap1 cor v1T))))
      disp = thmTDispAxConst_param (ap1 cor v1T) (ap1 cor v2T)

      -- Bridge RHS:  cor v1  ->  cor (Const v1 v2) .
      --   axConst v1 v2     : Const v1 v2 = v1
      --   cong1 cor          : cor (Const v1 v2) = cor v1
      --   ruleSym            : cor v1 = cor (Const v1 v2) .

      bR : Deriv (atomic (eqn (ap1 cor v1T)
                               (ap1 cor (ap2 Const v1T v2T))))
      bR = ruleSym (cong1 cor (axConst v1T v2T))

      bridge : Deriv (atomic (eqn
                (ap2 Pair (ap2 Pair (reify tagAp2)
                                    (ap2 Pair (reify (codeF2 Const))
                                               (ap2 Pair (ap1 cor v1T)
                                                          (ap1 cor v2T))))
                           (ap1 cor v1T))
                (codeFTeq2Asym Const v1T v2T)))
      bridge = congR Pair
                 (ap2 Pair (reify tagAp2)
                            (ap2 Pair (reify (codeF2 Const))
                                       (ap2 Pair (ap1 cor v1T)
                                                  (ap1 cor v2T))))
                 bR

      pf_final : Deriv (atomic (eqn (ap1 thmT Df_term)
                                     (codeFTeq2Asym Const v1T v2T)))
      pf_final = ruleTrans disp bridge

    in mkSigma Df_term pf_final

------------------------------------------------------------------------
-- thm12_Snd_pair_shape : Theorem 12 for f = Snd at Pair shape.
-- Mirror of thm12_Fst_pair_shape in BRA.Thm12AsymParametric.

module SndPairShape (v1 v2 : Nat) where

  thm12_Snd_pair_shape :
    Sigma Term (\ Df_term ->
      Deriv (atomic (eqn (ap1 thmT Df_term)
                          (codeFTeq1Asym Snd (ap2 Pair (var v1) (var v2))))))
  thm12_Snd_pair_shape =
    let
      v1T : Term
      v1T = var v1

      v2T : Term
      v2T = var v2

      pairT : Term
      pairT = ap2 Pair v1T v2T

      Df_term : Term
      Df_term = ap2 Pair tagCode_axSnd
                    (ap2 Pair (ap1 cor v1T) (ap1 cor v2T))

      disp : Deriv (atomic (eqn
              (ap1 thmT Df_term)
              (ap2 Pair
                (ap2 Pair (reify tagAp1)
                  (ap2 Pair (reify (codeF1 Snd))
                    (ap2 Pair (reify tagAp2)
                      (ap2 Pair (reify (codeF2 Pair))
                        (ap2 Pair (ap1 cor v1T) (ap1 cor v2T))))))
                (ap1 cor v2T))))
      disp = thmTDispAxSnd_param (ap1 cor v1T) (ap1 cor v2T)

      cor_red_Pair : Deriv (atomic (eqn
                       (ap1 cor pairT)
                       (ap2 Pair (reify tagAp2)
                         (ap2 Pair (reify (codeF2 Pair))
                           (ap2 Pair (ap1 cor v1T) (ap1 cor v2T))))))
      cor_red_Pair =
        let recs = ap2 Pair (ap1 cor v1T) (ap1 cor v2T)
            axNd = axRecNd O stepCor v1T v2T
            stRed = stepCorRed pairT recs
        in ruleTrans axNd stRed

      bridge_LHS_inner : Deriv (atomic (eqn
                          (ap2 Pair (reify (codeF1 Snd)) (ap1 cor pairT))
                          (ap2 Pair (reify (codeF1 Snd))
                            (ap2 Pair (reify tagAp2)
                              (ap2 Pair (reify (codeF2 Pair))
                                (ap2 Pair (ap1 cor v1T) (ap1 cor v2T)))))))
      bridge_LHS_inner = congR Pair (reify (codeF1 Snd)) cor_red_Pair

      bridge_LHS : Deriv (atomic (eqn
                    (mkAp1T (reify (codeF1 Snd)) (ap1 cor pairT))
                    (ap2 Pair (reify tagAp1)
                      (ap2 Pair (reify (codeF1 Snd))
                        (ap2 Pair (reify tagAp2)
                          (ap2 Pair (reify (codeF2 Pair))
                            (ap2 Pair (ap1 cor v1T) (ap1 cor v2T))))))))
      bridge_LHS = congR Pair (reify tagAp1) bridge_LHS_inner

      bR : Deriv (atomic (eqn (ap1 cor (ap1 Snd pairT))
                               (ap1 cor v2T)))
      bR = cong1 cor (axSnd v1T v2T)

      step_LHS : Deriv (atomic (eqn
                  (ap2 Pair
                    (ap2 Pair (reify tagAp1)
                      (ap2 Pair (reify (codeF1 Snd))
                        (ap2 Pair (reify tagAp2)
                          (ap2 Pair (reify (codeF2 Pair))
                            (ap2 Pair (ap1 cor v1T) (ap1 cor v2T))))))
                    (ap1 cor v2T))
                  (ap2 Pair
                    (mkAp1T (reify (codeF1 Snd)) (ap1 cor pairT))
                    (ap1 cor v2T))))
      step_LHS = congL Pair (ap1 cor v2T) (ruleSym bridge_LHS)

      step_RHS : Deriv (atomic (eqn
                  (ap2 Pair
                    (mkAp1T (reify (codeF1 Snd)) (ap1 cor pairT))
                    (ap1 cor v2T))
                  (ap2 Pair
                    (mkAp1T (reify (codeF1 Snd)) (ap1 cor pairT))
                    (ap1 cor (ap1 Snd pairT)))))
      step_RHS = congR Pair
                   (mkAp1T (reify (codeF1 Snd)) (ap1 cor pairT))
                   (ruleSym bR)

      bridge_total : Deriv (atomic (eqn
              (ap2 Pair
                (ap2 Pair (reify tagAp1)
                  (ap2 Pair (reify (codeF1 Snd))
                    (ap2 Pair (reify tagAp2)
                      (ap2 Pair (reify (codeF2 Pair))
                        (ap2 Pair (ap1 cor v1T) (ap1 cor v2T))))))
                (ap1 cor v2T))
              (codeFTeq1Asym Snd pairT)))
      bridge_total = ruleTrans step_LHS step_RHS

      pf_final : Deriv (atomic (eqn (ap1 thmT Df_term)
                                     (codeFTeq1Asym Snd pairT)))
      pf_final = ruleTrans disp bridge_total

    in mkSigma Df_term pf_final

------------------------------------------------------------------------
-- thm12_FstLf_at_O : Theorem 12 for f = Fst at x = O (leaf case).
-- Uses axFstLf : Fst O = O and the FstLf safe-default dispatch.

thm12_FstLf_at_O :
  Sigma Term (\ Df_term ->
    Deriv (atomic (eqn (ap1 thmT Df_term) (codeFTeq1Asym Fst O))))
thm12_FstLf_at_O =
  let
    Df_term : Term
    Df_term = ap2 Pair tagCode_axFstLf O

    -- thmTDispAxFstLf_param at any payT gives:
    --   thmT (Pair tagCode_axFstLf payT) = reify outAxFstLf
    --   = reify (codeFormula (atomic (eqn (Fst O) O)))
    --   = mkEqT (mkAp1T (codeF1 Fst) O) O .

    disp : Deriv (atomic (eqn (ap1 thmT Df_term)
                               (reify (codeFormula
                                 (atomic (eqn (ap1 Fst O) O))))))
    disp = thmTDispAxFstLf_param O

    -- Bridge: codeFTeq1Asym Fst O is Deriv-equal to the static GN
    -- of (Fst O = O), via cor (Fst O) reductions.

    cor_O : Deriv (atomic (eqn O (ap1 cor O)))
    cor_O = ruleSym (axRecLf O stepCor)

    -- LHS subterm bridge:  O  ->  ap1 cor O .
    bL_inner : Deriv (atomic (eqn
                (ap2 Pair (reify (codeF1 Fst)) O)
                (ap2 Pair (reify (codeF1 Fst)) (ap1 cor O))))
    bL_inner = congR Pair (reify (codeF1 Fst)) cor_O

    bL : Deriv (atomic (eqn
            (mkAp1T (reify (codeF1 Fst)) O)
            (mkAp1T (reify (codeF1 Fst)) (ap1 cor O))))
    bL = congR Pair (reify tagAp1) bL_inner

    -- RHS subterm bridge:  O  ->  ap1 cor (ap1 Fst O) .
    --   axFstLf       : Fst O = O
    --   cong1 cor     : cor (Fst O) = cor O
    --   axRecLf       : cor O = O
    --   ruleSym       : O = cor (Fst O) .

    bR_combined : Deriv (atomic (eqn (ap1 cor (ap1 Fst O)) O))
    bR_combined = ruleTrans (cong1 cor axFstLf) (axRecLf O stepCor)

    bR : Deriv (atomic (eqn O (ap1 cor (ap1 Fst O))))
    bR = ruleSym bR_combined

    step1 : Deriv (atomic (eqn
              (ap2 Pair (mkAp1T (reify (codeF1 Fst)) O) O)
              (ap2 Pair (mkAp1T (reify (codeF1 Fst)) (ap1 cor O)) O)))
    step1 = congL Pair O bL

    step2 : Deriv (atomic (eqn
              (ap2 Pair (mkAp1T (reify (codeF1 Fst)) (ap1 cor O)) O)
              (ap2 Pair (mkAp1T (reify (codeF1 Fst)) (ap1 cor O))
                         (ap1 cor (ap1 Fst O)))))
    step2 = congR Pair (mkAp1T (reify (codeF1 Fst)) (ap1 cor O)) bR

    bridge : Deriv (atomic (eqn
                (reify (codeFormula (atomic (eqn (ap1 Fst O) O))))
                (codeFTeq1Asym Fst O)))
    bridge = ruleTrans step1 step2

    pf_final : Deriv (atomic (eqn (ap1 thmT Df_term)
                                   (codeFTeq1Asym Fst O)))
    pf_final = ruleTrans disp bridge

  in mkSigma Df_term pf_final

------------------------------------------------------------------------
-- thm12_SndLf_at_O : analogous to thm12_FstLf_at_O.

thm12_SndLf_at_O :
  Sigma Term (\ Df_term ->
    Deriv (atomic (eqn (ap1 thmT Df_term) (codeFTeq1Asym Snd O))))
thm12_SndLf_at_O =
  let
    Df_term : Term
    Df_term = ap2 Pair tagCode_axSndLf O

    disp : Deriv (atomic (eqn (ap1 thmT Df_term)
                               (reify (codeFormula
                                 (atomic (eqn (ap1 Snd O) O))))))
    disp = thmTDispAxSndLf_param O

    cor_O : Deriv (atomic (eqn O (ap1 cor O)))
    cor_O = ruleSym (axRecLf O stepCor)

    bL_inner : Deriv (atomic (eqn
                (ap2 Pair (reify (codeF1 Snd)) O)
                (ap2 Pair (reify (codeF1 Snd)) (ap1 cor O))))
    bL_inner = congR Pair (reify (codeF1 Snd)) cor_O

    bL : Deriv (atomic (eqn
            (mkAp1T (reify (codeF1 Snd)) O)
            (mkAp1T (reify (codeF1 Snd)) (ap1 cor O))))
    bL = congR Pair (reify tagAp1) bL_inner

    bR_combined : Deriv (atomic (eqn (ap1 cor (ap1 Snd O)) O))
    bR_combined = ruleTrans (cong1 cor axSndLf) (axRecLf O stepCor)

    bR : Deriv (atomic (eqn O (ap1 cor (ap1 Snd O))))
    bR = ruleSym bR_combined

    step1 : Deriv (atomic (eqn
              (ap2 Pair (mkAp1T (reify (codeF1 Snd)) O) O)
              (ap2 Pair (mkAp1T (reify (codeF1 Snd)) (ap1 cor O)) O)))
    step1 = congL Pair O bL

    step2 : Deriv (atomic (eqn
              (ap2 Pair (mkAp1T (reify (codeF1 Snd)) (ap1 cor O)) O)
              (ap2 Pair (mkAp1T (reify (codeF1 Snd)) (ap1 cor O))
                         (ap1 cor (ap1 Snd O)))))
    step2 = congR Pair (mkAp1T (reify (codeF1 Snd)) (ap1 cor O)) bR

    bridge : Deriv (atomic (eqn
                (reify (codeFormula (atomic (eqn (ap1 Snd O) O))))
                (codeFTeq1Asym Snd O)))
    bridge = ruleTrans step1 step2

    pf_final : Deriv (atomic (eqn (ap1 thmT Df_term)
                                   (codeFTeq1Asym Snd O)))
    pf_final = ruleTrans disp bridge

  in mkSigma Df_term pf_final

------------------------------------------------------------------------
-- thm12_IfLfL_pair_LR : Theorem 12 for g = IfLf at IfLf O (Pair a b) shape.
--
-- The encoded equation at  x = O , v = Pair (var v1) (var v2)  is
--   "IfLf O (Pair v1 v2) = v1"  -- by axIfLfL.

module IfLfLCase (v1 v2 : Nat) where

  thm12_IfLfL_pair_LR :
    Sigma Term (\ Df_term ->
      Deriv (atomic (eqn (ap1 thmT Df_term)
                          (codeFTeq2Asym IfLf O
                            (ap2 Pair (var v1) (var v2))))))
  thm12_IfLfL_pair_LR =
    let
      v1T : Term
      v1T = var v1

      v2T : Term
      v2T = var v2

      pairT : Term
      pairT = ap2 Pair v1T v2T

      -- thmTDispAxIfLfL_param at aT = cor v1, bT = cor v2 gives:
      --   thmT (Pair tagCode_axIfLfL (Pair (cor v1) (cor v2)))
      --     = mkEqT (mkAp2T (codeF2 IfLf) O (mkAp2T (codeF2 Pair) (cor v1) (cor v2)))
      --             (cor v1)

      Df_term : Term
      Df_term = ap2 Pair tagCode_axIfLfL
                    (ap2 Pair (ap1 cor v1T) (ap1 cor v2T))

      disp : Deriv (atomic (eqn
              (ap1 thmT Df_term)
              (ap2 Pair
                (ap2 Pair (reify tagAp2)
                  (ap2 Pair (reify (codeF2 IfLf))
                    (ap2 Pair O
                      (ap2 Pair (reify tagAp2)
                        (ap2 Pair (reify (codeF2 Pair))
                          (ap2 Pair (ap1 cor v1T) (ap1 cor v2T)))))))
                (ap1 cor v1T))))
      disp = thmTDispAxIfLfL_param (ap1 cor v1T) (ap1 cor v2T)

      -- Bridge LHS:  the inner subterm (mkAp2T pairCodeF2T (cor v1) (cor v2))
      -- needs to come from  cor (Pair v1 v2) .

      cor_red_pair : Deriv (atomic (eqn (ap1 cor pairT)
                              (ap2 Pair (reify tagAp2)
                                (ap2 Pair (reify (codeF2 Pair))
                                  (ap2 Pair (ap1 cor v1T) (ap1 cor v2T))))))
      cor_red_pair =
        let recs = ap2 Pair (ap1 cor v1T) (ap1 cor v2T)
            axNd = axRecNd O stepCor v1T v2T
            stRed = stepCorRed pairT recs
        in ruleTrans axNd stRed

      -- LHS of disp's RHS-form has structure
      --   mkAp2T (codeF2 IfLf) O (mkAp2T pairCodeF2T (cor v1) (cor v2))
      -- and codeFTeq2Asym IfLf O (Pair v1 v2) has
      --   mkAp2T (codeF2 IfLf) (cor O) (cor (Pair v1 v2))
      -- with cor O = O and cor (Pair v1 v2) = (above).

      cor_O : Deriv (atomic (eqn O (ap1 cor O)))
      cor_O = ruleSym (axRecLf O stepCor)

      bridge_LHS_innermost : Deriv (atomic (eqn
                  (ap2 Pair O
                    (ap2 Pair (reify tagAp2)
                      (ap2 Pair (reify (codeF2 Pair))
                        (ap2 Pair (ap1 cor v1T) (ap1 cor v2T)))))
                  (ap2 Pair (ap1 cor O) (ap1 cor pairT))))
      bridge_LHS_innermost = ruleTrans
        (congL Pair (ap2 Pair (reify tagAp2)
                              (ap2 Pair (reify (codeF2 Pair))
                                (ap2 Pair (ap1 cor v1T) (ap1 cor v2T))))
                    cor_O)
        (congR Pair (ap1 cor O) (ruleSym cor_red_pair))

      bridge_LHS_inner : Deriv (atomic (eqn
                          (ap2 Pair (reify (codeF2 IfLf))
                            (ap2 Pair O
                              (ap2 Pair (reify tagAp2)
                                (ap2 Pair (reify (codeF2 Pair))
                                  (ap2 Pair (ap1 cor v1T) (ap1 cor v2T))))))
                          (ap2 Pair (reify (codeF2 IfLf))
                            (ap2 Pair (ap1 cor O) (ap1 cor pairT)))))
      bridge_LHS_inner = congR Pair (reify (codeF2 IfLf)) bridge_LHS_innermost

      bridge_LHS : Deriv (atomic (eqn
                    (ap2 Pair (reify tagAp2)
                      (ap2 Pair (reify (codeF2 IfLf))
                        (ap2 Pair O
                          (ap2 Pair (reify tagAp2)
                            (ap2 Pair (reify (codeF2 Pair))
                              (ap2 Pair (ap1 cor v1T) (ap1 cor v2T)))))))
                    (mkAp2T (reify (codeF2 IfLf)) (ap1 cor O) (ap1 cor pairT))))
      bridge_LHS = congR Pair (reify tagAp2) bridge_LHS_inner

      -- Bridge RHS:  cor v1 -> cor (IfLf O (Pair v1 v2)) .
      --   axIfLfL v1 v2  : IfLf O (Pair v1 v2) = v1
      --   cong1 cor       : cor (IfLf O (Pair v1 v2)) = cor v1
      --   ruleSym         : cor v1 = cor (IfLf O (Pair v1 v2)) .

      bR : Deriv (atomic (eqn (ap1 cor v1T)
                               (ap1 cor (ap2 IfLf O pairT))))
      bR = ruleSym (cong1 cor (axIfLfL v1T v2T))

      step_LHS : Deriv (atomic (eqn
                  (ap2 Pair
                    (ap2 Pair (reify tagAp2)
                      (ap2 Pair (reify (codeF2 IfLf))
                        (ap2 Pair O
                          (ap2 Pair (reify tagAp2)
                            (ap2 Pair (reify (codeF2 Pair))
                              (ap2 Pair (ap1 cor v1T) (ap1 cor v2T)))))))
                    (ap1 cor v1T))
                  (ap2 Pair
                    (mkAp2T (reify (codeF2 IfLf)) (ap1 cor O) (ap1 cor pairT))
                    (ap1 cor v1T))))
      step_LHS = congL Pair (ap1 cor v1T) bridge_LHS

      step_RHS : Deriv (atomic (eqn
                  (ap2 Pair
                    (mkAp2T (reify (codeF2 IfLf)) (ap1 cor O) (ap1 cor pairT))
                    (ap1 cor v1T))
                  (ap2 Pair
                    (mkAp2T (reify (codeF2 IfLf)) (ap1 cor O) (ap1 cor pairT))
                    (ap1 cor (ap2 IfLf O pairT)))))
      step_RHS = congR Pair
                   (mkAp2T (reify (codeF2 IfLf)) (ap1 cor O) (ap1 cor pairT))
                   bR

      bridge_total : Deriv (atomic (eqn
                  (ap2 Pair
                    (ap2 Pair (reify tagAp2)
                      (ap2 Pair (reify (codeF2 IfLf))
                        (ap2 Pair O
                          (ap2 Pair (reify tagAp2)
                            (ap2 Pair (reify (codeF2 Pair))
                              (ap2 Pair (ap1 cor v1T) (ap1 cor v2T)))))))
                    (ap1 cor v1T))
                  (codeFTeq2Asym IfLf O pairT)))
      bridge_total = ruleTrans step_LHS step_RHS

      pf_final : Deriv (atomic (eqn (ap1 thmT Df_term)
                                     (codeFTeq2Asym IfLf O pairT)))
      pf_final = ruleTrans disp bridge_total

    in mkSigma Df_term pf_final

------------------------------------------------------------------------
-- thm12_IfLfLL_at_OO : Theorem 12 for g = IfLf at x = O, v = O.
-- Closed canonical input, axIfLfLL : IfLf O O = O.

thm12_IfLfLL_at_OO :
  Sigma Term (\ Df_term ->
    Deriv (atomic (eqn (ap1 thmT Df_term) (codeFTeq2Asym IfLf O O))))
thm12_IfLfLL_at_OO =
  let
    Df_term : Term
    Df_term = ap2 Pair tagCode_axIfLfLL O

    disp : Deriv (atomic (eqn (ap1 thmT Df_term)
                               (reify (codeFormula
                                 (atomic (eqn (ap2 IfLf O O) O))))))
    disp = thmTDispAxIfLfLL_param O

    cor_O : Deriv (atomic (eqn O (ap1 cor O)))
    cor_O = ruleSym (axRecLf O stepCor)

    -- Bridge LHS subterm:  mkAp2T (codeF2 IfLf) O O  ->  with cor O cor O.
    bL_inner_a : Deriv (atomic (eqn
                  (ap2 Pair (reify (codeF2 IfLf))
                    (ap2 Pair O O))
                  (ap2 Pair (reify (codeF2 IfLf))
                    (ap2 Pair (ap1 cor O) O))))
    bL_inner_a = congR Pair (reify (codeF2 IfLf))
                   (congL Pair O cor_O)

    bL_inner_b : Deriv (atomic (eqn
                  (ap2 Pair (reify (codeF2 IfLf))
                    (ap2 Pair (ap1 cor O) O))
                  (ap2 Pair (reify (codeF2 IfLf))
                    (ap2 Pair (ap1 cor O) (ap1 cor O)))))
    bL_inner_b = congR Pair (reify (codeF2 IfLf))
                   (congR Pair (ap1 cor O) cor_O)

    bL : Deriv (atomic (eqn
            (mkAp2T (reify (codeF2 IfLf)) O O)
            (mkAp2T (reify (codeF2 IfLf)) (ap1 cor O) (ap1 cor O))))
    bL = congR Pair (reify tagAp2)
           (ruleTrans bL_inner_a bL_inner_b)

    bR_combined : Deriv (atomic (eqn (ap1 cor (ap2 IfLf O O)) O))
    bR_combined = ruleTrans (cong1 cor axIfLfLL) (axRecLf O stepCor)

    bR : Deriv (atomic (eqn O (ap1 cor (ap2 IfLf O O))))
    bR = ruleSym bR_combined

    step1 : Deriv (atomic (eqn
              (ap2 Pair (mkAp2T (reify (codeF2 IfLf)) O O) O)
              (ap2 Pair (mkAp2T (reify (codeF2 IfLf)) (ap1 cor O) (ap1 cor O)) O)))
    step1 = congL Pair O bL

    step2 : Deriv (atomic (eqn
              (ap2 Pair (mkAp2T (reify (codeF2 IfLf)) (ap1 cor O) (ap1 cor O)) O)
              (ap2 Pair (mkAp2T (reify (codeF2 IfLf)) (ap1 cor O) (ap1 cor O))
                         (ap1 cor (ap2 IfLf O O)))))
    step2 = congR Pair (mkAp2T (reify (codeF2 IfLf)) (ap1 cor O) (ap1 cor O)) bR

    bridge : Deriv (atomic (eqn
                (reify (codeFormula (atomic (eqn (ap2 IfLf O O) O))))
                (codeFTeq2Asym IfLf O O)))
    bridge = ruleTrans step1 step2

    pf_final : Deriv (atomic (eqn (ap1 thmT Df_term)
                                   (codeFTeq2Asym IfLf O O)))
    pf_final = ruleTrans disp bridge

  in mkSigma Df_term pf_final

------------------------------------------------------------------------
-- thm12_TreeEqLL_at_OO : Theorem 12 for g = TreeEq at x = O, v = O.
-- Closed canonical input, axTreeEqLL : TreeEq O O = O.

thm12_TreeEqLL_at_OO :
  Sigma Term (\ Df_term ->
    Deriv (atomic (eqn (ap1 thmT Df_term) (codeFTeq2Asym TreeEq O O))))
thm12_TreeEqLL_at_OO =
  let
    Df_term : Term
    Df_term = ap2 Pair tagCode_axTreeEqLL O

    disp : Deriv (atomic (eqn (ap1 thmT Df_term)
                               (reify (codeFormula
                                 (atomic (eqn (ap2 TreeEq O O) O))))))
    disp = thmTDispAxTreeEqLL_param O

    cor_O : Deriv (atomic (eqn O (ap1 cor O)))
    cor_O = ruleSym (axRecLf O stepCor)

    bL_inner : Deriv (atomic (eqn
                  (ap2 Pair (reify (codeF2 TreeEq))
                    (ap2 Pair O O))
                  (ap2 Pair (reify (codeF2 TreeEq))
                    (ap2 Pair (ap1 cor O) (ap1 cor O)))))
    bL_inner = congR Pair (reify (codeF2 TreeEq))
                 (ruleTrans (congL Pair O cor_O)
                            (congR Pair (ap1 cor O) cor_O))

    bL : Deriv (atomic (eqn
            (mkAp2T (reify (codeF2 TreeEq)) O O)
            (mkAp2T (reify (codeF2 TreeEq)) (ap1 cor O) (ap1 cor O))))
    bL = congR Pair (reify tagAp2) bL_inner

    bR_combined : Deriv (atomic (eqn (ap1 cor (ap2 TreeEq O O)) O))
    bR_combined = ruleTrans (cong1 cor axTreeEqLL) (axRecLf O stepCor)

    bR : Deriv (atomic (eqn O (ap1 cor (ap2 TreeEq O O))))
    bR = ruleSym bR_combined

    step1 : Deriv (atomic (eqn
              (ap2 Pair (mkAp2T (reify (codeF2 TreeEq)) O O) O)
              (ap2 Pair (mkAp2T (reify (codeF2 TreeEq)) (ap1 cor O) (ap1 cor O)) O)))
    step1 = congL Pair O bL

    step2 : Deriv (atomic (eqn
              (ap2 Pair (mkAp2T (reify (codeF2 TreeEq)) (ap1 cor O) (ap1 cor O)) O)
              (ap2 Pair (mkAp2T (reify (codeF2 TreeEq)) (ap1 cor O) (ap1 cor O))
                         (ap1 cor (ap2 TreeEq O O)))))
    step2 = congR Pair (mkAp2T (reify (codeF2 TreeEq)) (ap1 cor O) (ap1 cor O)) bR

    bridge : Deriv (atomic (eqn
                (reify (codeFormula (atomic (eqn (ap2 TreeEq O O) O))))
                (codeFTeq2Asym TreeEq O O)))
    bridge = ruleTrans step1 step2

    pf_final : Deriv (atomic (eqn (ap1 thmT Df_term)
                                   (codeFTeq2Asym TreeEq O O)))
    pf_final = ruleTrans disp bridge

  in mkSigma Df_term pf_final

------------------------------------------------------------------------
-- thm12_Pair_param : Theorem 12 for g = Pair (Fun2) at variables v1, v2.
-- The encoded equation reduces to reflexivity via cor's axRecNd
-- (cor (Pair v1 v2) = mkAp2T pairCodeF2T (cor v1) (cor v2)).

module PairCase (v1 v2 : Nat) where

  thm12_Pair_param :
    Sigma Term (\ Df_term ->
      Deriv (atomic (eqn (ap1 thmT Df_term)
                          (codeFTeq2Asym Pair (var v1) (var v2)))))
  thm12_Pair_param =
    let
      v1T : Term
      v1T = var v1

      v2T : Term
      v2T = var v2

      pairT : Term
      pairT = ap2 Pair v1T v2T

      -- LHS subterm of the asymmetric encoded equation:
      --   mkAp2T (codeF2 Pair) (cor v1) (cor v2)
      lhsSub : Term
      lhsSub = mkAp2T (reify (codeF2 Pair)) (ap1 cor v1T) (ap1 cor v2T)

      -- thmTDispAxRefl_param at xT = lhsSub gives:
      --   thmT (Pair tagCode_axRefl lhsSub) = ap2 Pair lhsSub lhsSub.

      Df_term : Term
      Df_term = ap2 Pair tagCode_axRefl lhsSub

      disp : Deriv (atomic (eqn (ap1 thmT Df_term)
                                 (ap2 Pair lhsSub lhsSub)))
      disp = thmTDispAxRefl_param lhsSub

      -- Bridge:  ap2 Pair lhsSub lhsSub  ->  codeFTeq2Asym Pair v1 v2 .
      -- Need RHS subterm:  lhsSub  ->  cor (Pair v1 v2) .
      -- By cor's axRecNd + stepCorRed:  cor (Pair v1 v2) = lhsSub.

      cor_red_pair : Deriv (atomic (eqn (ap1 cor pairT) lhsSub))
      cor_red_pair =
        let recs = ap2 Pair (ap1 cor v1T) (ap1 cor v2T)
            axNd = axRecNd O stepCor v1T v2T
            stRed = stepCorRed pairT recs
        in ruleTrans axNd stRed

      bR : Deriv (atomic (eqn lhsSub (ap1 cor pairT)))
      bR = ruleSym cor_red_pair

      bridge : Deriv (atomic (eqn (ap2 Pair lhsSub lhsSub)
                                   (codeFTeq2Asym Pair v1T v2T)))
      bridge = congR Pair lhsSub bR

      pf_final : Deriv (atomic (eqn (ap1 thmT Df_term)
                                     (codeFTeq2Asym Pair v1T v2T)))
      pf_final = ruleTrans disp bridge

    in mkSigma Df_term pf_final

------------------------------------------------------------------------
-- thm12_IfLfNL_pair_O : Theorem 12 for g = IfLf at IfLf (Pair v1 v2) O.

module IfLfNLCase (v1 v2 : Nat) where

  thm12_IfLfNL_pair_O :
    Sigma Term (\ Df_term ->
      Deriv (atomic (eqn (ap1 thmT Df_term)
                          (codeFTeq2Asym IfLf (ap2 Pair (var v1) (var v2)) O))))
  thm12_IfLfNL_pair_O =
    let
      v1T : Term
      v1T = var v1

      v2T : Term
      v2T = var v2

      pairT : Term
      pairT = ap2 Pair v1T v2T

      Df_term : Term
      Df_term = ap2 Pair tagCode_axIfLfNL
                    (ap2 Pair (ap1 cor v1T) (ap1 cor v2T))

      disp : Deriv (atomic (eqn
              (ap1 thmT Df_term)
              (ap2 Pair
                (ap2 Pair (reify tagAp2)
                  (ap2 Pair (reify (codeF2 IfLf))
                    (ap2 Pair (ap2 Pair (reify tagAp2)
                                        (ap2 Pair (reify (codeF2 Pair))
                                                   (ap2 Pair (ap1 cor v1T)
                                                              (ap1 cor v2T))))
                              O)))
                O)))
      disp = thmTDispAxIfLfNL_param (ap1 cor v1T) (ap1 cor v2T)

      cor_red_pair : Deriv (atomic (eqn (ap1 cor pairT)
                              (ap2 Pair (reify tagAp2)
                                (ap2 Pair (reify (codeF2 Pair))
                                  (ap2 Pair (ap1 cor v1T) (ap1 cor v2T))))))
      cor_red_pair =
        let recs = ap2 Pair (ap1 cor v1T) (ap1 cor v2T)
            axNd = axRecNd O stepCor v1T v2T
            stRed = stepCorRed pairT recs
        in ruleTrans axNd stRed

      cor_O : Deriv (atomic (eqn O (ap1 cor O)))
      cor_O = ruleSym (axRecLf O stepCor)

      -- LHS subterm bridge to mkAp2T (codeF2 IfLf) (cor (Pair v1 v2)) (cor O).
      bL_innermost : Deriv (atomic (eqn
                  (ap2 Pair (ap2 Pair (reify tagAp2)
                                      (ap2 Pair (reify (codeF2 Pair))
                                                 (ap2 Pair (ap1 cor v1T)
                                                            (ap1 cor v2T))))
                            O)
                  (ap2 Pair (ap1 cor pairT) (ap1 cor O))))
      bL_innermost = ruleTrans
        (congL Pair O (ruleSym cor_red_pair))
        (congR Pair (ap1 cor pairT) cor_O)

      bL_inner : Deriv (atomic (eqn
                          (ap2 Pair (reify (codeF2 IfLf))
                            (ap2 Pair (ap2 Pair (reify tagAp2)
                                                (ap2 Pair (reify (codeF2 Pair))
                                                          (ap2 Pair (ap1 cor v1T)
                                                                    (ap1 cor v2T))))
                                      O))
                          (ap2 Pair (reify (codeF2 IfLf))
                            (ap2 Pair (ap1 cor pairT) (ap1 cor O)))))
      bL_inner = congR Pair (reify (codeF2 IfLf)) bL_innermost

      bL : Deriv (atomic (eqn
                    (ap2 Pair (reify tagAp2)
                      (ap2 Pair (reify (codeF2 IfLf))
                        (ap2 Pair (ap2 Pair (reify tagAp2)
                                            (ap2 Pair (reify (codeF2 Pair))
                                                       (ap2 Pair (ap1 cor v1T)
                                                                  (ap1 cor v2T))))
                                  O)))
                    (mkAp2T (reify (codeF2 IfLf)) (ap1 cor pairT) (ap1 cor O))))
      bL = congR Pair (reify tagAp2) bL_inner

      -- RHS subterm bridge:  O  ->  cor (IfLf (Pair v1 v2) O).
      bR_combined : Deriv (atomic (eqn (ap1 cor (ap2 IfLf pairT O)) O))
      bR_combined = ruleTrans (cong1 cor (axIfLfNL v1T v2T)) (axRecLf O stepCor)

      bR : Deriv (atomic (eqn O (ap1 cor (ap2 IfLf pairT O))))
      bR = ruleSym bR_combined

      step_LHS : Deriv (atomic (eqn
                  (ap2 Pair
                    (ap2 Pair (reify tagAp2)
                      (ap2 Pair (reify (codeF2 IfLf))
                        (ap2 Pair (ap2 Pair (reify tagAp2)
                                            (ap2 Pair (reify (codeF2 Pair))
                                                       (ap2 Pair (ap1 cor v1T)
                                                                  (ap1 cor v2T))))
                                  O)))
                    O)
                  (ap2 Pair
                    (mkAp2T (reify (codeF2 IfLf)) (ap1 cor pairT) (ap1 cor O))
                    O)))
      step_LHS = congL Pair O bL

      step_RHS : Deriv (atomic (eqn
                  (ap2 Pair
                    (mkAp2T (reify (codeF2 IfLf)) (ap1 cor pairT) (ap1 cor O))
                    O)
                  (ap2 Pair
                    (mkAp2T (reify (codeF2 IfLf)) (ap1 cor pairT) (ap1 cor O))
                    (ap1 cor (ap2 IfLf pairT O)))))
      step_RHS = congR Pair
                   (mkAp2T (reify (codeF2 IfLf)) (ap1 cor pairT) (ap1 cor O))
                   bR

      bridge_total : Deriv (atomic (eqn
                  (ap2 Pair
                    (ap2 Pair (reify tagAp2)
                      (ap2 Pair (reify (codeF2 IfLf))
                        (ap2 Pair (ap2 Pair (reify tagAp2)
                                            (ap2 Pair (reify (codeF2 Pair))
                                                       (ap2 Pair (ap1 cor v1T)
                                                                  (ap1 cor v2T))))
                                  O)))
                    O)
                  (codeFTeq2Asym IfLf pairT O)))
      bridge_total = ruleTrans step_LHS step_RHS

      pf_final : Deriv (atomic (eqn (ap1 thmT Df_term)
                                     (codeFTeq2Asym IfLf pairT O)))
      pf_final = ruleTrans disp bridge_total

    in mkSigma Df_term pf_final

------------------------------------------------------------------------
-- thm12_IfLfN_pair_pair : Theorem 12 for g = IfLf at Pair-Pair shape.
-- IfLf (Pair v1 v2) (Pair v3 v4) = v4 (axIfLfN).

module IfLfNCase (v1 v2 v3 v4 : Nat) where

  thm12_IfLfN_pair_pair :
    Sigma Term (\ Df_term ->
      Deriv (atomic (eqn (ap1 thmT Df_term)
                          (codeFTeq2Asym IfLf
                            (ap2 Pair (var v1) (var v2))
                            (ap2 Pair (var v3) (var v4))))))
  thm12_IfLfN_pair_pair =
    let
      v1T = var v1
      v2T = var v2
      v3T = var v3
      v4T = var v4

      pair12 = ap2 Pair v1T v2T
      pair34 = ap2 Pair v3T v4T

      Df_term : Term
      Df_term = ap2 Pair tagCode_axIfLfN
                    (ap2 Pair (ap1 cor v1T)
                      (ap2 Pair (ap1 cor v2T)
                        (ap2 Pair (ap1 cor v3T) (ap1 cor v4T))))

      disp = thmTDispAxIfLfN_param (ap1 cor v1T) (ap1 cor v2T)
                                    (ap1 cor v3T) (ap1 cor v4T)

      -- cor (Pair v1 v2) reduction.
      cor_red_pairAB : Deriv (atomic (eqn (ap1 cor pair12)
                            (ap2 Pair (reify tagAp2)
                              (ap2 Pair (reify (codeF2 Pair))
                                (ap2 Pair (ap1 cor v1T) (ap1 cor v2T))))))
      cor_red_pairAB =
        let recs = ap2 Pair (ap1 cor v1T) (ap1 cor v2T)
        in ruleTrans (axRecNd O stepCor v1T v2T) (stepCorRed pair12 recs)

      -- cor (Pair v3 v4) reduction.
      cor_red_pairCD : Deriv (atomic (eqn (ap1 cor pair34)
                            (ap2 Pair (reify tagAp2)
                              (ap2 Pair (reify (codeF2 Pair))
                                (ap2 Pair (ap1 cor v3T) (ap1 cor v4T))))))
      cor_red_pairCD =
        let recs = ap2 Pair (ap1 cor v3T) (ap1 cor v4T)
        in ruleTrans (axRecNd O stepCor v3T v4T) (stepCorRed pair34 recs)

      -- LHS subterm bridge:  the inner pair structure  ->  cor pair12, cor pair34.
      bL_innermost : Deriv (atomic (eqn
                  (ap2 Pair (ap2 Pair (reify tagAp2)
                                      (ap2 Pair (reify (codeF2 Pair))
                                                 (ap2 Pair (ap1 cor v1T)
                                                            (ap1 cor v2T))))
                            (ap2 Pair (reify tagAp2)
                                      (ap2 Pair (reify (codeF2 Pair))
                                                 (ap2 Pair (ap1 cor v3T)
                                                            (ap1 cor v4T)))))
                  (ap2 Pair (ap1 cor pair12) (ap1 cor pair34))))
      bL_innermost = ruleTrans
        (congL Pair (ap2 Pair (reify tagAp2)
                              (ap2 Pair (reify (codeF2 Pair))
                                (ap2 Pair (ap1 cor v3T) (ap1 cor v4T))))
                    (ruleSym cor_red_pairAB))
        (congR Pair (ap1 cor pair12) (ruleSym cor_red_pairCD))

      bL_inner : Deriv (atomic (eqn
                          (ap2 Pair (reify (codeF2 IfLf))
                            (ap2 Pair (ap2 Pair (reify tagAp2)
                                                (ap2 Pair (reify (codeF2 Pair))
                                                          (ap2 Pair (ap1 cor v1T)
                                                                    (ap1 cor v2T))))
                                      (ap2 Pair (reify tagAp2)
                                                (ap2 Pair (reify (codeF2 Pair))
                                                          (ap2 Pair (ap1 cor v3T)
                                                                    (ap1 cor v4T))))))
                          (ap2 Pair (reify (codeF2 IfLf))
                            (ap2 Pair (ap1 cor pair12) (ap1 cor pair34)))))
      bL_inner = congR Pair (reify (codeF2 IfLf)) bL_innermost

      bL : Deriv (atomic (eqn
                    (ap2 Pair (reify tagAp2)
                      (ap2 Pair (reify (codeF2 IfLf))
                        (ap2 Pair (ap2 Pair (reify tagAp2)
                                            (ap2 Pair (reify (codeF2 Pair))
                                                       (ap2 Pair (ap1 cor v1T)
                                                                  (ap1 cor v2T))))
                                  (ap2 Pair (reify tagAp2)
                                            (ap2 Pair (reify (codeF2 Pair))
                                                       (ap2 Pair (ap1 cor v3T)
                                                                  (ap1 cor v4T)))))))
                    (mkAp2T (reify (codeF2 IfLf)) (ap1 cor pair12) (ap1 cor pair34))))
      bL = congR Pair (reify tagAp2) bL_inner

      -- RHS bridge: cor v4 -> cor (IfLf (Pair v1 v2) (Pair v3 v4)).
      bR : Deriv (atomic (eqn (ap1 cor v4T)
                               (ap1 cor (ap2 IfLf pair12 pair34))))
      bR = ruleSym (cong1 cor (axIfLfN v1T v2T v3T v4T))

      step_LHS = congL Pair (ap1 cor v4T) bL
      step_RHS = congR Pair
                   (mkAp2T (reify (codeF2 IfLf)) (ap1 cor pair12) (ap1 cor pair34))
                   bR

      pf_final = ruleTrans disp (ruleTrans step_LHS step_RHS)

    in mkSigma Df_term pf_final

------------------------------------------------------------------------
-- thm12_TreeEqLN_pair : Theorem 12 for TreeEq O (Pair a b).
-- axTreeEqLN: TreeEq O (Pair a b) = Pair O O.

module TreeEqLNCase (v1 v2 : Nat) where

  thm12_TreeEqLN_pair :
    Sigma Term (\ Df_term ->
      Deriv (atomic (eqn (ap1 thmT Df_term)
                          (codeFTeq2Asym TreeEq O (ap2 Pair (var v1) (var v2))))))
  thm12_TreeEqLN_pair =
    let
      v1T = var v1
      v2T = var v2
      pair12 = ap2 Pair v1T v2T

      Df_term : Term
      Df_term = ap2 Pair tagCode_axTreeEqLN
                    (ap2 Pair (ap1 cor v1T) (ap1 cor v2T))

      disp = thmTDispAxTreeEqLN_param (ap1 cor v1T) (ap1 cor v2T)

      cor_red_pairAB : Deriv (atomic (eqn (ap1 cor pair12)
                            (ap2 Pair (reify tagAp2)
                              (ap2 Pair (reify (codeF2 Pair))
                                (ap2 Pair (ap1 cor v1T) (ap1 cor v2T))))))
      cor_red_pairAB =
        let recs = ap2 Pair (ap1 cor v1T) (ap1 cor v2T)
        in ruleTrans (axRecNd O stepCor v1T v2T) (stepCorRed pair12 recs)

      cor_O : Deriv (atomic (eqn O (ap1 cor O)))
      cor_O = ruleSym (axRecLf O stepCor)

      -- LHS bridge:  reach cor O on first slot, cor pair12 on second.
      bL_innermost : Deriv (atomic (eqn
                      (ap2 Pair O
                        (ap2 Pair (reify tagAp2)
                          (ap2 Pair (reify (codeF2 Pair))
                            (ap2 Pair (ap1 cor v1T) (ap1 cor v2T)))))
                      (ap2 Pair (ap1 cor O) (ap1 cor pair12))))
      bL_innermost = ruleTrans
        (congL Pair (ap2 Pair (reify tagAp2)
                              (ap2 Pair (reify (codeF2 Pair))
                                (ap2 Pair (ap1 cor v1T) (ap1 cor v2T))))
                    cor_O)
        (congR Pair (ap1 cor O) (ruleSym cor_red_pairAB))

      bL_inner = congR Pair (reify (codeF2 TreeEq)) bL_innermost

      bL : Deriv (atomic (eqn
                    (ap2 Pair (reify tagAp2)
                      (ap2 Pair (reify (codeF2 TreeEq))
                        (ap2 Pair O
                          (ap2 Pair (reify tagAp2)
                            (ap2 Pair (reify (codeF2 Pair))
                              (ap2 Pair (ap1 cor v1T) (ap1 cor v2T)))))))
                    (mkAp2T (reify (codeF2 TreeEq)) (ap1 cor O) (ap1 cor pair12))))
      bL = congR Pair (reify tagAp2) bL_inner

      -- RHS bridge:  reify (code (Pair O O))  ->  cor (TreeEq O (Pair v1 v2)).
      cor_pair_OO : Deriv (atomic (eqn (ap1 cor (ap2 Pair O O))
                              (reify (code (ap2 Pair O O)))))
      cor_pair_OO = corOfReify (nd lf lf)

      bR_step1 : Deriv (atomic (eqn (reify (code (ap2 Pair O O)))
                                     (ap1 cor (ap2 Pair O O))))
      bR_step1 = ruleSym cor_pair_OO

      bR_step2 : Deriv (atomic (eqn (ap1 cor (ap2 Pair O O))
                                     (ap1 cor (ap2 TreeEq O pair12))))
      bR_step2 = cong1 cor (ruleSym (axTreeEqLN v1T v2T))

      bR : Deriv (atomic (eqn (reify (code (ap2 Pair O O)))
                               (ap1 cor (ap2 TreeEq O pair12))))
      bR = ruleTrans bR_step1 bR_step2

      step_LHS = congL Pair (reify (code (ap2 Pair O O))) bL
      step_RHS = congR Pair
                   (mkAp2T (reify (codeF2 TreeEq)) (ap1 cor O) (ap1 cor pair12))
                   bR

      pf_final = ruleTrans disp (ruleTrans step_LHS step_RHS)

    in mkSigma Df_term pf_final

------------------------------------------------------------------------
-- thm12_TreeEqNL_pair : Theorem 12 for TreeEq (Pair a b) O.
-- axTreeEqNL: TreeEq (Pair a b) O = Pair O O.  Mirror of TreeEqLN.

module TreeEqNLCase (v1 v2 : Nat) where

  thm12_TreeEqNL_pair :
    Sigma Term (\ Df_term ->
      Deriv (atomic (eqn (ap1 thmT Df_term)
                          (codeFTeq2Asym TreeEq (ap2 Pair (var v1) (var v2)) O))))
  thm12_TreeEqNL_pair =
    let
      v1T = var v1
      v2T = var v2
      pair12 = ap2 Pair v1T v2T

      Df_term : Term
      Df_term = ap2 Pair tagCode_axTreeEqNL
                    (ap2 Pair (ap1 cor v1T) (ap1 cor v2T))

      disp = thmTDispAxTreeEqNL_param (ap1 cor v1T) (ap1 cor v2T)

      cor_red_pairAB : Deriv (atomic (eqn (ap1 cor pair12)
                            (ap2 Pair (reify tagAp2)
                              (ap2 Pair (reify (codeF2 Pair))
                                (ap2 Pair (ap1 cor v1T) (ap1 cor v2T))))))
      cor_red_pairAB =
        let recs = ap2 Pair (ap1 cor v1T) (ap1 cor v2T)
        in ruleTrans (axRecNd O stepCor v1T v2T) (stepCorRed pair12 recs)

      cor_O : Deriv (atomic (eqn O (ap1 cor O)))
      cor_O = ruleSym (axRecLf O stepCor)

      bL_innermost : Deriv (atomic (eqn
                      (ap2 Pair (ap2 Pair (reify tagAp2)
                                  (ap2 Pair (reify (codeF2 Pair))
                                    (ap2 Pair (ap1 cor v1T) (ap1 cor v2T))))
                                O)
                      (ap2 Pair (ap1 cor pair12) (ap1 cor O))))
      bL_innermost = ruleTrans
        (congL Pair O (ruleSym cor_red_pairAB))
        (congR Pair (ap1 cor pair12) cor_O)

      bL_inner = congR Pair (reify (codeF2 TreeEq)) bL_innermost

      bL : Deriv (atomic (eqn
                    (ap2 Pair (reify tagAp2)
                      (ap2 Pair (reify (codeF2 TreeEq))
                        (ap2 Pair (ap2 Pair (reify tagAp2)
                                    (ap2 Pair (reify (codeF2 Pair))
                                      (ap2 Pair (ap1 cor v1T) (ap1 cor v2T))))
                                  O)))
                    (mkAp2T (reify (codeF2 TreeEq)) (ap1 cor pair12) (ap1 cor O))))
      bL = congR Pair (reify tagAp2) bL_inner

      cor_pair_OO : Deriv (atomic (eqn (ap1 cor (ap2 Pair O O))
                              (reify (code (ap2 Pair O O)))))
      cor_pair_OO = corOfReify (nd lf lf)

      bR_step1 : Deriv (atomic (eqn (reify (code (ap2 Pair O O)))
                                     (ap1 cor (ap2 Pair O O))))
      bR_step1 = ruleSym cor_pair_OO

      bR_step2 : Deriv (atomic (eqn (ap1 cor (ap2 Pair O O))
                                     (ap1 cor (ap2 TreeEq pair12 O))))
      bR_step2 = cong1 cor (ruleSym (axTreeEqNL v1T v2T))

      bR : Deriv (atomic (eqn (reify (code (ap2 Pair O O)))
                               (ap1 cor (ap2 TreeEq pair12 O))))
      bR = ruleTrans bR_step1 bR_step2

      step_LHS = congL Pair (reify (code (ap2 Pair O O))) bL
      step_RHS = congR Pair
                   (mkAp2T (reify (codeF2 TreeEq)) (ap1 cor pair12) (ap1 cor O))
                   bR

      pf_final = ruleTrans disp (ruleTrans step_LHS step_RHS)

    in mkSigma Df_term pf_final
