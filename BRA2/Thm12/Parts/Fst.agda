{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm12.Parts.Fst   (Theorem 12 case for f = Fst).
--
-- Fst is partial: axFst handles ap1 Fst (ap2 Pair a b) = a; the
-- safe-default axFstLf handles ap1 Fst O = O.  Theorem 12 holds
-- for Fst via ruleIndBT (binary-tree induction on x).
--
-- D_Fst : Fun1 dispatches on x via IfLf:
--   ap1 D_Fst O = parEncAxFstLf O    (closed encoding of Fst O = O)
--   ap1 D_Fst (Pair v1 v2) = parEncAxFst (cor v1) (cor v2)
--
-- D_correct_Fst : (x : Term) -> Deriv (eqn (thmT (D_Fst x)) (codeFTeq1_Fst x))
-- Proof: ruleIndBT + ruleInst.

module BRA2.Thm12.Parts.Fst where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Deriv
open import BRA2.Cor
open import BRA2.Thm.Tag using (tagAxFst ; tagAxFstLf)
open import BRA2.Thm.ThmT using (thmT ; tagCode_axFst ; tagCode_axFstLf ; thClosed)
open import BRA2.Thm12.Param.AxFst
  using (parEncAxFst ; parOutAxFst ; parDispAxFst)
open import BRA2.Thm12.Param.AxFstLf
  using (parEncAxFstLf ; parOutAxFstLf ; parDispAxFstLf)

------------------------------------------------------------------------
-- The encoded equation we want to prove:
--
--   thmT(D_Fst x) = encoded (Fst (cor x) = cor (Fst x))
--                 = Pair (Pair tagAp1 (Pair codeF1Fst (cor x))) (cor (Fst x))

codeFTeq1_Fst : Term -> Term
codeFTeq1_Fst x =
  ap2 Pair
    (ap2 Pair (reify tagAp1)
              (ap2 Pair (reify (codeF1 Fst)) (ap1 cor x)))
    (ap1 cor (ap1 Fst x))

------------------------------------------------------------------------
-- The Fun1 D_Fst.  Dispatches on x via IfLf:
--   when x = O:        produces parEncAxFstLf O = ap2 Pair tagCode_axFstLf O
--   when x = Pair v1 v2: produces parEncAxFst (cor v1) (cor v2)
--
-- Built as Comp2 IfLf I dispatchFun where dispatchFun produces the
-- pair (leafBranch , nonleafBranch).

private
  -- ap1 nonleafFun x = Pair tagCode_axFst (Pair (cor (Fst x)) (cor (Snd x)))
  --                  = parEncAxFst (cor (Fst x)) (cor (Snd x))
  nonleafFun : Fun1
  nonleafFun = Comp2 Pair (KT tagCode_axFst)
                  (Comp2 Pair (Comp cor Fst) (Comp cor Snd))

  -- ap1 dispatchFun x = Pair (parEncAxFstLf O) (ap1 nonleafFun x)
  dispatchFun : Fun1
  dispatchFun = Comp2 Pair (KT (parEncAxFstLf O)) nonleafFun

D_Fst : Fun1
D_Fst = Comp2 IfLf I dispatchFun

------------------------------------------------------------------------
-- Combinator reduction at x = O: ap1 D_Fst O = parEncAxFstLf O.

D_Fst_reduce_O : Deriv (atomic (eqn (ap1 D_Fst O) (parEncAxFstLf O)))
D_Fst_reduce_O =
  let -- ap1 (Comp2 IfLf I dispatchFun) O = ap2 IfLf (ap1 I O) (ap1 dispatchFun O)
      s1 : Deriv (atomic (eqn (ap1 D_Fst O)
                              (ap2 IfLf (ap1 I O) (ap1 dispatchFun O))))
      s1 = axComp2 IfLf I dispatchFun O

      -- ap1 I O = O
      s2 : Deriv (atomic (eqn (ap1 I O) O))
      s2 = axI O

      -- Rewrite the LEFT slot of IfLf to O.
      s3 : Deriv (atomic (eqn (ap2 IfLf (ap1 I O) (ap1 dispatchFun O))
                              (ap2 IfLf O (ap1 dispatchFun O))))
      s3 = congL IfLf (ap1 dispatchFun O) s2

      -- ap1 dispatchFun O = ap2 Pair (ap1 (KT (parEncAxFstLf O)) O) (ap1 nonleafFun O)
      d1 : Deriv (atomic (eqn (ap1 dispatchFun O)
                              (ap2 Pair (ap1 (KT (parEncAxFstLf O)) O)
                                        (ap1 nonleafFun O))))
      d1 = axComp2 Pair (KT (parEncAxFstLf O)) nonleafFun O

      -- ap1 (KT (parEncAxFstLf O)) O = parEncAxFstLf O.
      -- parEncAxFstLf O = ap2 Pair tagCode_axFstLf O = reify (nd (natCode tagAxFstLf) lf).
      d2 : Deriv (atomic (eqn (ap1 (KT (parEncAxFstLf O)) O) (parEncAxFstLf O)))
      d2 = axKT (nd (natCode tagAxFstLf) lf) (valNd (natCode tagAxFstLf) lf (natCode_isValue tagAxFstLf) valO) O

      -- Combine: ap1 dispatchFun O = ap2 Pair (parEncAxFstLf O) (ap1 nonleafFun O)
      d_final : Deriv (atomic (eqn (ap1 dispatchFun O)
                                   (ap2 Pair (parEncAxFstLf O) (ap1 nonleafFun O))))
      d_final = ruleTrans d1 (congL Pair (ap1 nonleafFun O) d2)

      -- Rewrite the RIGHT slot of IfLf via d_final.
      s4 : Deriv (atomic (eqn (ap2 IfLf O (ap1 dispatchFun O))
                              (ap2 IfLf O (ap2 Pair (parEncAxFstLf O)
                                                    (ap1 nonleafFun O)))))
      s4 = congR IfLf O d_final

      -- axIfLfL: ap2 IfLf O (ap2 Pair a b) = a.
      s5 : Deriv (atomic (eqn (ap2 IfLf O (ap2 Pair (parEncAxFstLf O)
                                                    (ap1 nonleafFun O)))
                              (parEncAxFstLf O)))
      s5 = axIfLfL (parEncAxFstLf O) (ap1 nonleafFun O)
  in ruleTrans s1 (ruleTrans s3 (ruleTrans s4 s5))

------------------------------------------------------------------------
-- Combinator reduction at x = Pair v1 v2: ap1 D_Fst (Pair v1 v2) reduces
-- (via combinator + axFst, axSnd) to parEncAxFst (cor v1) (cor v2).

D_Fst_reduce_Pair : (v1 v2 : Term) ->
  Deriv (atomic (eqn (ap1 D_Fst (ap2 Pair v1 v2))
                     (parEncAxFst (ap1 cor v1) (ap1 cor v2))))
D_Fst_reduce_Pair v1 v2 =
  let pv : Term
      pv = ap2 Pair v1 v2

      -- ap1 D_Fst pv = ap2 IfLf (ap1 I pv) (ap1 dispatchFun pv)
      s1 : Deriv (atomic (eqn (ap1 D_Fst pv)
                              (ap2 IfLf (ap1 I pv) (ap1 dispatchFun pv))))
      s1 = axComp2 IfLf I dispatchFun pv

      -- ap1 I pv = pv
      s2 : Deriv (atomic (eqn (ap1 I pv) pv))
      s2 = axI pv

      -- Rewrite LEFT slot of IfLf.
      s3 : Deriv (atomic (eqn (ap2 IfLf (ap1 I pv) (ap1 dispatchFun pv))
                              (ap2 IfLf pv (ap1 dispatchFun pv))))
      s3 = congL IfLf (ap1 dispatchFun pv) s2

      -- ap1 dispatchFun pv = ap2 Pair (parEncAxFstLf O) (ap1 nonleafFun pv)
      d1 : Deriv (atomic (eqn (ap1 dispatchFun pv)
                              (ap2 Pair (ap1 (KT (parEncAxFstLf O)) pv)
                                        (ap1 nonleafFun pv))))
      d1 = axComp2 Pair (KT (parEncAxFstLf O)) nonleafFun pv

      d2 : Deriv (atomic (eqn (ap1 (KT (parEncAxFstLf O)) pv) (parEncAxFstLf O)))
      d2 = axKT (nd (natCode tagAxFstLf) lf) (valNd (natCode tagAxFstLf) lf (natCode_isValue tagAxFstLf) valO) pv

      d_kt : Deriv (atomic (eqn (ap1 dispatchFun pv)
                                (ap2 Pair (parEncAxFstLf O) (ap1 nonleafFun pv))))
      d_kt = ruleTrans d1 (congL Pair (ap1 nonleafFun pv) d2)

      -- Now we need ap1 nonleafFun pv = parEncAxFst (cor v1) (cor v2).
      -- nonleafFun = Comp2 Pair (KT tagCode_axFst) (Comp2 Pair (Comp cor Fst) (Comp cor Snd))

      -- ap1 nonleafFun pv = ap2 Pair (ap1 (KT tagCode_axFst) pv)
      --                              (ap1 (Comp2 Pair (Comp cor Fst) (Comp cor Snd)) pv)
      n1 : Deriv (atomic (eqn (ap1 nonleafFun pv)
                              (ap2 Pair (ap1 (KT tagCode_axFst) pv)
                                        (ap1 (Comp2 Pair (Comp cor Fst) (Comp cor Snd)) pv))))
      n1 = axComp2 Pair (KT tagCode_axFst)
                   (Comp2 Pair (Comp cor Fst) (Comp cor Snd)) pv

      n2 : Deriv (atomic (eqn (ap1 (KT tagCode_axFst) pv) tagCode_axFst))
      n2 = axKT (natCode (suc (suc zero))) (natCode_isValue (suc (suc zero))) pv  -- tagAxFst = 2

      -- ap1 (Comp2 Pair (Comp cor Fst) (Comp cor Snd)) pv
      --   = ap2 Pair (ap1 (Comp cor Fst) pv) (ap1 (Comp cor Snd) pv)
      --   = ap2 Pair (cor (Fst pv)) (cor (Snd pv))
      --   = ap2 Pair (cor v1) (cor v2)   (using axFst, axSnd, cong cor)
      n3a : Deriv (atomic (eqn (ap1 (Comp2 Pair (Comp cor Fst) (Comp cor Snd)) pv)
                               (ap2 Pair (ap1 (Comp cor Fst) pv)
                                         (ap1 (Comp cor Snd) pv))))
      n3a = axComp2 Pair (Comp cor Fst) (Comp cor Snd) pv

      n3b : Deriv (atomic (eqn (ap1 (Comp cor Fst) pv) (ap1 cor (ap1 Fst pv))))
      n3b = axComp cor Fst pv

      n3c : Deriv (atomic (eqn (ap1 cor (ap1 Fst pv)) (ap1 cor v1)))
      n3c = cong1 cor (axFst v1 v2)

      n3 : Deriv (atomic (eqn (ap1 (Comp cor Fst) pv) (ap1 cor v1)))
      n3 = ruleTrans n3b n3c

      n4b : Deriv (atomic (eqn (ap1 (Comp cor Snd) pv) (ap1 cor (ap1 Snd pv))))
      n4b = axComp cor Snd pv

      n4c : Deriv (atomic (eqn (ap1 cor (ap1 Snd pv)) (ap1 cor v2)))
      n4c = cong1 cor (axSnd v1 v2)

      n4 : Deriv (atomic (eqn (ap1 (Comp cor Snd) pv) (ap1 cor v2)))
      n4 = ruleTrans n4b n4c

      n5 : Deriv (atomic (eqn (ap2 Pair (ap1 (Comp cor Fst) pv)
                                         (ap1 (Comp cor Snd) pv))
                              (ap2 Pair (ap1 cor v1) (ap1 cor v2))))
      n5 = ruleTrans (congL Pair (ap1 (Comp cor Snd) pv) n3)
                     (congR Pair (ap1 cor v1) n4)

      n6 : Deriv (atomic (eqn (ap1 (Comp2 Pair (Comp cor Fst) (Comp cor Snd)) pv)
                              (ap2 Pair (ap1 cor v1) (ap1 cor v2))))
      n6 = ruleTrans n3a n5

      -- Combine: ap1 nonleafFun pv = parEncAxFst (cor v1) (cor v2)
      n_final : Deriv (atomic (eqn (ap1 nonleafFun pv)
                                   (ap2 Pair tagCode_axFst
                                             (ap2 Pair (ap1 cor v1) (ap1 cor v2)))))
      n_final = ruleTrans n1
                  (ruleTrans (congL Pair _ n2)
                             (congR Pair tagCode_axFst n6))

      -- Rewrite RIGHT slot of (the inner) Pair in dispatchFun's result.
      d_step : Deriv (atomic (eqn (ap1 dispatchFun pv)
                                  (ap2 Pair (parEncAxFstLf O)
                                            (parEncAxFst (ap1 cor v1) (ap1 cor v2)))))
      d_step = ruleTrans d_kt
                 (congR Pair (parEncAxFstLf O) n_final)

      -- Rewrite RIGHT slot of IfLf.
      s4 : Deriv (atomic (eqn (ap2 IfLf pv (ap1 dispatchFun pv))
                              (ap2 IfLf pv (ap2 Pair (parEncAxFstLf O)
                                                     (parEncAxFst (ap1 cor v1) (ap1 cor v2))))))
      s4 = congR IfLf pv d_step

      -- axIfLfN: ap2 IfLf (Pair v1 v2) (Pair a b) = b.
      s5 : Deriv (atomic (eqn (ap2 IfLf pv (ap2 Pair (parEncAxFstLf O)
                                                     (parEncAxFst (ap1 cor v1) (ap1 cor v2))))
                              (parEncAxFst (ap1 cor v1) (ap1 cor v2))))
      s5 = axIfLfN v1 v2 (parEncAxFstLf O) (parEncAxFst (ap1 cor v1) (ap1 cor v2))
  in ruleTrans s1 (ruleTrans s3 (ruleTrans s4 s5))

------------------------------------------------------------------------
-- Bridges: relate parOutAxFstLf and parOutAxFst (cor v1) (cor v2) to the
-- target codeFTeq1_Fst at O and Pair v1 v2.

-- Bridge at base case: parOutAxFstLf -> codeFTeq1_Fst O.
--
-- parOutAxFstLf = reify outAxFstLf
--   = ap2 Pair (ap2 Pair (reify tagAp1) (ap2 Pair (reify (codeF1 Fst)) O)) O
--
-- codeFTeq1_Fst O
--   = ap2 Pair (ap2 Pair (reify tagAp1) (ap2 Pair (reify (codeF1 Fst)) (ap1 cor O)))
--              (ap1 cor (ap1 Fst O))
--
-- Bridge: rewrite O -> ap1 cor O via ruleSym (axRecLf stepCor) inside the
-- Fst-LHS slot, and O -> ap1 cor (ap1 Fst O) via ruleSym
-- (cor (Fst O) = cor O = O).

bridgeBase : Deriv (atomic (eqn parOutAxFstLf (codeFTeq1_Fst O)))
bridgeBase =
  let -- cor O = O
      cor_O : Deriv (atomic (eqn (ap1 cor O) O))
      cor_O = axRecLf stepCor

      -- ap1 Fst O = O
      fst_O : Deriv (atomic (eqn (ap1 Fst O) O))
      fst_O = axFstLf

      -- cor (ap1 Fst O) = cor O
      cor_fst_O_to_cor_O : Deriv (atomic (eqn (ap1 cor (ap1 Fst O)) (ap1 cor O)))
      cor_fst_O_to_cor_O = cong1 cor fst_O

      -- cor (ap1 Fst O) = O
      cor_fst_O : Deriv (atomic (eqn (ap1 cor (ap1 Fst O)) O))
      cor_fst_O = ruleTrans cor_fst_O_to_cor_O cor_O

      -- Inner LHS: rewrite O -> cor O.
      -- Goal LHS slot of inner Pair: (ap2 Pair (reify (codeF1 Fst)) (ap1 cor O))
      -- Currently: (ap2 Pair (reify (codeF1 Fst)) O)
      step_inner : Deriv (atomic (eqn
                          (ap2 Pair (reify (codeF1 Fst)) O)
                          (ap2 Pair (reify (codeF1 Fst)) (ap1 cor O))))
      step_inner = congR Pair (reify (codeF1 Fst)) (ruleSym cor_O)

      -- Outer LHS: ap2 Pair (reify tagAp1) (...)
      step_outer : Deriv (atomic (eqn
                          (ap2 Pair (reify tagAp1) (ap2 Pair (reify (codeF1 Fst)) O))
                          (ap2 Pair (reify tagAp1) (ap2 Pair (reify (codeF1 Fst)) (ap1 cor O)))))
      step_outer = congR Pair (reify tagAp1) step_inner

      -- Top Pair LHS slot rewrite.
      step_lhs : Deriv (atomic (eqn
                          (ap2 Pair (ap2 Pair (reify tagAp1) (ap2 Pair (reify (codeF1 Fst)) O)) O)
                          (ap2 Pair (ap2 Pair (reify tagAp1) (ap2 Pair (reify (codeF1 Fst)) (ap1 cor O))) O)))
      step_lhs = congL Pair O step_outer

      -- Top Pair RHS slot rewrite: O -> cor (Fst O).
      step_rhs : Deriv (atomic (eqn
                          (ap2 Pair (ap2 Pair (reify tagAp1) (ap2 Pair (reify (codeF1 Fst)) (ap1 cor O))) O)
                          (ap2 Pair (ap2 Pair (reify tagAp1) (ap2 Pair (reify (codeF1 Fst)) (ap1 cor O))) (ap1 cor (ap1 Fst O)))))
      step_rhs = congR Pair _ (ruleSym cor_fst_O)
  in ruleTrans step_lhs step_rhs

-- Bridge at step case: parOutAxFst (cor v1) (cor v2) -> codeFTeq1_Fst (Pair v1 v2).
--
-- parOutAxFst (cor v1) (cor v2) =
--   Pair (Pair tagAp1 (Pair codeF1Fst (Pair tagAp2 (Pair codeF2Pair (Pair (cor v1) (cor v2))))))
--        (cor v1)
--
-- codeFTeq1_Fst (Pair v1 v2) =
--   Pair (Pair tagAp1 (Pair codeF1Fst (cor (Pair v1 v2)))) (cor (Fst (Pair v1 v2)))
--
-- Bridge:
--   LHS slot: rewrite Pair tagAp2 (Pair codeF2Pair (Pair (cor v1) (cor v2))) -> cor (Pair v1 v2)
--             via ruleSym corPairUnfold.
--   RHS slot: rewrite (cor v1) -> cor (Fst (Pair v1 v2)) via ruleSym (cong1 cor (axFst v1 v2)).

bridgeStep : (v1 v2 : Term) ->
  Deriv (atomic (eqn (parOutAxFst (ap1 cor v1) (ap1 cor v2))
                     (codeFTeq1_Fst (ap2 Pair v1 v2))))
bridgeStep v1 v2 =
  let -- corPairUnfold: cor (Pair v1 v2) = Pair tagAp2 (Pair codeF2Pair (Pair (cor v1) (cor v2)))
      cor_pair_unfold : Deriv (atomic (eqn (ap1 cor (ap2 Pair v1 v2))
                                           (ap2 Pair (reify tagAp2)
                                                     (ap2 Pair (reify (codeF2 Pair))
                                                               (ap2 Pair (ap1 cor v1) (ap1 cor v2))))))
      cor_pair_unfold =
        let recs = ap2 Pair (ap1 cor v1) (ap1 cor v2)
            orig = ap2 Pair v1 v2
            origW = ap2 Pair O orig
            r1 : Deriv (atomic (eqn (ap1 cor orig) (ap2 stepCor origW recs)))
            r1 = axRecNd stepCor v1 v2
            r2 : Deriv (atomic (eqn (ap2 stepCor origW recs)
                                    (ap2 Pair (reify tagAp2) (ap2 Pair (reify (codeF2 Pair)) recs))))
            r2 = stepCorRed origW recs
        in ruleTrans r1 r2

      -- cor (Fst (Pair v1 v2)) = cor v1.
      cor_fst_pair : Deriv (atomic (eqn (ap1 cor (ap1 Fst (ap2 Pair v1 v2))) (ap1 cor v1)))
      cor_fst_pair = cong1 cor (axFst v1 v2)

      -- LHS slot rewrite:
      --   Pair tagAp2 (Pair codeF2Pair (Pair (cor v1) (cor v2)))
      --   -> cor (Pair v1 v2)
      lhs_inner : Deriv (atomic (eqn
                          (ap2 Pair (reify tagAp2)
                            (ap2 Pair (reify (codeF2 Pair)) (ap2 Pair (ap1 cor v1) (ap1 cor v2))))
                          (ap1 cor (ap2 Pair v1 v2))))
      lhs_inner = ruleSym cor_pair_unfold

      lhs_step : Deriv (atomic (eqn
                          (ap2 Pair (reify (codeF1 Fst))
                            (ap2 Pair (reify tagAp2)
                              (ap2 Pair (reify (codeF2 Pair)) (ap2 Pair (ap1 cor v1) (ap1 cor v2)))))
                          (ap2 Pair (reify (codeF1 Fst)) (ap1 cor (ap2 Pair v1 v2)))))
      lhs_step = congR Pair (reify (codeF1 Fst)) lhs_inner

      lhs_outer : Deriv (atomic (eqn
                          (ap2 Pair (reify tagAp1)
                            (ap2 Pair (reify (codeF1 Fst))
                              (ap2 Pair (reify tagAp2)
                                (ap2 Pair (reify (codeF2 Pair))
                                  (ap2 Pair (ap1 cor v1) (ap1 cor v2))))))
                          (ap2 Pair (reify tagAp1)
                            (ap2 Pair (reify (codeF1 Fst)) (ap1 cor (ap2 Pair v1 v2))))))
      lhs_outer = congR Pair (reify tagAp1) lhs_step

      step_lhs : Deriv (atomic (eqn (parOutAxFst (ap1 cor v1) (ap1 cor v2))
                                    (ap2 Pair
                                      (ap2 Pair (reify tagAp1)
                                        (ap2 Pair (reify (codeF1 Fst))
                                          (ap1 cor (ap2 Pair v1 v2))))
                                      (ap1 cor v1))))
      step_lhs = congL Pair (ap1 cor v1) lhs_outer

      -- RHS slot rewrite: (cor v1) -> cor (Fst (Pair v1 v2)).
      step_rhs : Deriv (atomic (eqn
                          (ap2 Pair
                            (ap2 Pair (reify tagAp1)
                              (ap2 Pair (reify (codeF1 Fst)) (ap1 cor (ap2 Pair v1 v2))))
                            (ap1 cor v1))
                          (codeFTeq1_Fst (ap2 Pair v1 v2))))
      step_rhs = congR Pair _ (ruleSym cor_fst_pair)
  in ruleTrans step_lhs step_rhs

------------------------------------------------------------------------
-- Pointwise correctness at base and step.

D_correct_Fst_base : Deriv (atomic (eqn (ap1 thmT (ap1 D_Fst O)) (codeFTeq1_Fst O)))
D_correct_Fst_base =
  let r_thmT : Deriv (atomic (eqn (ap1 thmT (ap1 D_Fst O))
                                  (ap1 thmT (parEncAxFstLf O))))
      r_thmT = cong1 thmT D_Fst_reduce_O
      r_disp = parDispAxFstLf O
  in ruleTrans r_thmT (ruleTrans r_disp bridgeBase)

D_correct_Fst_step : (v1 v2 : Term) ->
  Deriv (atomic (eqn (ap1 thmT (ap1 D_Fst (ap2 Pair v1 v2))) (codeFTeq1_Fst (ap2 Pair v1 v2))))
D_correct_Fst_step v1 v2 =
  let r_thmT : Deriv (atomic (eqn (ap1 thmT (ap1 D_Fst (ap2 Pair v1 v2)))
                                  (ap1 thmT (parEncAxFst (ap1 cor v1) (ap1 cor v2)))))
      r_thmT = cong1 thmT (D_Fst_reduce_Pair v1 v2)
      r_disp = parDispAxFst (ap1 cor v1) (ap1 cor v2)
      r_bridge = bridgeStep v1 v2
  in ruleTrans r_thmT (ruleTrans r_disp r_bridge)

------------------------------------------------------------------------
-- Universal proof via ruleIndBT + specialization via ruleInst.
-- Choose v1 = 1, v2 = 2 as fresh BRA variables (var 0 is the inducting var).

private
  v1Nat : Nat
  v1Nat = suc zero
  v2Nat : Nat
  v2Nat = suc (suc zero)

  P_Fst : Formula
  P_Fst = atomic (eqn (ap1 thmT (ap1 D_Fst (var zero))) (codeFTeq1_Fst (var zero)))

  -- substF zero O P_Fst evaluates to atomic (eqn (ap1 (substF1 zero O thmT) (ap1 D_Fst O)) (codeFTeq1_Fst O))
  -- because thmT is in an abstract block; we transport via thClosed.
  base_proof : Deriv (substF zero O P_Fst)
  base_proof =
    eqSubst (\ fT -> Deriv (atomic (eqn (ap1 fT (ap1 D_Fst O)) (codeFTeq1_Fst O))))
             (eqSym (thClosed zero O))
             D_correct_Fst_base

  step_concl : Deriv (substF zero (ap2 Pair (var v1Nat) (var v2Nat)) P_Fst)
  step_concl =
    eqSubst (\ fT -> Deriv (atomic (eqn
                                (ap1 fT (ap1 D_Fst (ap2 Pair (var v1Nat) (var v2Nat))))
                                (codeFTeq1_Fst (ap2 Pair (var v1Nat) (var v2Nat))))))
             (eqSym (thClosed zero (ap2 Pair (var v1Nat) (var v2Nat))))
             (D_correct_Fst_step (var v1Nat) (var v2Nat))

  -- Wrap step_concl in two axK's to discharge v1- and v2-hypotheses.
  step_imp_inner : Deriv (substF zero (var v2Nat) P_Fst imp
                          substF zero (ap2 Pair (var v1Nat) (var v2Nat)) P_Fst)
  step_imp_inner =
    mp (axK (substF zero (ap2 Pair (var v1Nat) (var v2Nat)) P_Fst)
            (substF zero (var v2Nat) P_Fst))
       step_concl

  step_imp : Deriv (substF zero (var v1Nat) P_Fst imp
                    (substF zero (var v2Nat) P_Fst imp
                     substF zero (ap2 Pair (var v1Nat) (var v2Nat)) P_Fst))
  step_imp =
    mp (axK (substF zero (var v2Nat) P_Fst imp
             substF zero (ap2 Pair (var v1Nat) (var v2Nat)) P_Fst)
            (substF zero (var v1Nat) P_Fst))
       step_imp_inner

  univ : Deriv P_Fst
  univ = ruleIndBT P_Fst v1Nat v2Nat base_proof step_imp

D_correct_Fst : (x : Term) ->
  Deriv (atomic (eqn (ap1 thmT (ap1 D_Fst x)) (codeFTeq1_Fst x)))
D_correct_Fst x =
  eqSubst (\ fT -> Deriv (atomic (eqn (ap1 fT (ap1 D_Fst x)) (codeFTeq1_Fst x))))
           (thClosed zero x)
           (ruleInst zero x univ)
