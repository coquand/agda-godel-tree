{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm12.Parts.Snd   (Theorem 12 case for f = Snd).
--
-- Mirrors Parts/Fst.agda with Fst -> Snd, axFst -> axSnd, axFstLf -> axSndLf,
-- and the v1 -> v2 axis flip in axSnd (Pair v1 v2) = v2.

module BRA.Thm12.Parts.Snd where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor
open import BRA.Thm.Tag using (tagAxSnd ; tagAxSndLf)
open import BRA.Thm.ThmT using (thmT ; tagCode_axSnd ; tagCode_axSndLf ; thClosed)
open import BRA.Thm12.Param.AxSnd
  using (parEncAxSnd ; parOutAxSnd ; parDispAxSnd)
open import BRA.Thm12.Param.AxSndLf
  using (parEncAxSndLf ; parOutAxSndLf ; parDispAxSndLf)

------------------------------------------------------------------------
codeFTeq1_Snd : Term -> Term
codeFTeq1_Snd x =
  ap2 Pair
    (ap2 Pair (reify tagAp1)
              (ap2 Pair (reify (codeF1 Snd)) (ap1 cor x)))
    (ap1 cor (ap1 Snd x))

------------------------------------------------------------------------
private
  nonleafFun : Fun1
  nonleafFun = Comp2 Pair (KT tagCode_axSnd)
                  (Comp2 Pair (Comp cor Fst) (Comp cor Snd))

  dispatchFun : Fun1
  dispatchFun = Comp2 Pair (KT (parEncAxSndLf O)) nonleafFun

D_Snd : Fun1
D_Snd = Comp2 IfLf I dispatchFun

------------------------------------------------------------------------
D_Snd_reduce_O : Deriv (atomic (eqn (ap1 D_Snd O) (parEncAxSndLf O)))
D_Snd_reduce_O =
  let s1 : Deriv (atomic (eqn (ap1 D_Snd O)
                              (ap2 IfLf (ap1 I O) (ap1 dispatchFun O))))
      s1 = axComp2 IfLf I dispatchFun O

      s2 = axI O

      s3 : Deriv (atomic (eqn (ap2 IfLf (ap1 I O) (ap1 dispatchFun O))
                              (ap2 IfLf O (ap1 dispatchFun O))))
      s3 = congL IfLf (ap1 dispatchFun O) s2

      d1 = axComp2 Pair (KT (parEncAxSndLf O)) nonleafFun O

      d2 : Deriv (atomic (eqn (ap1 (KT (parEncAxSndLf O)) O) (parEncAxSndLf O)))
      d2 = axKT (nd (natCode tagAxSndLf) lf) O

      d_final : Deriv (atomic (eqn (ap1 dispatchFun O)
                                   (ap2 Pair (parEncAxSndLf O) (ap1 nonleafFun O))))
      d_final = ruleTrans d1 (congL Pair (ap1 nonleafFun O) d2)

      s4 = congR IfLf O d_final

      s5 = axIfLfL (parEncAxSndLf O) (ap1 nonleafFun O)
  in ruleTrans s1 (ruleTrans s3 (ruleTrans s4 s5))

------------------------------------------------------------------------
D_Snd_reduce_Pair : (v1 v2 : Term) ->
  Deriv (atomic (eqn (ap1 D_Snd (ap2 Pair v1 v2))
                     (parEncAxSnd (ap1 cor v1) (ap1 cor v2))))
D_Snd_reduce_Pair v1 v2 =
  let pv = ap2 Pair v1 v2

      s1 = axComp2 IfLf I dispatchFun pv
      s2 = axI pv
      s3 = congL IfLf (ap1 dispatchFun pv) s2

      d1 = axComp2 Pair (KT (parEncAxSndLf O)) nonleafFun pv
      d2 : Deriv (atomic (eqn (ap1 (KT (parEncAxSndLf O)) pv) (parEncAxSndLf O)))
      d2 = axKT (nd (natCode tagAxSndLf) lf) pv
      d_kt = ruleTrans d1 (congL Pair (ap1 nonleafFun pv) d2)

      n1 = axComp2 Pair (KT tagCode_axSnd)
                   (Comp2 Pair (Comp cor Fst) (Comp cor Snd)) pv
      n2 : Deriv (atomic (eqn (ap1 (KT tagCode_axSnd) pv) tagCode_axSnd))
      n2 = axKT (natCode (suc (suc (suc zero)))) pv  -- tagAxSnd = 3

      n3a = axComp2 Pair (Comp cor Fst) (Comp cor Snd) pv
      n3b = axComp cor Fst pv
      n3c : Deriv (atomic (eqn (ap1 cor (ap1 Fst pv)) (ap1 cor v1)))
      n3c = cong1 cor (axFst v1 v2)
      n3 = ruleTrans n3b n3c

      n4b = axComp cor Snd pv
      n4c : Deriv (atomic (eqn (ap1 cor (ap1 Snd pv)) (ap1 cor v2)))
      n4c = cong1 cor (axSnd v1 v2)
      n4 = ruleTrans n4b n4c

      n5 = ruleTrans (congL Pair (ap1 (Comp cor Snd) pv) n3)
                     (congR Pair (ap1 cor v1) n4)
      n6 = ruleTrans n3a n5

      n_final : Deriv (atomic (eqn (ap1 nonleafFun pv)
                                   (ap2 Pair tagCode_axSnd
                                             (ap2 Pair (ap1 cor v1) (ap1 cor v2)))))
      n_final = ruleTrans n1
                  (ruleTrans (congL Pair _ n2)
                             (congR Pair tagCode_axSnd n6))

      d_step : Deriv (atomic (eqn (ap1 dispatchFun pv)
                                  (ap2 Pair (parEncAxSndLf O)
                                            (parEncAxSnd (ap1 cor v1) (ap1 cor v2)))))
      d_step = ruleTrans d_kt (congR Pair (parEncAxSndLf O) n_final)

      s4 = congR IfLf pv d_step

      s5 = axIfLfN v1 v2 (parEncAxSndLf O) (parEncAxSnd (ap1 cor v1) (ap1 cor v2))
  in ruleTrans s1 (ruleTrans s3 (ruleTrans s4 s5))

------------------------------------------------------------------------
bridgeBase : Deriv (atomic (eqn parOutAxSndLf (codeFTeq1_Snd O)))
bridgeBase =
  let cor_O : Deriv (atomic (eqn (ap1 cor O) O))
      cor_O = axRecLf O stepCor

      snd_O : Deriv (atomic (eqn (ap1 Snd O) O))
      snd_O = axSndLf

      cor_snd_O_to_cor_O : Deriv (atomic (eqn (ap1 cor (ap1 Snd O)) (ap1 cor O)))
      cor_snd_O_to_cor_O = cong1 cor snd_O

      cor_snd_O : Deriv (atomic (eqn (ap1 cor (ap1 Snd O)) O))
      cor_snd_O = ruleTrans cor_snd_O_to_cor_O cor_O

      step_inner : Deriv (atomic (eqn
                          (ap2 Pair (reify (codeF1 Snd)) O)
                          (ap2 Pair (reify (codeF1 Snd)) (ap1 cor O))))
      step_inner = congR Pair (reify (codeF1 Snd)) (ruleSym cor_O)

      step_outer : Deriv (atomic (eqn
                          (ap2 Pair (reify tagAp1) (ap2 Pair (reify (codeF1 Snd)) O))
                          (ap2 Pair (reify tagAp1) (ap2 Pair (reify (codeF1 Snd)) (ap1 cor O)))))
      step_outer = congR Pair (reify tagAp1) step_inner

      step_lhs : Deriv (atomic (eqn
                          (ap2 Pair (ap2 Pair (reify tagAp1) (ap2 Pair (reify (codeF1 Snd)) O)) O)
                          (ap2 Pair (ap2 Pair (reify tagAp1) (ap2 Pair (reify (codeF1 Snd)) (ap1 cor O))) O)))
      step_lhs = congL Pair O step_outer

      step_rhs : Deriv (atomic (eqn
                          (ap2 Pair (ap2 Pair (reify tagAp1) (ap2 Pair (reify (codeF1 Snd)) (ap1 cor O))) O)
                          (ap2 Pair (ap2 Pair (reify tagAp1) (ap2 Pair (reify (codeF1 Snd)) (ap1 cor O))) (ap1 cor (ap1 Snd O)))))
      step_rhs = congR Pair _ (ruleSym cor_snd_O)
  in ruleTrans step_lhs step_rhs

bridgeStep : (v1 v2 : Term) ->
  Deriv (atomic (eqn (parOutAxSnd (ap1 cor v1) (ap1 cor v2))
                     (codeFTeq1_Snd (ap2 Pair v1 v2))))
bridgeStep v1 v2 =
  let cor_pair_unfold : Deriv (atomic (eqn (ap1 cor (ap2 Pair v1 v2))
                                           (ap2 Pair (reify tagAp2)
                                                     (ap2 Pair (reify (codeF2 Pair))
                                                               (ap2 Pair (ap1 cor v1) (ap1 cor v2))))))
      cor_pair_unfold =
        let recs = ap2 Pair (ap1 cor v1) (ap1 cor v2)
            orig = ap2 Pair v1 v2
            r1 = axRecNd O stepCor v1 v2
            r2 = stepCorRed orig recs
        in ruleTrans r1 r2

      cor_snd_pair : Deriv (atomic (eqn (ap1 cor (ap1 Snd (ap2 Pair v1 v2))) (ap1 cor v2)))
      cor_snd_pair = cong1 cor (axSnd v1 v2)

      lhs_inner : Deriv (atomic (eqn
                          (ap2 Pair (reify tagAp2)
                            (ap2 Pair (reify (codeF2 Pair)) (ap2 Pair (ap1 cor v1) (ap1 cor v2))))
                          (ap1 cor (ap2 Pair v1 v2))))
      lhs_inner = ruleSym cor_pair_unfold

      lhs_step : Deriv (atomic (eqn
                          (ap2 Pair (reify (codeF1 Snd))
                            (ap2 Pair (reify tagAp2)
                              (ap2 Pair (reify (codeF2 Pair)) (ap2 Pair (ap1 cor v1) (ap1 cor v2)))))
                          (ap2 Pair (reify (codeF1 Snd)) (ap1 cor (ap2 Pair v1 v2)))))
      lhs_step = congR Pair (reify (codeF1 Snd)) lhs_inner

      lhs_outer : Deriv (atomic (eqn
                          (ap2 Pair (reify tagAp1)
                            (ap2 Pair (reify (codeF1 Snd))
                              (ap2 Pair (reify tagAp2)
                                (ap2 Pair (reify (codeF2 Pair))
                                  (ap2 Pair (ap1 cor v1) (ap1 cor v2))))))
                          (ap2 Pair (reify tagAp1)
                            (ap2 Pair (reify (codeF1 Snd)) (ap1 cor (ap2 Pair v1 v2))))))
      lhs_outer = congR Pair (reify tagAp1) lhs_step

      step_lhs : Deriv (atomic (eqn (parOutAxSnd (ap1 cor v1) (ap1 cor v2))
                                    (ap2 Pair
                                      (ap2 Pair (reify tagAp1)
                                        (ap2 Pair (reify (codeF1 Snd))
                                          (ap1 cor (ap2 Pair v1 v2))))
                                      (ap1 cor v2))))
      step_lhs = congL Pair (ap1 cor v2) lhs_outer

      step_rhs : Deriv (atomic (eqn
                          (ap2 Pair
                            (ap2 Pair (reify tagAp1)
                              (ap2 Pair (reify (codeF1 Snd)) (ap1 cor (ap2 Pair v1 v2))))
                            (ap1 cor v2))
                          (codeFTeq1_Snd (ap2 Pair v1 v2))))
      step_rhs = congR Pair _ (ruleSym cor_snd_pair)
  in ruleTrans step_lhs step_rhs

------------------------------------------------------------------------
D_correct_Snd_base : Deriv (atomic (eqn (ap1 thmT (ap1 D_Snd O)) (codeFTeq1_Snd O)))
D_correct_Snd_base =
  let r_thmT = cong1 thmT D_Snd_reduce_O
      r_disp = parDispAxSndLf O
  in ruleTrans r_thmT (ruleTrans r_disp bridgeBase)

D_correct_Snd_step : (v1 v2 : Term) ->
  Deriv (atomic (eqn (ap1 thmT (ap1 D_Snd (ap2 Pair v1 v2))) (codeFTeq1_Snd (ap2 Pair v1 v2))))
D_correct_Snd_step v1 v2 =
  let r_thmT = cong1 thmT (D_Snd_reduce_Pair v1 v2)
      r_disp = parDispAxSnd (ap1 cor v1) (ap1 cor v2)
      r_bridge = bridgeStep v1 v2
  in ruleTrans r_thmT (ruleTrans r_disp r_bridge)

------------------------------------------------------------------------
private
  v1Nat : Nat
  v1Nat = suc zero
  v2Nat : Nat
  v2Nat = suc (suc zero)

  P_Snd : Formula
  P_Snd = atomic (eqn (ap1 thmT (ap1 D_Snd (var zero))) (codeFTeq1_Snd (var zero)))

  base_proof : Deriv (substF zero O P_Snd)
  base_proof =
    eqSubst (\ fT -> Deriv (atomic (eqn (ap1 fT (ap1 D_Snd O)) (codeFTeq1_Snd O))))
            (eqSym (thClosed zero O))
            D_correct_Snd_base

  step_concl : Deriv (substF zero (ap2 Pair (var v1Nat) (var v2Nat)) P_Snd)
  step_concl =
    eqSubst (\ fT -> Deriv (atomic (eqn
                                (ap1 fT (ap1 D_Snd (ap2 Pair (var v1Nat) (var v2Nat))))
                                (codeFTeq1_Snd (ap2 Pair (var v1Nat) (var v2Nat))))))
            (eqSym (thClosed zero (ap2 Pair (var v1Nat) (var v2Nat))))
            (D_correct_Snd_step (var v1Nat) (var v2Nat))

  step_imp_inner : Deriv (substF zero (var v2Nat) P_Snd imp
                          substF zero (ap2 Pair (var v1Nat) (var v2Nat)) P_Snd)
  step_imp_inner =
    mp (axK (substF zero (ap2 Pair (var v1Nat) (var v2Nat)) P_Snd)
            (substF zero (var v2Nat) P_Snd))
       step_concl

  step_imp : Deriv (substF zero (var v1Nat) P_Snd imp
                    (substF zero (var v2Nat) P_Snd imp
                     substF zero (ap2 Pair (var v1Nat) (var v2Nat)) P_Snd))
  step_imp =
    mp (axK (substF zero (var v2Nat) P_Snd imp
             substF zero (ap2 Pair (var v1Nat) (var v2Nat)) P_Snd)
            (substF zero (var v1Nat) P_Snd))
       step_imp_inner

  univ : Deriv P_Snd
  univ = ruleIndBT P_Snd v1Nat v2Nat base_proof step_imp

D_correct_Snd : (x : Term) ->
  Deriv (atomic (eqn (ap1 thmT (ap1 D_Snd x)) (codeFTeq1_Snd x)))
D_correct_Snd x =
  eqSubst (\ fT -> Deriv (atomic (eqn (ap1 fT (ap1 D_Snd x)) (codeFTeq1_Snd x))))
          (thClosed zero x)
          (ruleInst zero x univ)
