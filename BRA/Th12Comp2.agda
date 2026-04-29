{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Th12Comp2 -- schematic Theorem 12 for Comp2 h f g (Fun1 case).

module BRA.Th12Comp2 where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor          using (cor)
open import BRA.Thm.ThmT     using (thmT)
import BRA.Thm12.Parts.Comp2

module Th12Comp2Case
  (h : Fun2)
  (f g : Fun1)
  (D2_h : Fun2)
  (Df Dg : Fun1)
  (D_correct2_h : (x v : Term) ->
     Deriv (atomic (eqn
       (ap1 thmT (ap2 D2_h x v))
       (ap2 Pair
         (ap2 Pair (reify tagAp2)
                   (ap2 Pair (reify (codeF2 h))
                             (ap2 Pair (ap1 cor x) (ap1 cor v))))
         (ap1 cor (ap2 h x v))))))
  (D_correct_f : (x : Term) ->
     Deriv (atomic (eqn
       (ap1 thmT (ap1 Df x))
       (ap2 Pair
         (ap2 Pair (reify tagAp1)
                   (ap2 Pair (reify (codeF1 f)) (ap1 cor x)))
         (ap1 cor (ap1 f x))))))
  (D_correct_g : (x : Term) ->
     Deriv (atomic (eqn
       (ap1 thmT (ap1 Dg x))
       (ap2 Pair
         (ap2 Pair (reify tagAp1)
                   (ap2 Pair (reify (codeF1 g)) (ap1 cor x)))
         (ap1 cor (ap1 g x))))))
  (Df_shape : (x : Term) ->
     Sigma Term (\ y' -> Sigma Term (\ x' ->
       Deriv (atomic (eqn (ap1 Fst (ap1 Df x)) (ap2 Pair x' y'))))))
  (Dg_shape : (x : Term) ->
     Sigma Term (\ y' -> Sigma Term (\ x' ->
       Deriv (atomic (eqn (ap1 Fst (ap1 Dg x)) (ap2 Pair x' y'))))))
  where

  open BRA.Thm12.Parts.Comp2.Comp2Case h f g D2_h Df Dg
    D_correct2_h D_correct_f D_correct_g Df_shape Dg_shape
    using (D_Comp2_hfg ; D_correct_Comp2_hfg ; codeFTeq1_Comp2)
    public

  Df_F1_Comp2_hfg : Fun1
  Df_F1_Comp2_hfg = D_Comp2_hfg

  P_Th12_Comp2_hfg : Formula
  P_Th12_Comp2_hfg =
    atomic (eqn (ap1 thmT (ap1 Df_F1_Comp2_hfg (var zero)))
                (codeFTeq1_Comp2 (var zero)))

  Th12_F1_Comp2_hfg : Deriv P_Th12_Comp2_hfg
  Th12_F1_Comp2_hfg = D_correct_Comp2_hfg (var zero)
