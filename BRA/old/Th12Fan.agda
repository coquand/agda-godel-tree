{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Th12Fan -- schematic Theorem 12 for Fan h1 h2 h (Fun2 case).

module BRA.Th12Fan where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor          using (cor)
open import BRA.Thm.ThmT     using (thmT)
import BRA.Thm12.Parts.Fan

module Th12FanCase
  (h1 h2 h : Fun2)
  (D2_h1 D2_h2 D2_h : Fun2)
  (D_correct_h1 : (x v : Term) ->
     Deriv (atomic (eqn
       (ap1 thmT (ap2 D2_h1 x v))
       (ap2 Pair
         (ap2 Pair (reify tagAp2)
                   (ap2 Pair (reify (codeF2 h1))
                             (ap2 Pair (ap1 cor x) (ap1 cor v))))
         (ap1 cor (ap2 h1 x v))))))
  (D_correct_h2 : (x v : Term) ->
     Deriv (atomic (eqn
       (ap1 thmT (ap2 D2_h2 x v))
       (ap2 Pair
         (ap2 Pair (reify tagAp2)
                   (ap2 Pair (reify (codeF2 h2))
                             (ap2 Pair (ap1 cor x) (ap1 cor v))))
         (ap1 cor (ap2 h2 x v))))))
  (D_correct_h : (x v : Term) ->
     Deriv (atomic (eqn
       (ap1 thmT (ap2 D2_h x v))
       (ap2 Pair
         (ap2 Pair (reify tagAp2)
                   (ap2 Pair (reify (codeF2 h))
                             (ap2 Pair (ap1 cor x) (ap1 cor v))))
         (ap1 cor (ap2 h x v))))))
  (D2_h1_shape : (x v : Term) ->
     Sigma Term (\ y' -> Sigma Term (\ x' ->
       Deriv (atomic (eqn (ap1 Fst (ap2 D2_h1 x v)) (ap2 Pair x' y'))))))
  (D2_h2_shape : (x v : Term) ->
     Sigma Term (\ y' -> Sigma Term (\ x' ->
       Deriv (atomic (eqn (ap1 Fst (ap2 D2_h2 x v)) (ap2 Pair x' y'))))))
  where

  open BRA.Thm12.Parts.Fan.FanCase h1 h2 h D2_h1 D2_h2 D2_h
    D_correct_h1 D_correct_h2 D_correct_h D2_h1_shape D2_h2_shape
    using (D2_Fan_h1h2h ; D_correct2_Fan_h1h2h ; codeFTeq2_Fan)
    public

  Df_F2_Fan_h1h2h : Fun2
  Df_F2_Fan_h1h2h = D2_Fan_h1h2h

  P_Th12_Fan_h1h2h : Formula
  P_Th12_Fan_h1h2h =
    atomic (eqn (ap1 thmT (ap2 Df_F2_Fan_h1h2h (var zero) (var (suc zero))))
                (codeFTeq2_Fan (var zero) (var (suc zero))))

  Th12_F2_Fan_h1h2h : Deriv P_Th12_Fan_h1h2h
  Th12_F2_Fan_h1h2h = D_correct2_Fan_h1h2h (var zero) (var (suc zero))
