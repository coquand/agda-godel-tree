{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Th12Comp -- schematic Theorem 12 for Comp f g (Fun1 case).

module BRA.Th12Comp where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor          using (cor)
open import BRA.Thm.ThmT     using (thmT)
import BRA.Thm12.Parts.Comp

module Th12CompCase
  (f' g : Fun1)
  (Df' Dg : Fun1)
  (D_correct_f' : (x : Term) ->
     Deriv (atomic (eqn
       (ap1 thmT (ap1 Df' x))
       (ap2 Pair
         (ap2 Pair (reify tagAp1)
                   (ap2 Pair (reify (codeF1 f')) (ap1 cor x)))
         (ap1 cor (ap1 f' x))))))
  (D_correct_g : (x : Term) ->
     Deriv (atomic (eqn
       (ap1 thmT (ap1 Dg x))
       (ap2 Pair
         (ap2 Pair (reify tagAp1)
                   (ap2 Pair (reify (codeF1 g)) (ap1 cor x)))
         (ap1 cor (ap1 g x))))))
  where

  open BRA.Thm12.Parts.Comp.CompCase f' g Df' Dg D_correct_f' D_correct_g
    using (D_Comp_f'g ; D_correct_Comp_f'g ; codeFTeq1_Comp)
    public

  Df_F1_Comp_f'g : Fun1
  Df_F1_Comp_f'g = D_Comp_f'g

  P_Th12_Comp_f'g : Formula
  P_Th12_Comp_f'g =
    atomic (eqn (ap1 thmT (ap1 Df_F1_Comp_f'g (var zero)))
                (codeFTeq1_Comp (var zero)))

  Th12_F1_Comp_f'g : Deriv P_Th12_Comp_f'g
  Th12_F1_Comp_f'g = D_correct_Comp_f'g (var zero)
