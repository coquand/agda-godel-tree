{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Th12Lift -- schematic Theorem 12 for Lift f (Fun2 case).
--
-- Lift f is structural: Theorem 12 for Lift f is derived from Theorem 12
-- for the underlying f (Fun1) via the parametric LiftCase module in
-- BRA/Thm12/Parts/Lift.agda.
--
-- This file packages the parametric LiftCase as a schematic Deriv P
-- (with var 0, var 1 free) for uniformity with Th12_F2_Pair etc.
-- The wrapper takes Theorem 12 for f as a parametric input.

module BRA.Th12Lift where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor          using (cor)
open import BRA.Thm.ThmT     using (thmT)
import BRA.Thm12.Parts.Lift

------------------------------------------------------------------------
-- Th12_F2_Lift : parametric over (f, Df, D_correct_f) -- the underlying
-- functor f, its Theorem 12 witness Df, and its correctness lemma.
--
-- Output: schematic Deriv P with var 0 (= a), var 1 (= b) free.

module Th12LiftCase
  (f : Fun1)
  (Df : Fun1)
  (D_correct_f : (x : Term) ->
     Deriv (atomic (eqn
       (ap1 thmT (ap1 Df x))
       (ap2 Pair
         (ap2 Pair (reify tagAp1)
                   (ap2 Pair (reify (codeF1 f)) (ap1 cor x)))
         (ap1 cor (ap1 f x))))))
  where

  open BRA.Thm12.Parts.Lift.LiftCase f Df D_correct_f
    using (D2_Lift_f ; D_correct2_Lift_f ; codeFTeq2_Lift)
    public

  Df_F2_Lift_f : Fun2
  Df_F2_Lift_f = D2_Lift_f

  P_Th12_Lift_f : Formula
  P_Th12_Lift_f = atomic (eqn (ap1 thmT (ap2 Df_F2_Lift_f (var zero) (var (suc zero))))
                               (codeFTeq2_Lift (var zero) (var (suc zero))))

  Th12_F2_Lift_f : Deriv P_Th12_Lift_f
  Th12_F2_Lift_f = D_correct2_Lift_f (var zero) (var (suc zero))
