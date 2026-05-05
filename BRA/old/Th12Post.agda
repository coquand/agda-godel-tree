{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Th12Post -- schematic Theorem 12 for Post f h (Fun2 case).

module BRA.Th12Post where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor          using (cor)
open import BRA.Thm.ThmT     using (thmT)
import BRA.Thm12.Parts.Post

module Th12PostCase
  (f : Fun1)
  (h : Fun2)
  (Df : Fun1)
  (D2_h : Fun2)
  (D_correct_f : (x : Term) ->
     Deriv (atomic (eqn
       (ap1 thmT (ap1 Df x))
       (ap2 Pair
         (ap2 Pair (reify tagAp1)
                   (ap2 Pair (reify (codeF1 f)) (ap1 cor x)))
         (ap1 cor (ap1 f x))))))
  (D_correct_h : (x v : Term) ->
     Deriv (atomic (eqn
       (ap1 thmT (ap2 D2_h x v))
       (ap2 Pair
         (ap2 Pair (reify tagAp2)
                   (ap2 Pair (reify (codeF2 h))
                             (ap2 Pair (ap1 cor x) (ap1 cor v))))
         (ap1 cor (ap2 h x v))))))
  where

  open BRA.Thm12.Parts.Post.PostCase f h Df D2_h D_correct_f D_correct_h
    using (D2_Post_fh ; D_correct2_Post_fh ; codeFTeq2_Post)
    public

  Df_F2_Post_fh : Fun2
  Df_F2_Post_fh = D2_Post_fh

  P_Th12_Post_fh : Formula
  P_Th12_Post_fh =
    atomic (eqn (ap1 thmT (ap2 Df_F2_Post_fh (var zero) (var (suc zero))))
                (codeFTeq2_Post (var zero) (var (suc zero))))

  Th12_F2_Post_fh : Deriv P_Th12_Post_fh
  Th12_F2_Post_fh = D_correct2_Post_fh (var zero) (var (suc zero))
