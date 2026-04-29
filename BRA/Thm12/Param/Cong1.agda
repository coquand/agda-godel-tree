{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm12.Param.Cong1
--
-- Parametric-Term encoding constructor and dispatch for cong1.
-- Wraps a sub-encoding y_h_T (whose thmT-image is Pair u1 u2) with cong1
-- under a Fun1 functor; result image: Pair (encoded f-applied-to-u1)
-- (encoded f-applied-to-u2).

module BRA.Thm12.Param.Cong1 where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Thm.ThmT
  using ( thmT ; tagCode_cong1 ; thmTDispCong1_param )

parEncCong1 : Fun1 -> Term -> Term
parEncCong1 f y_h_T =
  ap2 Pair tagCode_cong1 (ap2 Pair (reify (codeF1 f)) y_h_T)

parOutCong1 : Fun1 -> Term -> Term -> Term
parOutCong1 f u1 u2 =
  ap2 Pair (ap2 Pair (reify tagAp1) (ap2 Pair (reify (codeF1 f)) u1))
           (ap2 Pair (reify tagAp1) (ap2 Pair (reify (codeF1 f)) u2))

parDispCong1 : (f : Fun1) (y_h_T : Term) (u1 u2 : Term) ->
  Deriv (atomic (eqn (ap1 thmT y_h_T) (ap2 Pair u1 u2))) ->
  Deriv (atomic (eqn (ap1 thmT (parEncCong1 f y_h_T)) (parOutCong1 f u1 u2)))
parDispCong1 f y_h_T u1 u2 d_h = thmTDispCong1_param f y_h_T u1 u2 d_h
