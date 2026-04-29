{-# OPTIONS --safe --without-K --exact-split #-}

module BRA.Thm12.Param.CongR where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Thm.ThmT
  using ( thmT ; tagCode_congR ; thmTDispCongR_param )

parEncCongR : Fun2 -> Term -> Term -> Term
parEncCongR g y_h_T xT =
  ap2 Pair tagCode_congR
    (ap2 Pair (reify (codeF2 g)) (ap2 Pair y_h_T xT))

parOutCongR : Fun2 -> Term -> Term -> Term -> Term
parOutCongR g xT u1 u2 =
  ap2 Pair (ap2 Pair (reify tagAp2)
                     (ap2 Pair (reify (codeF2 g))
                               (ap2 Pair xT u1)))
           (ap2 Pair (reify tagAp2)
                     (ap2 Pair (reify (codeF2 g))
                               (ap2 Pair xT u2)))

parDispCongR : (g : Fun2) (y_h_T xT : Term) (u1 u2 : Term)
               (y_h' x' : Term) ->
  Deriv (atomic (eqn (ap1 Fst y_h_T) (ap2 Pair x' y_h'))) ->
  Deriv (atomic (eqn (ap1 thmT y_h_T) (ap2 Pair u1 u2))) ->
  Deriv (atomic (eqn (ap1 thmT (parEncCongR g y_h_T xT))
                     (parOutCongR g xT u1 u2)))
parDispCongR g y_h_T xT u1 u2 y_h' x' shape d_h =
  thmTDispCongR_param g xT y_h_T u1 u2 y_h' x' shape d_h
