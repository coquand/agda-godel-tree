{-# OPTIONS --safe --without-K --exact-split #-}

module BRA2.Thm12.Param.AxTreeEqNL where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Deriv
open import BRA2.Thm.ThmT
  using ( thmT ; tagCode_axTreeEqNL ; thmTDispAxTreeEqNL_param )

parEncAxTreeEqNL : Term -> Term -> Term
parEncAxTreeEqNL aT bT =
  ap2 Pair tagCode_axTreeEqNL (ap2 Pair aT bT)

parOutAxTreeEqNL : Term -> Term -> Term
parOutAxTreeEqNL aT bT =
  ap2 Pair
    (ap2 Pair (reify tagAp2)
      (ap2 Pair (reify (codeF2 TreeEq))
        (ap2 Pair (ap2 Pair (reify tagAp2)
                            (ap2 Pair (reify (codeF2 Pair))
                                      (ap2 Pair aT bT)))
                  O)))
    (reify (code (ap2 Pair O O)))

parDispAxTreeEqNL : (aT bT : Term) ->
  Deriv (atomic (eqn (ap1 thmT (parEncAxTreeEqNL aT bT)) (parOutAxTreeEqNL aT bT)))
parDispAxTreeEqNL aT bT = thmTDispAxTreeEqNL_param aT bT
