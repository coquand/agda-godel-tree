{-# OPTIONS --safe --without-K --exact-split #-}

module BRA2.Thm12.Param.AxTreeEqLN where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.DerivThreshold
open import BRA2.Thm.ThmT
  using ( thmT ; tagCode_axTreeEqLN ; thmTDispAxTreeEqLN_param )

parEncAxTreeEqLN : Term -> Term -> Term
parEncAxTreeEqLN aT bT =
  ap2 Pair tagCode_axTreeEqLN (ap2 Pair aT bT)

parOutAxTreeEqLN : Term -> Term -> Term
parOutAxTreeEqLN aT bT =
  ap2 Pair
    (ap2 Pair (reify tagAp2)
      (ap2 Pair (reify (codeF2 TreeEq))
        (ap2 Pair O
          (ap2 Pair (reify tagAp2)
            (ap2 Pair (reify (codeF2 Pair))
              (ap2 Pair aT bT))))))
    (reify (code (ap2 Pair O O)))

parDispAxTreeEqLN : (aT bT : Term) ->
  Deriv (atomic (eqn (ap1 thmT (parEncAxTreeEqLN aT bT)) (parOutAxTreeEqLN aT bT)))
parDispAxTreeEqLN aT bT = thmTDispAxTreeEqLN_param aT bT
