{-# OPTIONS --safe --without-K --exact-split #-}

module BRA2.Thm12.Param.AxFst where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Deriv
open import BRA2.Thm.ThmT
  using ( thmT ; tagCode_axFst ; thmTDispAxFst_param )

parEncAxFst : Term -> Term -> Term
parEncAxFst aT bT =
  ap2 Pair tagCode_axFst (ap2 Pair aT bT)

parOutAxFst : Term -> Term -> Term
parOutAxFst aT bT =
  ap2 Pair
    (ap2 Pair (reify tagAp1)
      (ap2 Pair (reify (codeF1 Fst))
        (ap2 Pair (reify tagAp2)
          (ap2 Pair (reify (codeF2 Pair))
            (ap2 Pair aT bT)))))
    aT

parDispAxFst : (aT bT : Term) ->
  Deriv (atomic (eqn (ap1 thmT (parEncAxFst aT bT)) (parOutAxFst aT bT)))
parDispAxFst aT bT = thmTDispAxFst_param aT bT
