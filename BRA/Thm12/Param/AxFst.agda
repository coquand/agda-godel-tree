{-# OPTIONS --safe --without-K --exact-split #-}

module BRA.Thm12.Param.AxFst where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Thm.ThmT
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
