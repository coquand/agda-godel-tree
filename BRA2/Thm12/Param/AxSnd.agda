{-# OPTIONS --safe --without-K --exact-split #-}

module BRA2.Thm12.Param.AxSnd where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.DerivThreshold
open import BRA2.Thm.ThmT
  using ( thmT ; tagCode_axSnd ; thmTDispAxSnd_param )

parEncAxSnd : Term -> Term -> Term
parEncAxSnd aT bT =
  ap2 Pair tagCode_axSnd (ap2 Pair aT bT)

parOutAxSnd : Term -> Term -> Term
parOutAxSnd aT bT =
  ap2 Pair
    (ap2 Pair (reify tagAp1)
      (ap2 Pair (reify (codeF1 Snd))
        (ap2 Pair (reify tagAp2)
          (ap2 Pair (reify (codeF2 Pair))
            (ap2 Pair aT bT)))))
    bT

parDispAxSnd : (aT bT : Term) ->
  Deriv (atomic (eqn (ap1 thmT (parEncAxSnd aT bT)) (parOutAxSnd aT bT)))
parDispAxSnd aT bT = thmTDispAxSnd_param aT bT
