{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm12.Param.AxLift
--
-- Parametric-Term encoding constants and dispatch lemma for axLift.

module BRA2.Thm12.Param.AxLift where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Deriv
open import BRA2.Thm.ThmT
  using ( thmT ; tagCode_axLift ; thmTDispAxLift_param )

parEncAxLift : Fun1 -> Term -> Term -> Term
parEncAxLift f aT bT =
  ap2 Pair tagCode_axLift
    (ap2 Pair (reify (codeF1 f)) (ap2 Pair aT bT))

parOutAxLift : Fun1 -> Term -> Term -> Term
parOutAxLift f aT bT =
  ap2 Pair
    (ap2 Pair (reify tagAp2)
      (ap2 Pair (ap2 Pair (reify (leftT (codeF2 (Lift I))))
                          (reify (codeF1 f)))
                (ap2 Pair aT bT)))
    (ap2 Pair (reify tagAp1)
      (ap2 Pair (reify (codeF1 f)) aT))

parDispAxLift : (f : Fun1) (aT bT : Term) ->
  Deriv (atomic (eqn (ap1 thmT (parEncAxLift f aT bT)) (parOutAxLift f aT bT)))
parDispAxLift f aT bT = thmTDispAxLift_param f aT bT
