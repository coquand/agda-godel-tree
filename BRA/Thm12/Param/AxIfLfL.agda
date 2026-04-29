{-# OPTIONS --safe --without-K --exact-split #-}

module BRA.Thm12.Param.AxIfLfL where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Thm.ThmT
  using ( thmT ; tagCode_axIfLfL ; thmTDispAxIfLfL_param )

parEncAxIfLfL : Term -> Term -> Term
parEncAxIfLfL aT bT =
  ap2 Pair tagCode_axIfLfL (ap2 Pair aT bT)

parOutAxIfLfL : Term -> Term -> Term
parOutAxIfLfL aT bT =
  ap2 Pair
    (ap2 Pair (reify tagAp2)
      (ap2 Pair (reify (codeF2 IfLf))
        (ap2 Pair O
          (ap2 Pair (reify tagAp2)
            (ap2 Pair (reify (codeF2 Pair))
              (ap2 Pair aT bT))))))
    aT

parDispAxIfLfL : (aT bT : Term) ->
  Deriv (atomic (eqn (ap1 thmT (parEncAxIfLfL aT bT)) (parOutAxIfLfL aT bT)))
parDispAxIfLfL aT bT = thmTDispAxIfLfL_param aT bT
