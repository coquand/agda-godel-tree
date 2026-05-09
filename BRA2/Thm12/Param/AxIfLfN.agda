{-# OPTIONS --safe --without-K --exact-split #-}

module BRA2.Thm12.Param.AxIfLfN where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.DerivThreshold
open import BRA2.Thm.ThmT
  using ( thmT ; tagCode_axIfLfN ; thmTDispAxIfLfN_param )

parEncAxIfLfN : Term -> Term -> Term -> Term -> Term
parEncAxIfLfN xT yT aT bT =
  ap2 Pair tagCode_axIfLfN
    (ap2 Pair xT (ap2 Pair yT (ap2 Pair aT bT)))

parOutAxIfLfN : Term -> Term -> Term -> Term -> Term
parOutAxIfLfN xT yT aT bT =
  ap2 Pair
    (ap2 Pair (reify tagAp2)
      (ap2 Pair (reify (codeF2 IfLf))
        (ap2 Pair (ap2 Pair (reify tagAp2)
                            (ap2 Pair (reify (codeF2 Pair))
                                      (ap2 Pair xT yT)))
                  (ap2 Pair (reify tagAp2)
                            (ap2 Pair (reify (codeF2 Pair))
                                      (ap2 Pair aT bT))))))
    bT

parDispAxIfLfN : (xT yT aT bT : Term) ->
  Deriv (atomic (eqn (ap1 thmT (parEncAxIfLfN xT yT aT bT))
                     (parOutAxIfLfN xT yT aT bT)))
parDispAxIfLfN xT yT aT bT = thmTDispAxIfLfN_param xT yT aT bT
