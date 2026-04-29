{-# OPTIONS --safe --without-K --exact-split #-}

module BRA.Thm12.Param.AxIfLfNL where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Thm.ThmT
  using ( thmT ; tagCode_axIfLfNL ; thmTDispAxIfLfNL_param )

parEncAxIfLfNL : Term -> Term -> Term
parEncAxIfLfNL xT yT =
  ap2 Pair tagCode_axIfLfNL (ap2 Pair xT yT)

parOutAxIfLfNL : Term -> Term -> Term
parOutAxIfLfNL xT yT =
  ap2 Pair
    (ap2 Pair (reify tagAp2)
      (ap2 Pair (reify (codeF2 IfLf))
        (ap2 Pair (ap2 Pair (reify tagAp2)
                            (ap2 Pair (reify (codeF2 Pair))
                                      (ap2 Pair xT yT)))
                  O)))
    O

parDispAxIfLfNL : (xT yT : Term) ->
  Deriv (atomic (eqn (ap1 thmT (parEncAxIfLfNL xT yT)) (parOutAxIfLfNL xT yT)))
parDispAxIfLfNL xT yT = thmTDispAxIfLfNL_param xT yT
