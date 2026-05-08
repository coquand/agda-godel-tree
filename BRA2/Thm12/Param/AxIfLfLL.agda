{-# OPTIONS --safe --without-K --exact-split #-}

module BRA2.Thm12.Param.AxIfLfLL where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Deriv
open import BRA2.Thm.Parts.AxIfLfLL using (outAxIfLfLL)
open import BRA2.Thm.ThmT
  using ( thmT ; tagCode_axIfLfLL ; thmTDispAxIfLfLL_param )

parEncAxIfLfLL : Term -> Term
parEncAxIfLfLL payT =
  ap2 Pair tagCode_axIfLfLL payT

parOutAxIfLfLL : Term
parOutAxIfLfLL = reify outAxIfLfLL

parDispAxIfLfLL : (payT : Term) ->
  Deriv (atomic (eqn (ap1 thmT (parEncAxIfLfLL payT)) parOutAxIfLfLL))
parDispAxIfLfLL payT = thmTDispAxIfLfLL_param payT
