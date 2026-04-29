{-# OPTIONS --safe --without-K --exact-split #-}

module BRA.Thm12.Param.AxIfLfLL where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Thm.Parts.AxIfLfLL using (outAxIfLfLL)
open import BRA.Thm.ThmT
  using ( thmT ; tagCode_axIfLfLL ; thmTDispAxIfLfLL_param )

parEncAxIfLfLL : Term -> Term
parEncAxIfLfLL payT =
  ap2 Pair tagCode_axIfLfLL payT

parOutAxIfLfLL : Term
parOutAxIfLfLL = reify outAxIfLfLL

parDispAxIfLfLL : (payT : Term) ->
  Deriv (atomic (eqn (ap1 thmT (parEncAxIfLfLL payT)) parOutAxIfLfLL))
parDispAxIfLfLL payT = thmTDispAxIfLfLL_param payT
