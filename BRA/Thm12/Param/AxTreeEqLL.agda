{-# OPTIONS --safe --without-K --exact-split #-}

module BRA.Thm12.Param.AxTreeEqLL where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Thm.Parts.AxTreeEqLL using (outAxTreeEqLL)
open import BRA.Thm.ThmT
  using ( thmT ; tagCode_axTreeEqLL ; thmTDispAxTreeEqLL_param )

parEncAxTreeEqLL : Term -> Term
parEncAxTreeEqLL payT =
  ap2 Pair tagCode_axTreeEqLL payT

parOutAxTreeEqLL : Term
parOutAxTreeEqLL = reify outAxTreeEqLL

parDispAxTreeEqLL : (payT : Term) ->
  Deriv (atomic (eqn (ap1 thmT (parEncAxTreeEqLL payT)) parOutAxTreeEqLL))
parDispAxTreeEqLL payT = thmTDispAxTreeEqLL_param payT
