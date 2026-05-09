{-# OPTIONS --safe --without-K --exact-split #-}

module BRA2.Thm12.Param.AxTreeEqLL where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.DerivThreshold
open import BRA2.Thm.Parts.AxTreeEqLL using (outAxTreeEqLL)
open import BRA2.Thm.ThmT
  using ( thmT ; tagCode_axTreeEqLL ; thmTDispAxTreeEqLL_param )

parEncAxTreeEqLL : Term -> Term
parEncAxTreeEqLL payT =
  ap2 Pair tagCode_axTreeEqLL payT

parOutAxTreeEqLL : Term
parOutAxTreeEqLL = reify outAxTreeEqLL

parDispAxTreeEqLL : (payT : Term) ->
  Deriv (atomic (eqn (ap1 thmT (parEncAxTreeEqLL payT)) parOutAxTreeEqLL))
parDispAxTreeEqLL payT = thmTDispAxTreeEqLL_param payT
