{-# OPTIONS --safe --without-K --exact-split #-}

module BRA2.Thm12.Param.AxFstLf where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Deriv
open import BRA2.Thm.Parts.AxFstLf using (outAxFstLf)
open import BRA2.Thm.ThmT
  using ( thmT ; tagCode_axFstLf ; thmTDispAxFstLf_param )

parEncAxFstLf : Term -> Term
parEncAxFstLf payT =
  ap2 Pair tagCode_axFstLf payT

parOutAxFstLf : Term
parOutAxFstLf = reify outAxFstLf

parDispAxFstLf : (payT : Term) ->
  Deriv (atomic (eqn (ap1 thmT (parEncAxFstLf payT)) parOutAxFstLf))
parDispAxFstLf payT = thmTDispAxFstLf_param payT
