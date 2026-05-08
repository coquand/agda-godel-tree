{-# OPTIONS --safe --without-K --exact-split #-}

module BRA2.Thm12.Param.AxSndLf where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Deriv
open import BRA2.Thm.Parts.AxSndLf using (outAxSndLf)
open import BRA2.Thm.ThmT
  using ( thmT ; tagCode_axSndLf ; thmTDispAxSndLf_param )

parEncAxSndLf : Term -> Term
parEncAxSndLf payT =
  ap2 Pair tagCode_axSndLf payT

parOutAxSndLf : Term
parOutAxSndLf = reify outAxSndLf

parDispAxSndLf : (payT : Term) ->
  Deriv (atomic (eqn (ap1 thmT (parEncAxSndLf payT)) parOutAxSndLf))
parDispAxSndLf payT = thmTDispAxSndLf_param payT
