{-# OPTIONS --safe --without-K --exact-split #-}

module BRA.Thm12.Param.AxSndLf where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Thm.Parts.AxSndLf using (outAxSndLf)
open import BRA.Thm.ThmT
  using ( thmT ; tagCode_axSndLf ; thmTDispAxSndLf_param )

parEncAxSndLf : Term -> Term
parEncAxSndLf payT =
  ap2 Pair tagCode_axSndLf payT

parOutAxSndLf : Term
parOutAxSndLf = reify outAxSndLf

parDispAxSndLf : (payT : Term) ->
  Deriv (atomic (eqn (ap1 thmT (parEncAxSndLf payT)) parOutAxSndLf))
parDispAxSndLf payT = thmTDispAxSndLf_param payT
