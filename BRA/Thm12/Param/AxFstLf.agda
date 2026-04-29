{-# OPTIONS --safe --without-K --exact-split #-}

module BRA.Thm12.Param.AxFstLf where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Thm.Parts.AxFstLf using (outAxFstLf)
open import BRA.Thm.ThmT
  using ( thmT ; tagCode_axFstLf ; thmTDispAxFstLf_param )

parEncAxFstLf : Term -> Term
parEncAxFstLf payT =
  ap2 Pair tagCode_axFstLf payT

parOutAxFstLf : Term
parOutAxFstLf = reify outAxFstLf

parDispAxFstLf : (payT : Term) ->
  Deriv (atomic (eqn (ap1 thmT (parEncAxFstLf payT)) parOutAxFstLf))
parDispAxFstLf payT = thmTDispAxFstLf_param payT
