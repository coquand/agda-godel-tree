{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.GoedelIIFull
--
-- Unconditional Goedel II: instantiates BRA2.GoedelII.Compose with the
-- concrete  (constr5_final, step5_l)  pair from BRA2.Th14Step5,
-- using  BRA2.Thm12.FromBridges.thm12_F1  /  thm12_F2  for the two
-- Theorem 12 results.
--
-- Output:
--   godelII : Deriv Con -> Deriv bot
--
-- Guard's Goedel II (1963) in BRA: if BRA's consistency  Con  is
-- provable, then BRA's bot is provable.
--
-- ASCII only.  No postulates, no holes.

module BRA2.GoedelIIFull where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Deriv

open import BRA2.Sub using (sub)
open import BRA2.Thm.ThmT using (thmT)
open import BRA2.Thm12 using (Thm12_F1_Result ; Thm12_F2_Result ; module FromBridges)

open import BRA2.GoedelII using (Con ; bot ; module Compose)

import BRA2.Th14Step5

----------------------------------------------------------------------
-- Concrete Theorem 12 results.

r12_th : Thm12_F1_Result thmT
r12_th = FromBridges.thm12_F1 thmT

r12_sub : Thm12_F2_Result sub
r12_sub = FromBridges.thm12_F2 sub

----------------------------------------------------------------------
-- godelII : the unconditional headline result.

module Step5 = BRA2.Th14Step5.Th14Step5 r12_th r12_sub
module Final = Compose Step5.constr5_final Step5.step5_l

godelII : Deriv Con -> Deriv bot
godelII = Final.godelII
