{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm.Parts.AxNeg
--
-- Proof-code vocabulary for Guard's Ax 13 (Lukasiewicz CCNpNqCqp form):
--   axNeg : Deriv (((not P) imp (not Q)) imp (Q imp P)) .

module BRA2.Thm.Parts.AxNeg where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Thm.Tag using (tagAxNeg)

encAxNeg : Formula -> Formula -> Tree
encAxNeg P Q = nd (natCode tagAxNeg) (nd (codeFormula P) (codeFormula Q))

outAxNeg : Formula -> Formula -> Tree
outAxNeg P Q = codeFormula (((not P) imp (not Q)) imp (Q imp P))
