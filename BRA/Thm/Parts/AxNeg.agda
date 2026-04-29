{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.Parts.AxNeg
--
-- Proof-code vocabulary for Guard's Ax 13 (curried contraposition):
--   axNeg : Deriv ((not P) imp ((not Q) imp (Q imp P))) .

module BRA.Thm.Parts.AxNeg where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Thm.Tag using (tagAxNeg)

encAxNeg : Formula -> Formula -> Tree
encAxNeg P Q = nd (natCode tagAxNeg) (nd (codeFormula P) (codeFormula Q))

outAxNeg : Formula -> Formula -> Tree
outAxNeg P Q = codeFormula ((not P) imp ((not Q) imp (Q imp P)))
