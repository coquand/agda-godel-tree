{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm.Parts.AxContrapos
--
-- Proof-code vocabulary for classical contraposition:
--   axContrapos : Deriv ((P imp Q) imp ((not Q) imp (not P))) .

module BRA2.Thm.Parts.AxContrapos where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Thm.Tag using (tagAxContrapos)

encAxContrapos : Formula -> Formula -> Tree
encAxContrapos P Q = nd (natCode tagAxContrapos)
                        (nd (codeFormula P) (codeFormula Q))

outAxContrapos : Formula -> Formula -> Tree
outAxContrapos P Q = codeFormula ((P imp Q) imp ((not Q) imp (not P)))
