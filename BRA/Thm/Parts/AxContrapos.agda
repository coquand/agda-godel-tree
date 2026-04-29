{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.Parts.AxContrapos
--
-- Proof-code vocabulary for classical contraposition:
--   axContrapos : Deriv ((P imp Q) imp ((not Q) imp (not P))) .

module BRA.Thm.Parts.AxContrapos where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Thm.Tag using (tagAxContrapos)

encAxContrapos : Formula -> Formula -> Tree
encAxContrapos P Q = nd (natCode tagAxContrapos)
                        (nd (codeFormula P) (codeFormula Q))

outAxContrapos : Formula -> Formula -> Tree
outAxContrapos P Q = codeFormula ((P imp Q) imp ((not Q) imp (not P)))
