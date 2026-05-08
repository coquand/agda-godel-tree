{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm.Parts.AxExFalso
--
-- Proof-code vocabulary for ex falso quodlibet:
--   axExFalso : Deriv (P imp ((not P) imp Q)) .

module BRA2.Thm.Parts.AxExFalso where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Thm.Tag using (tagAxExFalso)

encAxExFalso : Formula -> Formula -> Tree
encAxExFalso P Q = nd (natCode tagAxExFalso)
                      (nd (codeFormula P) (codeFormula Q))

outAxExFalso : Formula -> Formula -> Tree
outAxExFalso P Q = codeFormula (P imp ((not P) imp Q))
