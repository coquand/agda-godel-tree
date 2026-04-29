{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.Parts.AxExFalso
--
-- Proof-code vocabulary for ex falso quodlibet:
--   axExFalso : Deriv (P imp ((not P) imp Q)) .

module BRA.Thm.Parts.AxExFalso where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Thm.Tag using (tagAxExFalso)

encAxExFalso : Formula -> Formula -> Tree
encAxExFalso P Q = nd (natCode tagAxExFalso)
                      (nd (codeFormula P) (codeFormula Q))

outAxExFalso : Formula -> Formula -> Tree
outAxExFalso P Q = codeFormula (P imp ((not P) imp Q))
