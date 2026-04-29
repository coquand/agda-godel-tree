{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.Parts.AxS
--
-- Proof-code vocabulary for Guard's Ax 12 (S):
--   axS : Deriv ((P imp (Q imp R)) imp ((P imp Q) imp (P imp R))) .

module BRA.Thm.Parts.AxS where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Thm.Tag using (tagAxS)

encAxS : Formula -> Formula -> Formula -> Tree
encAxS P Q R = nd (natCode tagAxS)
                  (nd (codeFormula P)
                      (nd (codeFormula Q) (codeFormula R)))

outAxS : Formula -> Formula -> Formula -> Tree
outAxS P Q R = codeFormula ((P imp (Q imp R)) imp ((P imp Q) imp (P imp R)))
