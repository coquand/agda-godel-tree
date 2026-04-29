{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.Parts.AxTreeEqLL
--
-- Proof-code vocabulary for the 0-arg primitive
--   axTreeEqLL : Deriv (ap2 TreeEq O O = O) .
--
-- Encoding has no payload (the primitive takes no arguments).

module BRA.Thm.Parts.AxTreeEqLL where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Thm.Tag using (tagAxTreeEqLL)

encAxTreeEqLL : Tree
encAxTreeEqLL = nd (natCode tagAxTreeEqLL) lf

outAxTreeEqLL : Tree
outAxTreeEqLL = codeFormula (atomic (eqn (ap2 TreeEq O O) O))
