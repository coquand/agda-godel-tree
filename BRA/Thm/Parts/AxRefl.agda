{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.Parts.AxRefl
--
-- Proof-code vocabulary for
--   axRefl : Deriv (atomic (eqn t t)) .

module BRA.Thm.Parts.AxRefl where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Thm.Tag using (tagAxRefl)

encAxRefl : Term -> Tree
encAxRefl t = nd (natCode tagAxRefl) (code t)

outAxRefl : Term -> Tree
outAxRefl t = codeFormula (atomic (eqn t t))
