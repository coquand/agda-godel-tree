{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.Parts.AxTreeEqLN
--
-- Proof-code vocabulary for
--   axTreeEqLN : Deriv (ap2 TreeEq O (ap2 Pair a b) = ap2 Pair O O) .

module BRA.Thm.Parts.AxTreeEqLN where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Thm.Tag using (tagAxTreeEqLN)

encAxTreeEqLN : Term -> Term -> Tree
encAxTreeEqLN a b = nd (natCode tagAxTreeEqLN) (nd (code a) (code b))

outAxTreeEqLN : Term -> Term -> Tree
outAxTreeEqLN a b =
  codeFormula (atomic (eqn (ap2 TreeEq O (ap2 Pair a b)) (ap2 Pair O O)))
