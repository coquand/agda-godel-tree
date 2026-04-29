{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.Parts.AxTreeEqNL
--
-- Proof-code vocabulary for
--   axTreeEqNL : Deriv (ap2 TreeEq (ap2 Pair a b) O = ap2 Pair O O) .

module BRA.Thm.Parts.AxTreeEqNL where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Thm.Tag using (tagAxTreeEqNL)

encAxTreeEqNL : Term -> Term -> Tree
encAxTreeEqNL a b = nd (natCode tagAxTreeEqNL) (nd (code a) (code b))

outAxTreeEqNL : Term -> Term -> Tree
outAxTreeEqNL a b =
  codeFormula (atomic (eqn (ap2 TreeEq (ap2 Pair a b) O) (ap2 Pair O O)))
