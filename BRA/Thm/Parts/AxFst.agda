{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.Parts.AxFst
--
-- Proof-code vocabulary for the primitive
--   axFst : Deriv (ap1 Fst (ap2 Pair a b) = a) .

module BRA.Thm.Parts.AxFst where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Thm.Tag using (tagAxFst)

encAxFst : Term -> Term -> Tree
encAxFst a b = nd (natCode tagAxFst) (nd (code a) (code b))

outAxFst : Term -> Term -> Tree
outAxFst a b = codeFormula (atomic (eqn (ap1 Fst (ap2 Pair a b)) a))
