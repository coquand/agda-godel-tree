{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm.Parts.AxIfLfNL
--
-- Proof-code vocabulary for safe-default axiom
--   axIfLfNL : (x y : Term) -> Deriv (ap2 IfLf (ap2 Pair x y) O = O) .

module BRA2.Thm.Parts.AxIfLfNL where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Thm.Tag using (tagAxIfLfNL)

encAxIfLfNL : Term -> Term -> Tree
encAxIfLfNL x y = nd (natCode tagAxIfLfNL) (nd (code x) (code y))

outAxIfLfNL : Term -> Term -> Tree
outAxIfLfNL x y = codeFormula (atomic (eqn (ap2 IfLf (ap2 Pair x y) O) O))
