{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.Parts.AxIfLfL
--
-- Proof-code vocabulary for
--   axIfLfL : Deriv (ap2 IfLf O (ap2 Pair a b) = a) .

module BRA.Thm.Parts.AxIfLfL where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Thm.Tag using (tagAxIfLfL)

encAxIfLfL : Term -> Term -> Tree
encAxIfLfL a b = nd (natCode tagAxIfLfL) (nd (code a) (code b))

outAxIfLfL : Term -> Term -> Tree
outAxIfLfL a b = codeFormula (atomic (eqn (ap2 IfLf O (ap2 Pair a b)) a))
