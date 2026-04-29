{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.Parts.AxRecLf
--
-- Proof-code vocabulary for
--   axRecLf : Deriv (ap1 (Rec z s) O = z) .

module BRA.Thm.Parts.AxRecLf where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Thm.Tag using (tagAxRecLf)

encAxRecLf : Term -> Fun2 -> Tree
encAxRecLf z s = nd (natCode tagAxRecLf) (nd (code z) (codeF2 s))

outAxRecLf : Term -> Fun2 -> Tree
outAxRecLf z s = codeFormula (atomic (eqn (ap1 (Rec z s) O) z))
