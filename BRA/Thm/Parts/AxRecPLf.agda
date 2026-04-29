{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.Parts.AxRecPLf
--
-- Proof-code vocabulary for
--   axRecPLf : Deriv (ap2 (RecP s) p O = O) .

module BRA.Thm.Parts.AxRecPLf where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Thm.Tag using (tagAxRecPLf)

encAxRecPLf : Fun2 -> Term -> Tree
encAxRecPLf s p = nd (natCode tagAxRecPLf) (nd (codeF2 s) (code p))

outAxRecPLf : Fun2 -> Term -> Tree
outAxRecPLf s p = codeFormula (atomic (eqn (ap2 (RecP s) p O) O))
