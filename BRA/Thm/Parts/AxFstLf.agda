{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.Parts.AxFstLf
--
-- Proof-code vocabulary for safe-default axiom
--   axFstLf : Deriv (ap1 Fst O = O) .

module BRA.Thm.Parts.AxFstLf where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Thm.Tag using (tagAxFstLf)

encAxFstLf : Tree
encAxFstLf = nd (natCode tagAxFstLf) lf

outAxFstLf : Tree
outAxFstLf = codeFormula (atomic (eqn (ap1 Fst O) O))
