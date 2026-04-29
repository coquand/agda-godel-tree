{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.Parts.AxIfLfLL
--
-- Proof-code vocabulary for safe-default axiom
--   axIfLfLL : Deriv (ap2 IfLf O O = O) .

module BRA.Thm.Parts.AxIfLfLL where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Thm.Tag using (tagAxIfLfLL)

encAxIfLfLL : Tree
encAxIfLfLL = nd (natCode tagAxIfLfLL) lf

outAxIfLfLL : Tree
outAxIfLfLL = codeFormula (atomic (eqn (ap2 IfLf O O) O))
