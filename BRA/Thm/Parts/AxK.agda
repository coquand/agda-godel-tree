{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.Parts.AxK
--
-- Proof-code vocabulary for the propositional axiom
--   axK : Deriv (P imp (Q imp P))  (P, Q : Formula).

module BRA.Thm.Parts.AxK where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Thm.Tag using (tagAxK)

encAxK : Formula -> Formula -> Tree
encAxK P Q = nd (natCode tagAxK) (nd (codeFormula P) (codeFormula Q))

outAxK : Formula -> Formula -> Tree
outAxK P Q = codeFormula (P imp (Q imp P))
