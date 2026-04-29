{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.Parts.AxKT
--
-- Encoding for axZ (the new primitive replacing axKT in the 2026-04-26
-- refactor).  Filename retained for git-history continuity; the file
-- now contains encAxZ / outAxZ.
--
--   axZ x : Deriv (ap1 Z x = O)
--
-- Tag tagAxKT is reused for axZ.

module BRA.Thm.Parts.AxKT where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Thm.Tag using (tagAxKT)

encAxZ : Term -> Tree
encAxZ x = nd (natCode tagAxKT) (nd (codeF1 Z) (code x))

outAxZ : Term -> Tree
outAxZ x = codeFormula (atomic (eqn (ap1 Z x) O))
