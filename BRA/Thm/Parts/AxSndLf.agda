{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.Parts.AxSndLf
--
-- Proof-code vocabulary for safe-default axiom
--   axSndLf : Deriv (ap1 Snd O = O) .

module BRA.Thm.Parts.AxSndLf where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Thm.Tag using (tagAxSndLf)

encAxSndLf : Tree
encAxSndLf = nd (natCode tagAxSndLf) lf

outAxSndLf : Tree
outAxSndLf = codeFormula (atomic (eqn (ap1 Snd O) O))
