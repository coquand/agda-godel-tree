{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.Parts.AxSnd
--
-- Proof-code vocabulary for
--   axSnd : Deriv (ap1 Snd (ap2 Pair a b) = b) .

module BRA.Thm.Parts.AxSnd where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Thm.Tag using (tagAxSnd)

encAxSnd : Term -> Term -> Tree
encAxSnd a b = nd (natCode tagAxSnd) (nd (code a) (code b))

outAxSnd : Term -> Term -> Tree
outAxSnd a b = codeFormula (atomic (eqn (ap1 Snd (ap2 Pair a b)) b))
