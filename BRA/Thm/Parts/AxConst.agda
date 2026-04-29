{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.Parts.AxConst
--
-- Proof-code vocabulary for
--   axConst : Deriv (ap2 Const a b = a) .

module BRA.Thm.Parts.AxConst where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Thm.Tag using (tagAxConst)

encAxConst : Term -> Term -> Tree
encAxConst a b = nd (natCode tagAxConst) (nd (code a) (code b))

outAxConst : Term -> Term -> Tree
outAxConst a b = codeFormula (atomic (eqn (ap2 Const a b) a))
