{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.Parts.AxLift
--
-- Proof-code vocabulary for
--   axLift : Deriv (ap2 (Lift f) a b = ap1 f a) .

module BRA.Thm.Parts.AxLift where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Thm.Tag using (tagAxLift)

encAxLift : Fun1 -> Term -> Term -> Tree
encAxLift f a b = nd (natCode tagAxLift)
                     (nd (codeF1 f)
                         (nd (code a) (code b)))

outAxLift : Fun1 -> Term -> Term -> Tree
outAxLift f a b = codeFormula (atomic (eqn (ap2 (Lift f) a b) (ap1 f a)))
