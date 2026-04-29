{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.Parts.AxPost
--
-- Proof-code vocabulary for
--   axPost : Deriv (ap2 (Post f h) a b = ap1 f (ap2 h a b)) .

module BRA.Thm.Parts.AxPost where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Thm.Tag using (tagAxPost)

encAxPost : Fun1 -> Fun2 -> Term -> Term -> Tree
encAxPost f h a b = nd (natCode tagAxPost)
                       (nd (codeF1 f)
                           (nd (codeF2 h)
                               (nd (code a) (code b))))

outAxPost : Fun1 -> Fun2 -> Term -> Term -> Tree
outAxPost f h a b = codeFormula (atomic (eqn (ap2 (Post f h) a b)
                                             (ap1 f (ap2 h a b))))
