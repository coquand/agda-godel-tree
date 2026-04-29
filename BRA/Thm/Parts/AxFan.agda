{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.Parts.AxFan
--
-- Proof-code vocabulary for
--   axFan : Deriv (ap2 (Fan h1 h2 h) a b = ap2 h (ap2 h1 a b) (ap2 h2 a b)) .

module BRA.Thm.Parts.AxFan where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Thm.Tag using (tagAxFan)

encAxFan : Fun2 -> Fun2 -> Fun2 -> Term -> Term -> Tree
encAxFan h1 h2 h a b = nd (natCode tagAxFan)
                          (nd (codeF2 h1)
                              (nd (codeF2 h2)
                                  (nd (codeF2 h)
                                      (nd (code a) (code b)))))

outAxFan : Fun2 -> Fun2 -> Fun2 -> Term -> Term -> Tree
outAxFan h1 h2 h a b =
  codeFormula (atomic (eqn (ap2 (Fan h1 h2 h) a b)
                           (ap2 h (ap2 h1 a b) (ap2 h2 a b))))
