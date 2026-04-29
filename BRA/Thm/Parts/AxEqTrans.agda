{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.Parts.AxEqTrans
--
-- Proof-code vocabulary for the equality transitivity axiom (Guard Ax 4):
--   axEqTrans : Deriv (atomic (eqn a b)
--                       imp ((atomic (eqn a c))
--                             imp (atomic (eqn b c)))) .

module BRA.Thm.Parts.AxEqTrans where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Thm.Tag using (tagAxEqTrans)

encAxEqTrans : Term -> Term -> Term -> Tree
encAxEqTrans a b c = nd (natCode tagAxEqTrans)
                        (nd (code a)
                            (nd (code b) (code c)))

outAxEqTrans : Term -> Term -> Term -> Tree
outAxEqTrans a b c = codeFormula ((atomic (eqn a b))
                                    imp ((atomic (eqn a c))
                                          imp (atomic (eqn b c))))
