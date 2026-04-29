{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.Parts.AxEqCongL
--
-- Proof-code vocabulary for the binary left equality-congruence axiom (Guard Ax 6):
--   axEqCongL : Deriv ((atomic (eqn a b))
--                        imp (atomic (eqn (ap2 g a c) (ap2 g b c)))) .

module BRA.Thm.Parts.AxEqCongL where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Thm.Tag using (tagAxEqCongL)

encAxEqCongL : Fun2 -> Term -> Term -> Term -> Tree
encAxEqCongL g a b c = nd (natCode tagAxEqCongL)
                          (nd (codeF2 g)
                              (nd (code a)
                                  (nd (code b) (code c))))

outAxEqCongL : Fun2 -> Term -> Term -> Term -> Tree
outAxEqCongL g a b c = codeFormula ((atomic (eqn a b))
                                      imp (atomic (eqn (ap2 g a c) (ap2 g b c))))
