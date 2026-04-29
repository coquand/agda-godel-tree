{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.Parts.AxEqCongR
--
-- Proof-code vocabulary for the binary right equality-congruence axiom (Guard Ax 7):
--   axEqCongR : Deriv ((atomic (eqn a b))
--                        imp (atomic (eqn (ap2 g c a) (ap2 g c b)))) .

module BRA.Thm.Parts.AxEqCongR where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Thm.Tag using (tagAxEqCongR)

encAxEqCongR : Fun2 -> Term -> Term -> Term -> Tree
encAxEqCongR g a b c = nd (natCode tagAxEqCongR)
                          (nd (codeF2 g)
                              (nd (code a)
                                  (nd (code b) (code c))))

outAxEqCongR : Fun2 -> Term -> Term -> Term -> Tree
outAxEqCongR g a b c = codeFormula ((atomic (eqn a b))
                                      imp (atomic (eqn (ap2 g c a) (ap2 g c b))))
