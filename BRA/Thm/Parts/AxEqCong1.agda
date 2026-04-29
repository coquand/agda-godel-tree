{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.Parts.AxEqCong1
--
-- Proof-code vocabulary for the unary equality-congruence axiom (Guard Ax 5):
--   axEqCong1 : Deriv ((atomic (eqn a b))
--                        imp (atomic (eqn (ap1 f a) (ap1 f b)))) .

module BRA.Thm.Parts.AxEqCong1 where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Thm.Tag using (tagAxEqCong1)

encAxEqCong1 : Fun1 -> Term -> Term -> Tree
encAxEqCong1 f a b = nd (natCode tagAxEqCong1)
                        (nd (codeF1 f)
                            (nd (code a) (code b)))

outAxEqCong1 : Fun1 -> Term -> Term -> Tree
outAxEqCong1 f a b = codeFormula ((atomic (eqn a b))
                                    imp (atomic (eqn (ap1 f a) (ap1 f b))))
