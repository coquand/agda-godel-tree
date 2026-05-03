{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.Parts.CongR
--
-- Proof-code vocabulary for the binary right congruence rule (recursive, 1 sub-proof):
--   congR : (g : Fun2) (x : Term) -> Deriv (atomic (eqn t u))
--                                  -> Deriv (atomic (eqn (ap2 g x t) (ap2 g x u))) .

module BRA.Thm.Parts.CongR where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Thm.Tag using (tagCongR)

-- New layout (Finding 1): see CongL.
encCongR : Fun2 -> Term -> Tree -> Tree
encCongR g x y_h = nd (natCode tagCongR)
                      (nd (nd (codeF2 g) (code x))
                          y_h)

outCongR : Fun2 -> Term -> Term -> Term -> Tree
outCongR g x t u = codeFormula (atomic (eqn (ap2 g x t) (ap2 g x u)))
