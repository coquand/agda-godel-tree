{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.Parts.CongL
--
-- Proof-code vocabulary for the binary left congruence rule (recursive, 1 sub-proof):
--   congL : (g : Fun2) (x : Term) -> Deriv (atomic (eqn t u))
--                                  -> Deriv (atomic (eqn (ap2 g t x) (ap2 g u x))) .

module BRA.Thm.Parts.CongL where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Thm.Tag using (tagCongL)

-- Payload order: y_h sits in the inner-pair head so that  Fst (reify y_h)
-- = Pair O (...) holds for any sub-proof encoding.  This lets the
-- second-level inner-pair distribution discharge cleanly via  y_h 's
-- shape proof (provided by  encodeRich ).  Putting  code x  first
-- would block distribution when  x = O  (since  reify (code O) = Pair O O
-- has  Fst = O ).
encCongL : Fun2 -> Term -> Tree -> Tree
encCongL g x y_h = nd (natCode tagCongL)
                      (nd (codeF2 g)
                          (nd y_h (code x)))

outCongL : Fun2 -> Term -> Term -> Term -> Tree
outCongL g x t u = codeFormula (atomic (eqn (ap2 g t x) (ap2 g u x)))
