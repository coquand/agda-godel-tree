{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.Parts.AxGoodstein
--
-- Proof-code vocabulary for the tree analog of Goodstein's
-- characteristic equation:
--   axGoodstein : Deriv (ap2 IfLf (ap2 TreeEq a b) (ap2 Pair a O)
--                          =  ap2 IfLf (ap2 TreeEq a b) (ap2 Pair b O)) .

module BRA.Thm.Parts.AxGoodstein where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Thm.Tag using (tagAxGoodstein)

encAxGoodstein : Term -> Term -> Tree
encAxGoodstein a b = nd (natCode tagAxGoodstein) (nd (code a) (code b))

outAxGoodstein : Term -> Term -> Tree
outAxGoodstein a b =
  codeFormula (atomic (eqn (ap2 IfLf (ap2 TreeEq a b) (ap2 Pair a O))
                           (ap2 IfLf (ap2 TreeEq a b) (ap2 Pair b O))))
