{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.Parts.AxTreeEqNN
--
-- Proof-code vocabulary for
--   axTreeEqNN : Deriv (ap2 TreeEq (ap2 Pair a1 a2) (ap2 Pair b1 b2)
--                         =  ap2 IfLf (ap2 TreeEq a1 b1)
--                                     (ap2 Pair (ap2 TreeEq a2 b2)
--                                               (ap2 Pair O O))) .

module BRA.Thm.Parts.AxTreeEqNN where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Thm.Tag using (tagAxTreeEqNN)

encAxTreeEqNN : Term -> Term -> Term -> Term -> Tree
encAxTreeEqNN a1 a2 b1 b2 = nd (natCode tagAxTreeEqNN)
                               (nd (code a1)
                                   (nd (code a2)
                                       (nd (code b1) (code b2))))

outAxTreeEqNN : Term -> Term -> Term -> Term -> Tree
outAxTreeEqNN a1 a2 b1 b2 =
  codeFormula (atomic (eqn (ap2 TreeEq (ap2 Pair a1 a2) (ap2 Pair b1 b2))
                           (ap2 IfLf (ap2 TreeEq a1 b1)
                                     (ap2 Pair (ap2 TreeEq a2 b2)
                                               (ap2 Pair O O)))))
