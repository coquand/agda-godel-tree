{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.Parts.AxIfLfN
--
-- Proof-code vocabulary for
--   axIfLfN : Deriv (ap2 IfLf (ap2 Pair x y) (ap2 Pair a b) = b) .

module BRA.Thm.Parts.AxIfLfN where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Thm.Tag using (tagAxIfLfN)

encAxIfLfN : Term -> Term -> Term -> Term -> Tree
encAxIfLfN x y a b = nd (natCode tagAxIfLfN)
                        (nd (code x)
                            (nd (code y)
                                (nd (code a) (code b))))

outAxIfLfN : Term -> Term -> Term -> Term -> Tree
outAxIfLfN x y a b = codeFormula (atomic (eqn (ap2 IfLf (ap2 Pair x y)
                                                         (ap2 Pair a b))
                                                b))
