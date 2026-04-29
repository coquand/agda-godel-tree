{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.Parts.AxRecNd
--
-- Proof-code vocabulary for
--   axRecNd : Deriv (ap1 (Rec z s) (ap2 Pair a b)
--                     =  ap2 s (ap2 Pair a b)
--                              (ap2 Pair (ap1 (Rec z s) a) (ap1 (Rec z s) b))) .

module BRA.Thm.Parts.AxRecNd where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Thm.Tag using (tagAxRecNd)

encAxRecNd : Term -> Fun2 -> Term -> Term -> Tree
encAxRecNd z s a b = nd (natCode tagAxRecNd)
                        (nd (code z)
                            (nd (codeF2 s)
                                (nd (code a) (code b))))

outAxRecNd : Term -> Fun2 -> Term -> Term -> Tree
outAxRecNd z s a b =
  codeFormula (atomic (eqn (ap1 (Rec z s) (ap2 Pair a b))
                           (ap2 s (ap2 Pair a b)
                                  (ap2 Pair (ap1 (Rec z s) a)
                                            (ap1 (Rec z s) b)))))
