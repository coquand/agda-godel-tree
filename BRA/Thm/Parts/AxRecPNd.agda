{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.Parts.AxRecPNd
--
-- Proof-code vocabulary for
--   axRecPNd : Deriv (ap2 (RecP s) p (ap2 Pair a b)
--                       =  ap2 s (ap2 Pair p (ap2 Pair a b))
--                                (ap2 Pair (ap2 (RecP s) p a)
--                                          (ap2 (RecP s) p b))) .

module BRA.Thm.Parts.AxRecPNd where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Thm.Tag using (tagAxRecPNd)

encAxRecPNd : Fun2 -> Term -> Term -> Term -> Tree
encAxRecPNd s p a b = nd (natCode tagAxRecPNd)
                         (nd (codeF2 s)
                             (nd (code p)
                                 (nd (code a) (code b))))

outAxRecPNd : Fun2 -> Term -> Term -> Term -> Tree
outAxRecPNd s p a b =
  codeFormula (atomic (eqn (ap2 (RecP s) p (ap2 Pair a b))
                           (ap2 s (ap2 Pair p (ap2 Pair a b))
                                  (ap2 Pair (ap2 (RecP s) p a)
                                            (ap2 (RecP s) p b)))))
