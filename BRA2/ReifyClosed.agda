{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.ReifyClosed
--
-- Spec lemma 1 of the Thm 11 gap programme (see BRA/THM11-GAP.md):
-- reify T is a closed term, so subst is identity on it.
--
-- Proof: one induction on Tree.

module BRA2.ReifyClosed where

open import BRA2.Base
open import BRA2.Term

reifyClosed : (T : Term) -> IsValue T -> (x : Nat) (r : Term) ->
              Eq (subst x r T) T
reifyClosed .O                 valO                x r = refl
reifyClosed (ap2 Pair a b)    (valNd .a .b va vb)  x r =
  eqCong2 (ap2 Pair) (reifyClosed a va x r) (reifyClosed b vb x r)
