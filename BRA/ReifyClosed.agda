{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.ReifyClosed
--
-- Spec lemma 1 of the Thm 11 gap programme (see BRA/THM11-GAP.md):
-- reify T is a closed term, so subst is identity on it.
--
-- Proof: one induction on Tree.

module BRA.ReifyClosed where

open import BRA.Base
open import BRA.Term

reifyClosed : (T : Tree) (x : Nat) (r : Term) ->
              Eq (subst x r (reify T)) (reify T)
reifyClosed lf       x r = refl
reifyClosed (nd a b) x r =
  -- subst x r (ap2 Pair (reify a) (reify b))
  --   = ap2 Pair (subst x r (reify a)) (subst x r (reify b))
  --   by IH twice -> ap2 Pair (reify a) (reify b) = reify (nd a b).
  eqCong2 (ap2 Pair) (reifyClosed a x r) (reifyClosed b x r)
