{-# OPTIONS --safe --without-K --exact-split #-}

module Rose.Term where

open import Rose.Base using (Nat; zero; suc; Fin; fz; fs)

------------------------------------------------------------------------
-- Intrinsically scoped terms over binary trees.
--
-- Primitive basis:
--   leaf, pair  -- constructors
--   cas         -- case analysis (2 binders: left, right subtree)
--   rec         -- primitive tree recursion (4 binders)
--
-- This is the analogue of Rose's functors (o, i, s, K, R', C', R, Cp).

data Term : Nat -> Set where
  var  : {n : Nat} -> Fin n -> Term n
  leaf : {n : Nat} -> Term n
  pair : {n : Nat} -> Term n -> Term n -> Term n
  cas  : {n : Nat} -> Term n -> Term n -> Term (suc (suc n)) -> Term n
  rec  : {n : Nat} -> Term n -> Term n -> Term (suc (suc (suc (suc n)))) -> Term n
  niter : {n : Nat} -> Term n -> Term n -> Term (suc (suc n)) -> Term n

------------------------------------------------------------------------
-- Computation rules (intended):
--
-- cas leaf       u v  -->  u
-- cas (pair a b) u v  -->  v[b/0, a/1]
--
-- rec leaf       z s  -->  z
-- rec (pair a b) z s  -->  s[rec b z s/0, rec a z s/1, b/2, a/3]
--
-- Binding convention for cas step (v):
--   var 0 = right subtree  (b)
--   var 1 = left subtree   (a)
--
-- Binding convention for rec step (s):
--   var 0 = recursive result on right  (rec b z s)
--   var 1 = recursive result on left   (rec a z s)
--   var 2 = right subtree              (b)
--   var 3 = left subtree               (a)
--   var (4+k) = outer variable k
--
-- niter t state step: iterate step along the right spine of t,
-- threading state through.
--
-- Computation rules:
--   niter lf       state step  -->  state
--   niter (nd a k) state step  -->  niter k (step[k/0, state/1]) step
--
-- Binding convention for niter step:
--   var 0 = remaining tail     (k, right subtree of current node)
--   var 1 = current state
--   var (2+k) = outer variable k
