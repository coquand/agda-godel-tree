{-# OPTIONS --safe --without-K --exact-split #-}

-- Rose/Chi.agda
-- Nelson's chi-translation for binary tree arithmetic.
--
-- Formulas are translated to characteristic terms:
--   chi[a = b]   evaluates to lf (true) when eval a = eval b
--   chi[not A]   swaps lf and falseT
--   chi[A or B]  lf when either is lf
--   chi[A -> B]  = chi[not A or B]
--
-- The fundamental property: chi(A) = lf iff A holds.

module Rose.Chi where

open import Rose.Base
  using (Nat; zero; suc; Fin; fz; fs;
         Eq; refl; eqSym; eqTrans; eqCong; eqCong2; eqSubst;
         Empty; emptyElim; Unit; tt)
open import Rose.Tree using (Tree; lf; nd)
open import Rose.Term using (Term; var; leaf; pair; cas; rec; niter)
open import Rose.Eval
  using (Env; emptyEnv; extEnv; eval; evalEnv)
open import Rose.TreeEq using (trueT; falseT; eqTree; eqTree-refl; eqTree-sound)

------------------------------------------------------------------------
-- Truth values: trueT = lf, falseT = nd lf lf (from TreeEq).

-- Metalevel boolean operations on truth values.

chiNotMeta : Tree -> Tree
chiNotMeta lf = falseT
chiNotMeta (nd a b) = trueT

chiOrMeta : Tree -> Tree -> Tree
chiOrMeta lf b = trueT
chiOrMeta (nd a b) y = y

chiImpMeta : Tree -> Tree -> Tree
chiImpMeta a b = chiOrMeta (chiNotMeta a) b

------------------------------------------------------------------------
-- Term-level chi connectives.
--
-- These are Term n combinators: given characteristic terms for
-- sub-formulas, produce characteristic terms for the connective.

-- chi(not A): if A = lf, return falseT; if A = nd, return trueT.
chiNot : {n : Nat} -> Term n -> Term n
chiNot a = cas a (pair leaf leaf) leaf

-- chi(A or B): check A first, then B.
-- Problem: cas a trueBody falseBody where falseBody : Term (n+2).
-- We need b in the nd branch which has scope +2. Since b : Term n,
-- we can't directly use it. Instead: evaluate both and combine.
-- Use: cas a leaf (cas b leaf (pair leaf leaf))
-- Wait, same issue. The clean solution: compute both a and b
-- first (as a pair), then dispatch.
-- Simplest: pair a b, then cas on first, then on second.
-- Or: use the metalevel observation that chiOr only matters for
-- truth values. If a = lf: return lf. If a = nd ..: return b.
-- At the term level: use niter trick or pair+cas.
--
-- Actually, the simplest encoding: eqTree-based.
-- chiOr a b = chiNot (chiAnd (chiNot a) (chiNot b))
-- = not (not-a and not-b) = a or b (De Morgan).
-- But this requires chiAnd which has the same issue.
--
-- The real fix: use pair to compute both, then dispatch.
-- pair a b evaluates to nd (eval a) (eval b).
-- Then: cas (pair a b) ... dispatches on the pair.
-- If eval a = lf: pair = nd lf (eval b). Always nd. Go to nd branch.
-- Hmm, pair always gives nd, so cas always takes the nd branch.
--
-- Simplest correct encoding:
-- chiOr a b: "a = lf or b = lf"
-- = cas a leaf (chiNot (chiNot b))  -- if a=lf: true. if a=nd: b.
-- But chiNot (chiNot b) requires b in scope n, and we're in scope n+2.
--
-- The fundamental issue: cas adds 2 variables in the nd branch,
-- and b : Term n can't be used at Term (n+2) without weakening.
--
-- Solution: define chiOr at the METALEVEL only, or use a different
-- term structure. For now, define metalevel-only versions and use
-- matchSub for the term level.

-- chi(A or B): if A = lf, return trueT; otherwise return B.
-- Encoding: cas (chiNot a) b leaf.
-- When chiNot a = lf (a is false): cas takes lf branch, returns b.
-- When chiNot a = nd (a is true): cas takes nd branch, returns leaf = lf = trueT.
-- No weakening needed: leaf in the nd branch works at any scope.
chiOr : {n : Nat} -> Term n -> Term n -> Term n
chiOr a b = cas (chiNot a) b leaf

-- chi(A -> B) = chi(not A or B)
chiImp : {n : Nat} -> Term n -> Term n -> Term n
chiImp a b = chiOr (chiNot a) b

-- chi(A and B): if A = lf, return B; otherwise falseT.
chiAnd : {n : Nat} -> Term n -> Term n -> Term n
chiAnd a b = cas a b (pair leaf leaf)

------------------------------------------------------------------------
-- Correctness of the metalevel operations.

chiNotMeta-correct-t : Eq (chiNotMeta trueT) falseT
chiNotMeta-correct-t = refl

chiNotMeta-correct-f : Eq (chiNotMeta falseT) trueT
chiNotMeta-correct-f = refl

chiOrMeta-correct-tt : Eq (chiOrMeta trueT trueT) trueT
chiOrMeta-correct-tt = refl

chiOrMeta-correct-tf : Eq (chiOrMeta trueT falseT) trueT
chiOrMeta-correct-tf = refl

chiOrMeta-correct-ft : Eq (chiOrMeta falseT trueT) trueT
chiOrMeta-correct-ft = refl

chiOrMeta-correct-ff : Eq (chiOrMeta falseT falseT) falseT
chiOrMeta-correct-ff = refl

chiImpMeta-correct-tt : Eq (chiImpMeta trueT trueT) trueT
chiImpMeta-correct-tt = refl

chiImpMeta-correct-tf : Eq (chiImpMeta trueT falseT) falseT
chiImpMeta-correct-tf = refl

chiImpMeta-correct-ft : Eq (chiImpMeta falseT trueT) trueT
chiImpMeta-correct-ft = refl

chiImpMeta-correct-ff : Eq (chiImpMeta falseT falseT) trueT
chiImpMeta-correct-ff = refl

------------------------------------------------------------------------
-- Term-level correctness: the cas-based terms compute the metalevel
-- operations when evaluated.

open import Rose.Eval using (Env; evalEnv; evalCas; extEnv2)

chiNot-eval : {n : Nat} -> (env : Env n) -> (a : Term n) ->
  Eq (evalEnv env (chiNot a)) (chiNotMeta (evalEnv env a))
chiNot-eval env a = chiNot-helper (evalEnv env a)
  where
  chiNot-helper : (v : Tree) ->
    Eq (evalCas env v (pair leaf leaf) leaf) (chiNotMeta v)
  chiNot-helper lf = refl
  chiNot-helper (nd x y) = refl

chiOr-eval : {n : Nat} -> (env : Env n) -> (a b : Term n) ->
  Eq (evalEnv env (chiOr a b)) (chiOrMeta (evalEnv env a) (evalEnv env b))
chiOr-eval env a b = chiOr-helper (evalEnv env a) (evalEnv env (chiNot a))
                       (chiNot-eval env a)
  where
  chiOr-helper : (va : Tree) -> (vna : Tree) ->
    Eq vna (chiNotMeta va) ->
    Eq (evalCas env vna b leaf) (chiOrMeta va (evalEnv env b))
  chiOr-helper lf vna eq = eqSubst
    (\ z -> Eq (evalCas env z b leaf) (chiOrMeta lf (evalEnv env b)))
    (eqSym eq) refl
  chiOr-helper (nd x y) vna eq = eqSubst
    (\ z -> Eq (evalCas env z b leaf) (chiOrMeta (nd x y) (evalEnv env b)))
    (eqSym eq) refl

chiAndMeta : Tree -> Tree -> Tree
chiAndMeta lf b' = b'
chiAndMeta (nd x y) b' = falseT

chiAnd-eval : {n : Nat} -> (env : Env n) -> (a b : Term n) ->
  Eq (evalEnv env (chiAnd a b)) (chiAndMeta (evalEnv env a) (evalEnv env b))
chiAnd-eval env a b = chiAnd-helper (evalEnv env a)
  where
  chiAnd-helper : (v : Tree) ->
    Eq (evalCas env v b (pair leaf leaf)) (chiAndMeta v (evalEnv env b))
  chiAnd-helper lf = refl
  chiAnd-helper (nd x y) = refl

chiImp-eval : {n : Nat} -> (env : Env n) -> (a b : Term n) ->
  Eq (evalEnv env (chiImp a b)) (chiImpMeta (evalEnv env a) (evalEnv env b))
chiImp-eval env a b =
  eqTrans (chiOr-eval env (chiNot a) b)
    (eqCong (\ x -> chiOrMeta x (evalEnv env b)) (chiNot-eval env a))

------------------------------------------------------------------------
-- chiProv: characteristic term for "thS(y) = A" (parameterized by y).
--
-- This is a Term 1 where v0 = the proof tree candidate y.
-- Evaluates to lf when thS(y) equals the target code A.

open import Rose.TreeEq using (matchSub)
open import Rose.ThInt using (thTerm)

chiProvAt : Tree -> Term (suc zero)
chiProvAt target = matchSub target thTerm

-- chiProvAt target evaluated at y = eqTree(thS(y), target).
-- By matchSub-correct and thTerm-correct.

------------------------------------------------------------------------
-- The chi-translation is now in place:
--
--   Equations:    eqTree (eval s) (eval t)     [metalevel]
--                 matchSub target scrut         [term-level]
--
--   Negation:     chiNot                        [term-level]
--   Disjunction:  chiOr                         [term-level]
--   Implication:  chiImp                        [term-level]
--   Conjunction:  chiAnd                        [term-level]
--
--   Provability:  chiProvAt target              [Term 1, open in y]
--
-- The remaining question: can we close chiProvAt over y?
-- That requires bounded existential search over proof trees.
-- Nelson uses mu_A (bounded minimization) for this.
-- In our setting: niter over an enumeration of trees up to a bound.
