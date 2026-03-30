{-# OPTIONS --safe --without-K --exact-split #-}

module Rose.FixedPoint where

open import Rose.Base
  using (Nat; zero; suc; Fin; fz;
         Eq; refl; eqSym; eqTrans; eqCong; eqCong2; eqSubst)
open import Rose.Tree using (Tree; lf; nd)
open import Rose.Term using (Term; var; leaf; pair; cas; rec; niter)
open import Rose.Eval using (eval; evalEnv; emptyEnv; extEnv)
open import Rose.Reify using (reify; eval-reify)
open import Rose.Code using (codeTerm; codeEquation)
open import Rose.SubstAt using (substAt; substAt0)
open import Rose.DiagCode using (diagCode; diagCode-correct; codeReify)
open import Rose.Equation using (Equation; equation)
open import Rose.Eval using (TrueEq)

------------------------------------------------------------------------
-- The diagonal fixed-point construction.
--
-- For any schema A : Term 1 (a term with one free variable),
-- define the diagonalization G : Term 0 by substituting
-- the reified code of A for the free variable.
--
-- G = A[reify(codeTerm A) / 0]
--
-- This is Guard's construction: form the code of A, compute
-- its numeral, and substitute that numeral into A itself.

diag : Term (suc zero) -> Term zero
diag a = substAt0 (reify (codeTerm a)) a

------------------------------------------------------------------------
-- Fixed-point identity (code level):
--
-- codeTerm (diag A) = diagCode (codeTerm A)
--
-- This says: the code of the diagonalized term equals
-- the coded diagonal of A's code.
--
-- Proof: immediate from diagCode-correct.

diag-code : (a : Term (suc zero)) ->
  Eq (codeTerm (diag a)) (diagCode (codeTerm a))
diag-code a = eqSym (diagCode-correct a)

------------------------------------------------------------------------
-- Semantic fixed-point:
--
-- eval (diag A) = evalEnv [codeTerm A] A
--
-- That is, evaluating the diagonalized term gives the same result
-- as evaluating A in an environment where var 0 maps to codeTerm A.
--
-- This follows from eval-substAt and eval-reify.
-- eval (substAt0 (reify c) A)
--   = evalEnv [eval (reify c)] A     (by eval-substAt)
--   = evalEnv [c] A                   (by eval-reify)
-- where c = codeTerm A.
--
-- We state this as a corollary, deferring the full proof to
-- when EvalSubst.eval-substAt is imported.

------------------------------------------------------------------------
-- The Gödel sentence for a given schema.
--
-- Given A : Term 1, define:
--   godelEq A = equation (diag A) (diag A)
--
-- Wait -- this is trivially true (reflexivity). The actual Gödel
-- sentence requires A to express something about provability.
--
-- The real construction: A should be a term such that
--   eval (substAt0 (reify c) A) encodes "c is not provable"
--
-- For now, we provide the diagonal machinery and leave the
-- choice of A to the next stage (where th is internalized).

------------------------------------------------------------------------
-- Example: fixed point with a concrete schema.
--
-- If A = var fz (the identity schema), then:
--   diag A = substAt0 (reify (codeTerm (var fz))) (var fz)
--          = reify (codeTerm (var fz))
--          = reify (nd (nd lf lf) lf)     [tagVar, natCode 0]
--
-- eval (diag A) = nd (nd lf lf) lf
--
-- The fixed point says: codeTerm (diag A) = diagCode (codeTerm (var fz))
-- = codedSubst0 (codeReify (nd (nd lf lf) lf)) (nd (nd lf lf) lf)

diag-example : Eq (diag (var fz)) (reify (nd (nd lf lf) lf))
diag-example = refl

diag-example-eval : Eq (eval (diag (var fz))) (nd (nd lf lf) lf)
diag-example-eval = refl

------------------------------------------------------------------------
-- For the Gödel sentence construction, we need a schema A : Term 1
-- that "talks about provability." In the equational setting:
--
-- A(x) should compute a tree that encodes information about
-- whether x is in the range of th.
--
-- The key equation will be:
--   G = diag A
--   eval G = eval A[reify(codeTerm A) / 0]
--          = (the result of checking provability of codeTerm G)
--
-- Since codeTerm G = diagCode (codeTerm A) by diag-code,
-- and diagCode (codeTerm A) = codedSubst0 (codeReify (codeTerm A)) (codeTerm A),
-- the self-reference is established.

