{-# OPTIONS --safe --without-K --exact-split #-}

module Rose.Axiom where

open import Rose.Base
  using (Nat; zero; suc; Eq; refl; eqSym; eqTrans; eqCong; eqCong2; eqSubst)
open import Rose.Tree using (Tree; lf; nd)
open import Rose.Term using (Term; var; leaf; pair; cas; rec; niter)
open import Rose.Eval
  using (Env; emptyEnv; extEnv2; extEnv4;
         eval; evalEnv; evalCas; evalRec; evalNiter; TrueEq)
open import Rose.Equation using (Equation; equation)
open import Rose.Reify using (reify; eval-reify)
open import Rose.Code using (codeTerm; codeEquation)

------------------------------------------------------------------------
-- Tree projections (Guard's K and L).

treeK : Tree -> Tree
treeK lf       = lf
treeK (nd a b) = a

treeL : Tree -> Tree
treeL lf       = lf
treeL (nd a b) = b

------------------------------------------------------------------------
-- Axiom schemes for B*.
--
-- Each scheme takes Term parameters directly.
-- Soundness is definitional (refl) because eval reduces the LHS
-- to the same thing as eval of the RHS.

------------------------------------------------------------------------
-- Axiom 1: cas-leaf
-- cas leaf u v = u
-- (u : Term 0, v : Term 2)

axCasLeaf : Term zero -> Term (suc (suc zero)) -> Equation
axCasLeaf u v = equation (cas leaf u v) u

axCasLeaf-sound : (u : Term zero) -> (v : Term (suc (suc zero))) ->
  TrueEq (axCasLeaf u v)
axCasLeaf-sound u v = refl

------------------------------------------------------------------------
-- Axiom 2: rec-leaf
-- rec leaf z s = z
-- (z : Term 0, s : Term 4)

axRecLeaf : Term zero -> Term (suc (suc (suc (suc zero)))) -> Equation
axRecLeaf z s = equation (rec leaf z s) z

axRecLeaf-sound : (z : Term zero) ->
  (s : Term (suc (suc (suc (suc zero))))) ->
  TrueEq (axRecLeaf z s)
axRecLeaf-sound z s = refl

------------------------------------------------------------------------
-- Axiom 3: niter-leaf
-- niter leaf st step = st
-- (st : Term 0, step : Term 2)

axNiterLeaf : Term zero -> Term (suc (suc zero)) -> Equation
axNiterLeaf st step = equation (niter leaf st step) st

axNiterLeaf-sound : (st : Term zero) -> (step : Term (suc (suc zero))) ->
  TrueEq (axNiterLeaf st step)
axNiterLeaf-sound st step = refl

------------------------------------------------------------------------
-- Axiom 4: reflexivity
-- t = t

axRefl : Term zero -> Equation
axRefl t = equation t t

axRefl-sound : (t : Term zero) -> TrueEq (axRefl t)
axRefl-sound t = refl

------------------------------------------------------------------------
-- Axiom 5: cas-pair (with reify'd values for scrutinee)
-- cas (pair (reify a) (reify b)) u v = v[b/0, a/1]
--
-- Here a, b : Tree are the values in the scrutinee,
-- u : Term 0, v : Term 2.
-- The RHS is the evaluation result, reified.
--
-- eval lhs = evalCas env (nd (eval(reify a)) (eval(reify b))) u v
--          = evalEnv (extEnv2 env (eval(reify a)) (eval(reify b))) v
-- eval rhs = evalEnv (extEnv2 emptyEnv a b) v  (after reify round-trip)
--
-- These differ by eval(reify a) vs a, so not definitionally equal.
-- We state this axiom using reify on both sides to get definitional eq.

axCasPairVal : Tree -> Tree -> Term (suc (suc zero)) -> Equation
axCasPairVal a b v =
  equation (cas (pair (reify a) (reify b)) leaf v)
           (reify (evalEnv (extEnv2 emptyEnv a b) v))

-- Soundness: transport along eval-reify a and eval-reify b.
-- eval lhs = evalEnv (extEnv2 emptyEnv (eval (reify a)) (eval (reify b))) v
-- eval rhs = eval (reify (evalEnv (extEnv2 emptyEnv a b) v))

abstract

  axCasPairVal-sound : (a b : Tree) -> (v : Term (suc (suc zero))) ->
    TrueEq (axCasPairVal a b v)
  axCasPairVal-sound a b v =
    eqSubst
      (\ x -> Eq (evalEnv (extEnv2 emptyEnv (eval (reify a)) x) v)
                  (eval (reify (evalEnv (extEnv2 emptyEnv a b) v))))
      (eqSym (eval-reify b))
      (eqSubst
        (\ x -> Eq (evalEnv (extEnv2 emptyEnv x b) v)
                    (eval (reify (evalEnv (extEnv2 emptyEnv a b) v))))
        (eqSym (eval-reify a))
        (eqSym (eval-reify (evalEnv (extEnv2 emptyEnv a b) v))))

------------------------------------------------------------------------
-- Axiom 6: rec-pair (with reify'd values)
-- rec (pair (reify a) (reify b)) z s
--   = reify (evalEnv [a, b, rec-a, rec-b] s)

axRecPairVal : Tree -> Tree -> Term zero ->
  Term (suc (suc (suc (suc zero)))) -> Equation
axRecPairVal a b z s =
  equation (rec (pair (reify a) (reify b)) z s)
           (reify (evalEnv (extEnv4 emptyEnv a b
                    (evalRec emptyEnv a z s)
                    (evalRec emptyEnv b z s)) s))

abstract

  axRecPairVal-sound : (a b : Tree) -> (z : Term zero) ->
    (s : Term (suc (suc (suc (suc zero))))) ->
    TrueEq (axRecPairVal a b z s)
  axRecPairVal-sound a b z s =
    eqSubst
      (\ x -> Eq (evalEnv (extEnv4 emptyEnv (eval (reify a)) x
                     (evalRec emptyEnv (eval (reify a)) z s)
                     (evalRec emptyEnv x z s)) s)
                  (eval (reify (evalEnv (extEnv4 emptyEnv a b
                     (evalRec emptyEnv a z s)
                     (evalRec emptyEnv b z s)) s))))
      (eqSym (eval-reify b))
      (eqSubst
        (\ x -> Eq (evalEnv (extEnv4 emptyEnv x b
                       (evalRec emptyEnv x z s)
                       (evalRec emptyEnv b z s)) s)
                    (eval (reify (evalEnv (extEnv4 emptyEnv a b
                       (evalRec emptyEnv a z s)
                       (evalRec emptyEnv b z s)) s))))
        (eqSym (eval-reify a))
        (eqSym (eval-reify (evalEnv (extEnv4 emptyEnv a b
           (evalRec emptyEnv a z s)
           (evalRec emptyEnv b z s)) s))))

------------------------------------------------------------------------
-- Axiom 7: niter-pair (with reify'd values)
-- niter (pair (reify a) (reify k)) st step
--   = reify (evalNiter emptyEnv k (evalEnv [eval st, k] step) step)

axNiterPairVal : Tree -> Tree -> Term zero -> Term (suc (suc zero)) -> Equation
axNiterPairVal a k st step =
  equation (niter (pair (reify a) (reify k)) st step)
           (reify (evalNiter emptyEnv k
              (evalEnv (extEnv2 emptyEnv (eval st) k) step) step))

abstract

  axNiterPairVal-sound : (a k : Tree) -> (st : Term zero) ->
    (step : Term (suc (suc zero))) ->
    TrueEq (axNiterPairVal a k st step)
  axNiterPairVal-sound a k st step =
    eqSubst
      (\ x -> Eq (evalNiter emptyEnv x
                     (evalEnv (extEnv2 emptyEnv (eval st) x) step) step)
                  (eval (reify (evalNiter emptyEnv k
                     (evalEnv (extEnv2 emptyEnv (eval st) k) step) step))))
      (eqSym (eval-reify k))
      (eqSubst
        (\ x -> Eq (evalNiter emptyEnv k
                       (evalEnv (extEnv2 emptyEnv (eval st) k) step) step)
                    (eval (reify (evalNiter emptyEnv k
                       (evalEnv (extEnv2 emptyEnv (eval st) k) step) step))))
        (eqSym (eval-reify a))
        (eqSym (eval-reify (evalNiter emptyEnv k
           (evalEnv (extEnv2 emptyEnv (eval st) k) step) step))))
