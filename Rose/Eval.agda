{-# OPTIONS --safe --without-K --exact-split #-}

module Rose.Eval where

open import Rose.Base using (Nat; zero; suc; Fin; fz; fs; Eq; refl)
open import Rose.Tree using (Tree; lf; nd)
open import Rose.Term using (Term; var; leaf; pair; cas; rec; niter)
open import Rose.Equation using (Equation; equation)

------------------------------------------------------------------------
-- Environments: assignment of trees to variables.

Env : Nat -> Set
Env n = Fin n -> Tree

emptyEnv : Env zero
emptyEnv ()

------------------------------------------------------------------------
-- Extending environments.

extEnv : {n : Nat} -> Env n -> Tree -> Env (suc n)
extEnv env v fz     = v
extEnv env v (fs i) = env i

-- Extend by two values (for cas step).
-- var 0 = b (right), var 1 = a (left)
extEnv2 : {n : Nat} -> Env n -> Tree -> Tree -> Env (suc (suc n))
extEnv2 env a b fz          = b
extEnv2 env a b (fs fz)     = a
extEnv2 env a b (fs (fs i)) = env i

-- Extend by four values (for rec step).
-- var 0 = rb, var 1 = ra, var 2 = b, var 3 = a
extEnv4 : {n : Nat} -> Env n -> Tree -> Tree -> Tree -> Tree
        -> Env (suc (suc (suc (suc n))))
extEnv4 env a b ra rb fz                    = rb
extEnv4 env a b ra rb (fs fz)               = ra
extEnv4 env a b ra rb (fs (fs fz))          = b
extEnv4 env a b ra rb (fs (fs (fs fz)))     = a
extEnv4 env a b ra rb (fs (fs (fs (fs i)))) = env i

------------------------------------------------------------------------
-- Environment-based evaluation.
--
-- evalEnv is structurally recursive on the Term argument.
-- evalCas and evalRec are structurally recursive on the Tree argument
-- (the result of evaluating the scrutinee).
--
-- The mutual recursion terminates because every cycle through the
-- call graph strictly decreases the Term argument:
--   evalEnv[rec t z s] -> evalRec[z,s] -> evalEnv[s]
-- and s is a strict subterm of (rec t z s).
--
-- This is the analogue of Rose's vo(x,y): the valuation of term y
-- under valuation x.

mutual

  evalEnv : {n : Nat} -> Env n -> Term n -> Tree
  evalEnv env (var i)     = env i
  evalEnv env leaf        = lf
  evalEnv env (pair t u)  = nd (evalEnv env t) (evalEnv env u)
  evalEnv env (cas t u v) = evalCas env (evalEnv env t) u v
  evalEnv env (rec t z s) = evalRec env (evalEnv env t) z s
  evalEnv env (niter t st s) = evalNiter env (evalEnv env t) (evalEnv env st) s

  evalCas : {n : Nat} -> Env n -> Tree
          -> Term n -> Term (suc (suc n)) -> Tree
  evalCas env lf       u v = evalEnv env u
  evalCas env (nd a b) u v = evalEnv (extEnv2 env a b) v

  evalRec : {n : Nat} -> Env n -> Tree
          -> Term n -> Term (suc (suc (suc (suc n)))) -> Tree
  evalRec env lf       z s = evalEnv env z
  evalRec env (nd a b) z s =
    evalEnv (extEnv4 env a b (evalRec env a z s) (evalRec env b z s)) s

  evalNiter : {n : Nat} -> Env n -> Tree -> Tree
            -> Term (suc (suc n)) -> Tree
  evalNiter env lf       state s = state
  evalNiter env (nd a k) state s =
    evalNiter env k (evalEnv (extEnv2 env state k) s) s

------------------------------------------------------------------------
-- Evaluation of closed terms.

eval : Term zero -> Tree
eval t = evalEnv emptyEnv t

------------------------------------------------------------------------
-- Semantic truth of an equation.
--
-- Analogue of Rose's vl(x,y): equation y is true under valuation x
-- iff vl(x,y) = 0.

TrueEq : Equation -> Set
TrueEq (equation l r) = Eq (eval l) (eval r)
