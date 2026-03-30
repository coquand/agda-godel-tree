{-# OPTIONS --safe --without-K --exact-split #-}

module Rose.TreeEq where

open import Rose.Base
  using (Nat; zero; suc; Fin; fz; fs;
         Eq; refl; eqSym; eqTrans; eqCong; eqCong2; eqSubst)
open import Rose.Tree using (Tree; lf; nd)
open import Rose.Term using (Term; var; leaf; pair; cas; rec; niter)
open import Rose.Eval
  using (Env; emptyEnv; extEnv; extEnv2; extEnv4;
         eval; evalEnv; evalCas; evalRec)

------------------------------------------------------------------------
-- Truth values as trees.

trueT : Tree
trueT = lf

falseT : Tree
falseT = nd lf lf

------------------------------------------------------------------------
-- Boolean AND on tree truth values.

andT : Tree -> Tree -> Tree
andT lf y = y
andT (nd a b) y = falseT

------------------------------------------------------------------------
-- Metalevel tree equality test.

eqTree : Tree -> Tree -> Tree
eqTree lf lf = trueT
eqTree lf (nd a b) = falseT
eqTree (nd a b) lf = falseT
eqTree (nd a1 b1) (nd a2 b2) = andT (eqTree a1 a2) (eqTree b1 b2)

------------------------------------------------------------------------
-- Correctness.

eqTree-refl : (t : Tree) -> Eq (eqTree t t) trueT
eqTree-refl lf = refl
eqTree-refl (nd a b) =
  eqSubst (\ x -> Eq (andT x (eqTree b b)) trueT)
    (eqSym (eqTree-refl a))
    (eqSubst (\ x -> Eq (andT trueT x) trueT)
      (eqSym (eqTree-refl b))
      refl)

eqTree-sound : (a b : Tree) -> Eq (eqTree a b) trueT -> Eq a b
eqTree-sound lf lf p = refl
eqTree-sound lf (nd a b) ()
eqTree-sound (nd a b) lf ()
eqTree-sound (nd a1 b1) (nd a2 b2) p =
  eqCong2 nd (eqTree-sound a1 a2 (andFst p)) (eqTree-sound b1 b2 (andSnd p))
  where
    andFst : {x y : Tree} -> Eq (andT x y) trueT -> Eq x trueT
    andFst {lf} {lf} q = refl
    andFst {lf} {nd a b} ()
    andFst {nd a b} ()

    andSnd : {x y : Tree} -> Eq (andT x y) trueT -> Eq y trueT
    andSnd {lf} {lf} q = refl
    andSnd {lf} {nd a b} ()
    andSnd {nd a b} ()

------------------------------------------------------------------------
-- Fin helpers.

v0 : {n : Nat} -> Term (suc n)
v0 = var fz

v1 : {n : Nat} -> Term (suc (suc n))
v1 = var (fs fz)

------------------------------------------------------------------------
-- matchSub : match a term's value against a fixed tree constant.
--
-- matchSub target scrutinee : Term n
--
-- Evaluates to trueT if (eval scrutinee) = target,
--               falseT otherwise.
--
-- Built by structural recursion on the target tree.

matchSub : {n : Nat} -> Tree -> Term n -> Term n
matchSub lf scrut = cas scrut leaf (pair leaf leaf)
matchSub (nd a b) scrut =
  cas scrut
    (pair leaf leaf)         -- scrut = lf: falseT
    -- scrut = nd l r (scope +2): var 0 = r, var 1 = l
    (cas (matchSub a v1)     -- check left matches a
      (matchSub b v0)        -- true: check right matches b
      (pair leaf leaf))      -- false: falseT

------------------------------------------------------------------------
-- matchSub correctness: evaluates to eqTree (eval scrut) target.

abstract

  matchSub-correct : {n : Nat} -> (env : Env n) -> (target : Tree) ->
    (scrut : Term n) ->
    Eq (evalEnv env (matchSub target scrut)) (eqTree (evalEnv env scrut) target)

  matchSub-correct env lf scrut = msLf (evalEnv env scrut)
    where
      msLf : (v : Tree) -> Eq (evalCas env v leaf (pair leaf leaf)) (eqTree v lf)
      msLf lf = refl
      msLf (nd a b) = refl

  matchSub-correct env (nd a b) scrut = msNd env (evalEnv env scrut) a b
    where
      -- Helper: dispatch on the scrutinee value.
      msNd : {m : Nat} -> (env' : Env m) -> (v : Tree) -> (a b : Tree) ->
        Eq (evalCas env' v (pair leaf leaf)
             (cas (matchSub a v1) (matchSub b v0) (pair leaf leaf)))
           (eqTree v (nd a b))
      msNd env' lf a b = refl
      msNd env' (nd l r) a b =
        -- Need: evalCas (extEnv2 env' l r)
        --         (evalEnv (extEnv2 env' l r) (matchSub a v1))
        --         (matchSub b v0) (pair leaf leaf)
        --       = andT (eqTree l a) (eqTree r b)
        --
        -- By IH: evalEnv (extEnv2 env' l r) (matchSub a v1) = eqTree l a
        -- (since v1 in extEnv2 env' l r = l)
        eqSubst
          (\ x -> Eq (evalCas (extEnv2 env' l r) x
                        (matchSub b v0) (pair leaf leaf))
                     (andT (eqTree l a) (eqTree r b)))
          (eqSym (matchSub-correct (extEnv2 env' l r) a v1))
          (msNdInner env' l r a b (eqTree l a))
        where
          -- After substituting the first matchSub result.
          msNdInner : {m : Nat} -> (env' : Env m) ->
            (l r : Tree) -> (a b : Tree) -> (ela : Tree) ->
            Eq (evalCas (extEnv2 env' l r) ela
                  (matchSub b v0) (pair leaf leaf))
               (andT ela (eqTree r b))
          msNdInner env' l r a b lf =
            matchSub-correct (extEnv2 env' l r) b v0
          msNdInner env' l r a b (nd x y) = refl

------------------------------------------------------------------------
-- Unit tests.

mkEnv2 : Tree -> Tree -> Env (suc (suc zero))
mkEnv2 a b fz = b
mkEnv2 a b (fs fz) = a

-- Test: matchSub lf applied to lf = trueT
test1 : Eq (evalEnv (mkEnv2 lf lf) (matchSub lf v0)) trueT
test1 = refl

-- Test: matchSub lf applied to (nd lf lf) = falseT
test2 : Eq (evalEnv (mkEnv2 lf (nd lf lf)) (matchSub lf v0)) falseT
test2 = refl

-- Test: matchSub (nd lf lf) applied to (nd lf lf) = trueT
test3 : Eq (evalEnv (mkEnv2 lf (nd lf lf)) (matchSub (nd lf lf) v0)) trueT
test3 = refl

-- Test: matchSub (nd lf lf) applied to (nd lf (nd lf lf)) = falseT
test4 : Eq (evalEnv (mkEnv2 lf (nd lf (nd lf lf))) (matchSub (nd lf lf) v0)) falseT
test4 = refl

-- Test: matchSub (nd (nd lf lf) lf) applied to (nd (nd lf lf) lf) = trueT
test5 : Eq (evalEnv (mkEnv2 lf (nd (nd lf lf) lf))
            (matchSub (nd (nd lf lf) lf) v0)) trueT
test5 = refl

