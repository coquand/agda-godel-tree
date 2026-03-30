{-# OPTIONS --safe --without-K --exact-split #-}

module Rose.TreeEqInt where

open import Rose.Base
  using (Nat; zero; suc; Fin; fz; fs;
         Eq; refl; eqSym; eqTrans; eqCong; eqCong2; eqSubst)
open import Rose.Tree using (Tree; lf; nd)
open import Rose.Term using (Term; var; leaf; pair; cas; rec; niter)
open import Rose.Eval
  using (Env; emptyEnv; extEnv; extEnv2; extEnv4;
         eval; evalEnv; evalCas; evalRec; evalNiter)
open import Rose.TreeEq using (trueT; falseT; andT; eqTree)

------------------------------------------------------------------------
-- Var helpers.

v0 : {n : Nat} -> Term (suc n)
v0 = var fz

v1 : {n : Nat} -> Term (suc (suc n))
v1 = var (fs fz)

v2 : {n : Nat} -> Term (suc (suc (suc n)))
v2 = var (fs (fs fz))

v3 : {n : Nat} -> Term (suc (suc (suc (suc n))))
v3 = var (fs (fs (fs fz)))

v4 : {n : Nat} -> Term (suc (suc (suc (suc (suc n)))))
v4 = var (fs (fs (fs (fs fz))))

v5 : {n : Nat} -> Term (suc (suc (suc (suc (suc (suc n))))))
v5 = var (fs (fs (fs (fs (fs fz)))))

------------------------------------------------------------------------
-- Part 1: linearize term.

linearizeTerm : {n : Nat} -> Term n -> Term n
linearizeTerm t =
  rec t leaf (pair leaf (niter v1 v0 (pair leaf v1)))

------------------------------------------------------------------------
-- Part 2: processStep term.

processStep : {n : Nat} -> Term (suc (suc n))
processStep =
  cas v1                  -- dispatch on state (scope +2)
    leaf                  -- state = lf
    (cas v1               -- state=nd flag stack (+4): dispatch on flag
      (cas v0             -- flag=lf: dispatch on stack
        (pair leaf leaf)  -- stack=lf: done
        (cas v1           -- stack=nd pair rest (+6): dispatch on pair
          (pair (pair leaf leaf) v0)  -- pair=lf: fail
          (cas v1         -- pair=nd a b (+8): dispatch on a
            (cas v0       -- a=lf: dispatch on b
              (pair leaf v2)            -- b=lf: match, nd lf rest
              (pair (pair leaf leaf) v4))  -- b=nd: fail
            (cas v2       -- a=nd a1 a2 (+10): dispatch on b (shifted)
              (pair (pair leaf leaf) v4)   -- b=lf: fail
              (pair leaf                   -- b=nd b1 b2 (+12): push
                (pair (pair v3 v1)         -- nd a1 b1
                  (pair (pair v2 v0)       -- nd a2 b2
                    (var (fs (fs (fs (fs (fs (fs fz))))))))))))))  -- rest=v6
      (pair (pair leaf leaf) v2))  -- flag=nd: nd falseT stack (v2=stack shifted)

------------------------------------------------------------------------
-- Part 3: eqTreeTerm.

eqTreeTerm : Term (suc (suc zero))
eqTreeTerm =
  cas (niter (linearizeTerm (pair v1 v0))
        (pair leaf (pair (pair v1 v0) leaf))
        processStep)
    leaf
    v1

------------------------------------------------------------------------
-- Metalevel functions matching the term computations.

appendR : Tree -> Tree -> Tree
appendR lf ys = ys
appendR (nd a xs) ys = nd lf (appendR xs ys)

linearize : Tree -> Tree
linearize lf = lf
linearize (nd a b) = nd lf (appendR (linearize a) (linearize b))

process : Tree -> Tree
process lf = lf
process (nd lf lf) = nd lf lf
process (nd lf (nd lf rest)) = nd falseT rest
process (nd lf (nd (nd a b) rest)) = processAB a b rest
  where
    processAB : Tree -> Tree -> Tree -> Tree
    processAB lf lf rest' = nd lf rest'
    processAB lf (nd b1 b2) rest' = nd falseT rest'
    processAB (nd a1 a2) lf rest' = nd falseT rest'
    processAB (nd a1 a2) (nd b1 b2) rest' =
      nd lf (nd (nd a1 b1) (nd (nd a2 b2) rest'))
process (nd (nd x y) stack) = nd falseT stack

runNiter : Tree -> Tree -> Tree
runNiter lf state = state
runNiter (nd a k) state = runNiter k (process state)

extractFlagMeta : Tree -> Tree
extractFlagMeta lf = lf
extractFlagMeta (nd flag stack) = flag

runNiter-false : (clock stack : Tree) ->
  Eq (runNiter clock (nd falseT stack)) (nd falseT stack)
runNiter-false lf stack = refl
runNiter-false (nd a k) stack = runNiter-false k stack

runNiter-append : (xs ys state : Tree) ->
  Eq (runNiter (appendR xs ys) state) (runNiter ys (runNiter xs state))
runNiter-append lf ys state = refl
runNiter-append (nd a xs) ys state = runNiter-append xs ys (process state)

------------------------------------------------------------------------
-- Evaluation lemma 1: niter with (pair leaf v1) step = appendR.

-- appendR-shift: appendR c (nd lf s) = nd lf (appendR c s).
appendR-shift : (c s : Tree) -> Eq (appendR c (nd lf s)) (nd lf (appendR c s))
appendR-shift lf s = refl
appendR-shift (nd x k) s = eqCong (nd lf) (appendR-shift k s)

niterAppendR : {n : Nat} -> (env : Env n) -> (clock state : Tree) ->
  Eq (evalNiter env clock state (pair leaf v1)) (appendR clock state)
niterAppendR env lf state = refl
niterAppendR env (nd a k) state =
  eqTrans (niterAppendR env k (nd lf state)) (appendR-shift k state)

------------------------------------------------------------------------
-- Evaluation lemma 2: linearizeTerm evaluation = metalevel linearize.

linearize-eval : {n : Nat} -> (env : Env n) -> (t : Tree) ->
  Eq (evalRec env t leaf (pair leaf (niter v1 v0 (pair leaf v1))))
     (linearize t)
linearize-eval env lf = refl
linearize-eval env (nd a b) =
  eqCong (nd lf)
    (eqTrans (niterAppendR _ (evalRec env a leaf
                (pair leaf (niter v1 v0 (pair leaf v1))))
               (evalRec env b leaf
                (pair leaf (niter v1 v0 (pair leaf v1)))))
             (eqCong2 appendR (linearize-eval env a) (linearize-eval env b)))

------------------------------------------------------------------------
-- Evaluation lemma 3: niter with processStep = runNiter.
-- evalNiter env clock state processStep = runNiter clock state.
--
-- The key: for each constructor pattern of state, one processStep
-- evaluation step reduces to process state (definitionally).

niter-eval : {n : Nat} -> (env : Env n) -> (clock state : Tree) ->
  Eq (evalNiter env clock state processStep) (runNiter clock state)
niter-eval env lf state = refl
niter-eval env (nd a k) lf = niter-eval env k lf
niter-eval env (nd a k) (nd lf lf) = niter-eval env k (nd lf lf)
niter-eval env (nd a k) (nd lf (nd lf rest)) = niter-eval env k (nd falseT rest)
niter-eval env (nd a k) (nd lf (nd (nd a' b') rest)) =
  niter-eval-AB env a k a' b' rest
  where
    niter-eval-AB : {m : Nat} -> (env' : Env m) ->
      (a0 : Tree) -> (k0 : Tree) ->
      (a' b' rest : Tree) ->
      Eq (evalNiter env' k0
            (evalEnv (extEnv2 env' (nd lf (nd (nd a' b') rest)) k0) processStep)
            processStep)
         (runNiter k0 (process (nd lf (nd (nd a' b') rest))))
    niter-eval-AB env' a0 k0 lf lf rest = niter-eval env' k0 (nd lf rest)
    niter-eval-AB env' a0 k0 lf (nd b1 b2) rest = niter-eval env' k0 (nd falseT rest)
    niter-eval-AB env' a0 k0 (nd a1 a2) lf rest = niter-eval env' k0 (nd falseT rest)
    niter-eval-AB env' a0 k0 (nd a1 a2) (nd b1 b2) rest =
      niter-eval env' k0 (nd lf (nd (nd a1 b1) (nd (nd a2 b2) rest)))
niter-eval env (nd a k) (nd (nd lf lf) stack) = niter-eval env k (nd falseT stack)
niter-eval env (nd a k) (nd (nd lf (nd c d)) stack) = niter-eval env k (nd falseT stack)
niter-eval env (nd a k) (nd (nd (nd c d) e) stack) = niter-eval env k (nd falseT stack)

------------------------------------------------------------------------
-- Evaluation lemma 4: extractFlag evaluation = extractFlagMeta.

extractFlag-eval : {n : Nat} -> (env : Env n) -> (t : Tree) ->
  Eq (evalCas env t leaf v1) (extractFlagMeta t)
extractFlag-eval env lf = refl
extractFlag-eval env (nd flag stack) = refl

------------------------------------------------------------------------
-- Unit tests.

mkEnv2 : Tree -> Tree -> Env (suc (suc zero))
mkEnv2 a b fz = b
mkEnv2 a b (fs fz) = a

evalEq : Tree -> Tree -> Tree
evalEq a b = evalEnv (mkEnv2 a b) eqTreeTerm

test1 : Eq (evalEq lf lf) trueT
test1 = refl

test2 : Eq (evalEq lf (nd lf lf)) falseT
test2 = refl

test3 : Eq (evalEq (nd lf lf) lf) falseT
test3 = refl

test4 : Eq (evalEq (nd lf lf) (nd lf lf)) trueT
test4 = refl

test5 : Eq (evalEq (nd lf lf) (nd lf (nd lf lf))) falseT
test5 = refl

test6 : Eq (evalEq (nd (nd lf lf) lf) (nd (nd lf lf) lf)) trueT
test6 = refl

test7 : Eq (evalEq (nd (nd lf lf) (nd lf lf))
                   (nd (nd lf lf) (nd lf lf))) trueT
test7 = refl

test8 : Eq (evalEq (nd (nd lf lf) (nd lf lf))
                   (nd (nd lf lf) (nd lf (nd lf lf)))) falseT
test8 = refl

test9 : Eq (evalEq (nd (nd lf (nd lf lf)) (nd lf lf))
                   (nd (nd lf (nd lf lf)) (nd lf lf))) trueT
test9 = refl

test10 : Eq (evalEq (nd (nd lf (nd lf lf)) (nd lf lf))
                    (nd (nd lf (nd lf lf)) (nd (nd lf lf) lf))) falseT
test10 = refl

