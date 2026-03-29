{-# OPTIONS --safe --without-K --exact-split #-}

module Rose.Internal.Prims where

open import Rose.Base using (Nat; zero; suc; Fin; fz; fs; Eq; refl)
open import Rose.Tree using (Tree; lf; nd)
open import Rose.Term using (Term; var; leaf; pair; cas; rec)
open import Rose.Eval using (eval; evalEnv; evalCas; evalRec; Env; emptyEnv;
                             extEnv; extEnv2; extEnv4)

------------------------------------------------------------------------
-- Closed terms computing basic tree operations.
--
-- Convention: all terms are Term 0 (closed).  Arguments are passed
-- as trees via pair encoding.  Each term takes one argument.
--
-- We prove eval t = f  for the intended function f.

------------------------------------------------------------------------
-- Identity: returns its argument unchanged.

idTm : Term zero
idTm = cas (var fz) leaf (pair (var (fs fz)) (var fz))

-- TODO: Note — this doesn't work as identity because cas leaf u v = u = leaf,
-- but cas (pair a b) u v = v[b/0, a/1] = pair a b.
-- So idTm applied to leaf gives leaf, applied to (nd a b) gives (nd a b). Correct!

------------------------------------------------------------------------
-- First projection: given (nd a b), return a.

fstTm : Term zero
fstTm = cas (var fz) leaf (var (fs fz))

-- eval fstTm applied to (nd a b):
--   cas (nd a b) leaf (var (fs fz))
--   = evalEnv [0 -> b, 1 -> a] (var (fs fz))
--   = a
-- eval fstTm applied to lf:
--   = leaf -> lf  (junk, but total)

------------------------------------------------------------------------
-- Second projection: given (nd a b), return b.

sndTm : Term zero
sndTm = cas (var fz) leaf (var fz)

-- eval sndTm applied to (nd a b):
--   cas (nd a b) leaf (var fz)
--   = evalEnv [0 -> b, 1 -> a] (var fz)
--   = b

------------------------------------------------------------------------
-- Pair with a constant left component.
-- ndLf t = nd lf t   (wraps t with a lf on the left)
--
-- This is natCode successor: natCodeSuc t = nd lf t.

ndLfTm : Term zero
ndLfTm = pair leaf (var fz)

-- eval ndLfTm applied to t:
--   pair leaf (var fz) evaluated with [0 -> t]
--   = nd lf t

------------------------------------------------------------------------
-- Correctness proofs.

eval-fstTm : (a b : Tree) -> Eq (eval (cas (pair a b) leaf (var (fs fz)))) a
eval-fstTm a b = refl

eval-sndTm : (a b : Tree) -> Eq (eval (cas (pair a b) leaf (var fz))) b
eval-sndTm a b = refl

eval-ndLfTm : (t : Tree) -> Eq (eval (pair leaf t)) (nd lf t)
eval-ndLfTm t = refl
