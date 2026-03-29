{-# OPTIONS --safe --without-K --exact-split #-}

module Rose.Reify where

open import Rose.Base using (Nat; zero; Eq; refl; eqCong2)
open import Rose.Tree using (Tree; lf; nd)
open import Rose.Term using (Term; leaf; pair)
open import Rose.Eval using (eval)

------------------------------------------------------------------------
-- Reification: embed a tree as a closed term.
--
-- This is the analogue of Rose's nu(x), which gives the numeral
-- (object-level representation) for the number x.  In our setting,
-- since the data type IS binary trees, reification is the canonical
-- injection Tree -> Term 0.
--
-- Note: reify only produces leaf and pair terms.  It never produces
-- cas or rec.  This matters for the round-trip property below.

reify : Tree -> Term zero
reify lf       = leaf
reify (nd a b) = pair (reify a) (reify b)

------------------------------------------------------------------------
-- Round-trip: eval . reify = id
--
-- This holds because reify produces only leaf/pair, and eval on
-- those is the inverse.

eval-reify : (t : Tree) -> Eq (eval (reify t)) t
eval-reify lf       = refl
eval-reify (nd a b) = eqCong2 nd (eval-reify a) (eval-reify b)

------------------------------------------------------------------------
-- Note: the reverse round-trip (reify . eval = id) does NOT hold
-- for general terms with cas/rec.  For example:
--   eval (cas leaf leaf (pair (var fz) (var (fs fz)))) = lf
--   reify lf = leaf
-- but the original term is not leaf.
--
-- However, eval (reify (eval t)) = eval t always holds, as an
-- immediate consequence of eval-reify.
