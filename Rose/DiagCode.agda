{-# OPTIONS --safe --without-K --exact-split #-}

module Rose.DiagCode where

open import Rose.Base
  using (Nat; zero; suc; Eq; refl; eqSym; eqTrans; eqCong; eqCong2; eqSubst)
open import Rose.Tree using (Tree; lf; nd)
open import Rose.Term using (Term; var; leaf; pair; cas; rec; niter)
open import Rose.Code using (codeTerm; tagLeaf; tagPair)
open import Rose.Reify using (reify; eval-reify)
open import Rose.Eval using (eval; evalEnv; emptyEnv)
open import Rose.SubstAt using (substAt; substAt0; injectTerm)
open import Rose.CodedSubst using (codedSubst0)
open import Rose.CodedSubstCorrect using (codedSubst0-correct)

------------------------------------------------------------------------
-- codeReify: compute codeTerm (reify t) directly on trees.
--
-- reify lf       = leaf         , codeTerm leaf       = nd tagLeaf lf
-- reify (nd a b) = pair (reify a) (reify b)
-- codeTerm (pair s t) = nd tagPair (nd (codeTerm s) (codeTerm t))
--
-- So:
--   codeReify lf       = nd tagLeaf lf
--   codeReify (nd a b) = nd tagPair (nd (codeReify a) (codeReify b))

codeReify : Tree -> Tree
codeReify lf       = nd tagLeaf lf
codeReify (nd a b) = nd tagPair (nd (codeReify a) (codeReify b))

-- Correctness: codeReify t = codeTerm (reify t)

codeReify-correct : (t : Tree) -> Eq (codeReify t) (codeTerm (reify t))
codeReify-correct lf       = refl
codeReify-correct (nd a b) =
  eqCong2 (\ x y -> nd tagPair (nd x y))
    (codeReify-correct a)
    (codeReify-correct b)

------------------------------------------------------------------------
-- diagCode: the Guard-style diagonal on codes.
--
-- Given a tree c (intended to be the code of a Term 1),
-- compute the code of the result of substituting reify(c) for var 0.
--
-- This is Guard's sub(i,i): substitute the numeral of i into i itself.

diagCode : Tree -> Tree
diagCode c = codedSubst0 (codeReify c) c

------------------------------------------------------------------------
-- diagCode-correct: for any t : Term 1,
--
--   diagCode (codeTerm t) = codeTerm (substAt0 (reify (codeTerm t)) t)
--
-- Proof:
--   diagCode (codeTerm t)
--     = codedSubst0 (codeReify (codeTerm t)) (codeTerm t)
--       { by definition }
--     = codedSubst0 (codeTerm (reify (codeTerm t))) (codeTerm t)
--       { by codeReify-correct (codeTerm t) }
--     = codeTerm (substAt fz (reify (codeTerm t)) t)
--       { by codedSubst0-correct }
--     = codeTerm (substAt0 (reify (codeTerm t)) t)
--       { by definition of substAt0 }

diagCode-correct :
  (t : Term (suc zero)) ->
  Eq (diagCode (codeTerm t))
     (codeTerm (substAt0 (reify (codeTerm t)) t))
diagCode-correct t =
  eqSubst
    (\ x -> Eq (codedSubst0 x (codeTerm t))
                (codeTerm (substAt0 (reify (codeTerm t)) t)))
    (eqSym (codeReify-correct (codeTerm t)))
    (codedSubst0-correct (reify (codeTerm t)) t)

------------------------------------------------------------------------
-- Evaluation form: eval of the diagonalized term.
--
-- If we decode diagCode (codeTerm t) back to a term and eval it,
-- we get evalEnv [codeTerm t] t  (by the substitution lemma).
--
-- More precisely, using eval-reify:
--   eval (substAt0 (reify (codeTerm t)) t)
--     = evalEnv [eval (reify (codeTerm t))] t
--     = evalEnv [codeTerm t] t
--
-- This is the semantic content of the fixed point.
-- (Proved via EvalSubst.eval-substAt externally if needed.)

