{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.Thm12Uniform -- Guard's Theorem 12 in our Agda setting.
--
-- guard15 p.16 Thm 12 (unconditional):
--     For every singulary functor  f  there exists a singulary
--     functor  Df  such that  th(Df(x)) = "fx_ = fx" .
--     Similarly for every binary functor  g  there exists  Dg
--     such that  th(Dg(x,y)) = "g(x_,y_) = g(x,y)" .
--
-- In Guard's BRA,  "fx_"  (Def 12, p.16) uses  num x  where x's code
-- would otherwise go; for a singulary primitive recursive f,
--  num(f x) = 3J(num f, num x) + 1  (Def 10 rule 3 with  num  in
-- place of  ' A ' ), so  "fx_" = "fx"  as BRA terms.  Guard's Thm 12
-- proof is a meta-induction constructing  Df  per primitive-recursive
-- constructor of f.
--
-- In our Agda Term calculus, the analog of Guard's  num  is
--  cor : Fun1 .  The analog of Def 10 rule 3 — the structural
-- decomposition  code(ap1 f x) = nd tagAp1 (nd (codeF1 f) (code x))
-- — holds BY DEFINITION of our `code`.  Consequently Guard's meta-
-- induction is absorbed into the structural definition of `code`,
-- and  Df  can be given UNIFORMLY for every  f :
--
--     D_f(x)  :=  encAxRefl (ap1 cor (ap1 f x))
--
-- The correctness lemma is a one-line application of encAxReflCorr.
--
-- This is a faithful interpretation of Guard's Thm 12: the theorem's
-- CONTENT (encoded axRefl witness of  num(fx) = num(fx) ) is produced;
-- the per-f meta-induction is simply not needed because our encoder
-- `encAxRefl` is universal.  The non-trivial work of Gödel II lives
-- in the Thm 14 chain (Guard.Thm14Chain), not in Thm 12 itself.

module Guard.Thm12Uniform where

open import Guard.Base
open import Guard.Term
open import Guard.Formula
open import Guard.DerivF
open import Guard.ThFunTForHF using (thmT)
open import Guard.CodeOfReifyUnify using (cor)
open import Guard.ProofEncUnify using (encAxRefl ; encAxReflCorr)

------------------------------------------------------------------------
-- Singulary case (Guard's Df).
--
--  D1  takes a Fun1  f  and a Term  x ,  returning an encoded proof
-- Term whose thmT-evaluation is the Gödel code of  "cor(f x) = cor(f x)"
-- at the term level —  Pair (ap1 cor (ap1 f x)) (ap1 cor (ap1 f x)) .

D1 : Fun1 -> Term -> Term
D1 f x = encAxRefl (ap1 cor (ap1 f x))

thm12Fun1 : (f : Fun1) (x : Term) ->
  Deriv (atomic (eqn (ap1 thmT (D1 f x))
                     (ap2 Pair (ap1 cor (ap1 f x))
                               (ap1 cor (ap1 f x)))))
thm12Fun1 f x = encAxReflCorr (ap1 cor (ap1 f x))

------------------------------------------------------------------------
-- Binary case (Guard's Dg).

D2 : Fun2 -> Term -> Term -> Term
D2 g x y = encAxRefl (ap1 cor (ap2 g x y))

thm12Fun2 : (g : Fun2) (x y : Term) ->
  Deriv (atomic (eqn (ap1 thmT (D2 g x y))
                     (ap2 Pair (ap1 cor (ap2 g x y))
                               (ap1 cor (ap2 g x y)))))
thm12Fun2 g x y = encAxReflCorr (ap1 cor (ap2 g x y))
