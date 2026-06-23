{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ImpImpEq -- the DOUBLE-lift imp toolkit, shape  Rf => (A => .) , needed for
-- the nested `imp_byCases` dispatch in `certHeadZe_obj` (the inner cascade level
-- runs under BOTH the outer test condition and the accumulated head-equation Rf).
-- Mirrors T4.ImpEq one level up; everything reduces to  impImpMp (S-combinator
-- under Rf) + double  liftP  of the base equational axioms.  No new axioms.
--
--   impImpMp        : Rf=>(A=>(B=>C)) -> Rf=>(A=>B) -> Rf=>(A=>C)
--   impImpCong1 f   : Rf=>(A=>(a=b)) -> Rf=>(A=>(f a = f b))
--   impImpCongR g x : Rf=>(A=>(a=b)) -> Rf=>(A=>(g x a = g x b))
--   impImpSym       : Rf=>(A=>(a=b)) -> Rf=>(A=>(b=a))
--   impImpRuleTrans : Rf=>(A=>(X=Y)) -> Rf=>(A=>(Y=Z)) -> Rf=>(A=>(X=Z))
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.ImpImpEq where

open import T4.Base

open import T4.ImpEq            using ( impMp )
open import BRA3.Contrapositive using ( liftP )

------------------------------------------------------------------------
-- MP under Rf then A (the S-combinator, lifted twice).

impImpMp : (Rf A B Cf : Formula) ->
  Deriv (imp Rf (imp A (imp B Cf))) -> Deriv (imp Rf (imp A B)) ->
  Deriv (imp Rf (imp A Cf))
impImpMp Rf A B Cf h1 h2 = impMp (impMp (liftP Rf (axS A B Cf)) h1) h2

------------------------------------------------------------------------
-- cong1 under Rf then A.

impImpCong1 : (Rf A : Formula) (f : Fun1) {a b : Term} ->
  Deriv (imp Rf (imp A (eqF a b))) ->
  Deriv (imp Rf (imp A (eqF (ap1 f a) (ap1 f b))))
impImpCong1 Rf A f {a} {b} h =
  impImpMp Rf A (eqF a b) (eqF (ap1 f a) (ap1 f b))
    (liftP Rf (liftP A (ax_eqCong1 f a b))) h

------------------------------------------------------------------------
-- congR (second arg of a Fun2) under Rf then A.

impImpCongR : (Rf A : Formula) (g : Fun2) (x : Term) {a b : Term} ->
  Deriv (imp Rf (imp A (eqF a b))) ->
  Deriv (imp Rf (imp A (eqF (ap2 g x a) (ap2 g x b))))
impImpCongR Rf A g x {a} {b} h =
  impImpMp Rf A (eqF a b) (eqF (ap2 g x a) (ap2 g x b))
    (liftP Rf (liftP A (ax_eqCongR g a b x))) h

------------------------------------------------------------------------
-- Symmetry under Rf then A.

impImpSym : (Rf A : Formula) {a b : Term} ->
  Deriv (imp Rf (imp A (eqF a b))) -> Deriv (imp Rf (imp A (eqF b a)))
impImpSym Rf A {a} {b} h =
  impImpMp Rf A (eqF a a) (eqF b a)
    (impImpMp Rf A (eqF a b) (imp (eqF a a) (eqF b a))
      (liftP Rf (liftP A (ax_eqTrans a b a))) h)
    (liftP Rf (liftP A (axRefl a)))

------------------------------------------------------------------------
-- Transitivity under Rf then A.

impImpRuleTrans : (Rf A : Formula) {X Y Z : Term} ->
  Deriv (imp Rf (imp A (eqF X Y))) -> Deriv (imp Rf (imp A (eqF Y Z))) ->
  Deriv (imp Rf (imp A (eqF X Z)))
impImpRuleTrans Rf A {X} {Y} {Z} h1 h2 =
  impImpMp Rf A (eqF Y Z) (eqF X Z)
    (impImpMp Rf A (eqF Y X) (imp (eqF Y Z) (eqF X Z))
      (liftP Rf (liftP A (ax_eqTrans Y X Z))) (impImpSym Rf A h1))
    h2
