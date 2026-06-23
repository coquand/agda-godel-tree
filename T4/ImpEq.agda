{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ImpEq -- the small Carneiro imp-lifting toolkit for EQUATIONAL reasoning
-- under a fixed antecedent  Rf , needed to assemble the object head-stability
-- dispatch (certHeadZe_obj) where `byCases`/`imp_byCases` force imp-form.
--
--   impMp       : imp Rf (imp A B) -> imp Rf A -> imp Rf B        (MP under Rf, via axS)
--   impCong1    : imp Rf (a=b) -> imp Rf (f a = f b)              (cong1 under Rf)
--   impSym      : imp Rf (a=b) -> imp Rf (b=a)                    (ruleSym under Rf)
--   impRuleTrans: imp Rf (X=Y) -> imp Rf (Y=Z) -> imp Rf (X=Z)    (ruleTrans under Rf)
--
-- All from the primitive  axS / ax_eqTrans / ax_eqCong1 / axRefl + liftP +
-- impTrans -- no new axioms.  No holes, no postulates, no termination warnings;
-- --safe --without-K --exact-split.

module T4.ImpEq where

open import T4.Base

open import BRA3.Logic          using ( impTrans )
open import BRA3.Contrapositive using ( liftP )

------------------------------------------------------------------------
-- MP under a fixed antecedent  Rf  (the S-combinator).

impMp : {Rf A B : Formula} ->
        Deriv (imp Rf (imp A B)) -> Deriv (imp Rf A) -> Deriv (imp Rf B)
impMp {Rf} {A} {B} h1 h2 = mp (mp (axS Rf A B) h1) h2

------------------------------------------------------------------------
-- cong1 under Rf:  compose with the congruence axiom.

impCong1 : {Rf : Formula} (f : Fun1) {a b : Term} ->
           Deriv (imp Rf (eqF a b)) ->
           Deriv (imp Rf (eqF (ap1 f a) (ap1 f b)))
impCong1 {Rf} f {a} {b} h = impTrans h (ax_eqCong1 f a b)

------------------------------------------------------------------------
-- congR (second arg of a Fun2) under Rf.

impCongR : {Rf : Formula} (g : Fun2) (x : Term) {a b : Term} ->
           Deriv (imp Rf (eqF a b)) ->
           Deriv (imp Rf (eqF (ap2 g x a) (ap2 g x b)))
impCongR {Rf} g x {a} {b} h = impTrans h (ax_eqCongR g a b x)

------------------------------------------------------------------------
-- Symmetry under Rf.  ax_eqTrans a b a : (a=b)->(a=a)->(b=a).

impSym : {Rf : Formula} {a b : Term} ->
         Deriv (imp Rf (eqF a b)) -> Deriv (imp Rf (eqF b a))
impSym {Rf} {a} {b} h =
  impMp (impMp (liftP Rf (ax_eqTrans a b a)) h) (liftP Rf (axRefl a))

------------------------------------------------------------------------
-- Transitivity under Rf.  ax_eqTrans Y X Z : (Y=X)->(Y=Z)->(X=Z).

impRuleTrans : {Rf : Formula} {X Y Z : Term} ->
               Deriv (imp Rf (eqF X Y)) -> Deriv (imp Rf (eqF Y Z)) ->
               Deriv (imp Rf (eqF X Z))
impRuleTrans {Rf} {X} {Y} {Z} h1 h2 =
  impMp (impMp (liftP Rf (ax_eqTrans Y X Z)) (impSym h1)) h2
