{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Thm12.ImpHelpers -- Hilbert-lifted helper combinators for the
-- Carneiro lift used in Theorem 12 PartR step case.
--
-- Each helper mirrors an unconditional Deriv combinator with an extra
--  imp P  wrapper around the input/output Derivs, allowing the IH
--  imp P ...  to be threaded through the step proof inside ruleIndNat.
--
-- All helpers are derivable from axS , axK , ax_eqTrans , ax_eqCong1 ,
--  ax_eqCongL , ax_eqCongR  and  axRefl  in BRA3.Deriv.
--
-- Naming note.  BRA3.PairAlgebra already exports an  axI  meaning the
-- Term-level identity equality  eqF (ap1 I t) t .  To avoid clash we
-- name the propositional reflexivity  impRefl  here.
--
-- Public API:
--
--   impRefl  : (P : Formula) -> Deriv (imp P P)
--   impLift  : {P X : Formula} -> Deriv X -> Deriv (imp P X)
--   impMp    : {P A B : Formula} ->
--              Deriv (imp P (imp A B)) -> Deriv (imp P A) -> Deriv (imp P B)
--   impCong1 : {P : Formula} (f : Fun1) (a b : Term) ->
--              Deriv (imp P (eqF a b)) ->
--              Deriv (imp P (eqF (ap1 f a) (ap1 f b)))
--   impCongL : {P : Formula} (g : Fun2) (a b c : Term) ->
--              Deriv (imp P (eqF a b)) ->
--              Deriv (imp P (eqF (ap2 g a c) (ap2 g b c)))
--   impCongR : {P : Formula} (g : Fun2) (a b c : Term) ->
--              Deriv (imp P (eqF a b)) ->
--              Deriv (imp P (eqF (ap2 g c a) (ap2 g c b)))
--   impRuleSym : {P : Formula} {a b : Term} ->
--                Deriv (imp P (eqF a b)) -> Deriv (imp P (eqF b a))
--   impEqTrans : {P : Formula} (a b c : Term) ->
--                Deriv (imp P (eqF a b)) -> Deriv (imp P (eqF b c)) ->
--                Deriv (imp P (eqF a c))

module BRA4.Thm12.ImpHelpers where

open import BRA4.Base
open import BRA3.Logic using ( impTrans ; eqSymImp )

------------------------------------------------------------------------
-- impRefl :  imp P P .  Derived from axS + axK by Smullyan's I = SKK.
--
--   axS P (imp P P) P
--     : imp (imp P (imp (imp P P) P)) (imp (imp P (imp P P)) (imp P P))
--   axK P (imp P P) : imp P (imp (imp P P) P)
--   axK P P         : imp P (imp P P)
--   mp axS axK_1    : imp (imp P (imp P P)) (imp P P)
--   mp ... axK_2    : imp P P .

impRefl : (P : Formula) -> Deriv (imp P P)
impRefl P =
  mp (mp (axS P (imp P P) P) (axK P (imp P P))) (axK P P)

------------------------------------------------------------------------
-- impLift :  axK wrap of an unconditional Deriv.

impLift : {P X : Formula} -> Deriv X -> Deriv (imp P X)
impLift {P} {X} d = mp (axK X P) d

------------------------------------------------------------------------
-- impMp : Hilbert-lifted modus ponens.
--
--   axS P A B            : imp (imp P (imp A B)) (imp (imp P A) (imp P B))
--   mp axS f             : imp (imp P A) (imp P B)
--   mp ... g             : imp P B .

impMp : {P A B : Formula} ->
        Deriv (imp P (imp A B)) -> Deriv (imp P A) -> Deriv (imp P B)
impMp {P} {A} {B} f g = mp (mp (axS P A B) f) g

------------------------------------------------------------------------
-- impCong1 / impCongL / impCongR : Hilbert-lifted congruence rules.
--
-- Pattern:  impMp (impLift <unconditional cong axiom>) <imp-eq input>.

impCong1 : {P : Formula} (f : Fun1) (a b : Term) ->
           Deriv (imp P (eqF a b)) ->
           Deriv (imp P (eqF (ap1 f a) (ap1 f b)))
impCong1 {P} f a b imp_eq = impMp {P} (impLift {P} (ax_eqCong1 f a b)) imp_eq

impCongL : {P : Formula} (g : Fun2) (a b c : Term) ->
           Deriv (imp P (eqF a b)) ->
           Deriv (imp P (eqF (ap2 g a c) (ap2 g b c)))
impCongL {P} g a b c imp_eq = impMp {P} (impLift {P} (ax_eqCongL g a b c)) imp_eq

impCongR : {P : Formula} (g : Fun2) (a b c : Term) ->
           Deriv (imp P (eqF a b)) ->
           Deriv (imp P (eqF (ap2 g c a) (ap2 g c b)))
impCongR {P} g a b c imp_eq = impMp {P} (impLift {P} (ax_eqCongR g a b c)) imp_eq

------------------------------------------------------------------------
-- impRuleSym : Hilbert-lifted symmetry.  Compose with eqSymImp .

impRuleSym : {P : Formula} {a b : Term} ->
             Deriv (imp P (eqF a b)) -> Deriv (imp P (eqF b a))
impRuleSym {P} {a} {b} imp_eq = impTrans imp_eq (eqSymImp a b)

------------------------------------------------------------------------
-- impEqTrans : Hilbert-lifted transitivity over  eqF .
--
-- Strategy.  Given  imp P (a = b)  and  imp P (b = c) , produce
--  imp P (a = c)  by:
--   (a)  flip the first to  imp P (b = a)  via eqSymImp ;
--   (b)  compose with  ax_eqTrans b a c : imp (b = a) (imp (b = c) (a = c)) ;
--   (c)  distribute over  axS  to lift the inner imp and apply the second.

impEqTrans :
  {P : Formula} (a b c : Term) ->
  Deriv (imp P (eqF a b)) -> Deriv (imp P (eqF b c)) -> Deriv (imp P (eqF a c))
impEqTrans {P} a b c f1 f2 =
  let f1_flipped : Deriv (imp P (eqF b a))
      f1_flipped = impTrans f1 (eqSymImp a b)
      lifted : Deriv (imp P (imp (eqF b c) (eqF a c)))
      lifted = impTrans f1_flipped (ax_eqTrans b a c)
      dist : Deriv (imp (imp P (eqF b c)) (imp P (eqF a c)))
      dist = mp (axS P (eqF b c) (eqF a c)) lifted
  in mp dist f2
