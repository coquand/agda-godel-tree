{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.ProvableEqLifts -- derived rule-form helpers for the Provable
-- layer.
--
-- Step 4 (and 5) of GUARD-BRA-TEMPLATE.md.  Provides convenient
-- "rule" formulations of the propositional/equality axioms (which
-- live as ⊃-form axioms in Guard.Provable):
--
--   * hypSyll'  -- given (P ⊃ Q) and (Q ⊃ R), get (P ⊃ R).
--   * prRefl    -- a = a from axRefl via fromDeriv.
--   * prSym     -- from a = b, get b = a (via axEqTrans + prRefl).
--   * prTrans   -- from a = b and b = c, get a = c (via axEqTrans + sym).
--   * prCong1   -- from a = b, get f(a) = f(b).
--   * prCongL   -- from a = b, get g(a, c) = g(b, c).
--   * prCongR   -- from a = b, get g(c, a) = g(c, b).
--
-- Each rule is a one-line wrapper of mp + axiom or fromDeriv.
--
-- No postulates, no holes.

module Guard.ProvableEqLifts where

open import Guard.Base
open import Guard.Term
open import Guard.Step using (axRefl)
open import Guard.Formula
open import Guard.Provable
open import Guard.ProvableLemmas

------------------------------------------------------------------------
-- hypSyll' : composition / hypothetical syllogism (rule form).
--
-- From dPQ : Provable hyp (P imp Q) and dQR : Provable hyp (Q imp R),
-- derive Provable hyp (P imp R).
--
-- Derivation: build (axK (Q imp R) P : (Q imp R) imp (P imp (Q imp R))),
-- mp with dQR to get (P imp (Q imp R)), then mp with axS to get
-- ((P imp Q) imp (P imp R)), then mp with dPQ.

hypSyll' : (P Q R : Formula) {hyp : Formula} ->
           Provable hyp (P imp Q) ->
           Provable hyp (Q imp R) ->
           Provable hyp (P imp R)
hypSyll' P Q R dPQ dQR =
  mp (mp (axS P Q R) (mp (axK (Q imp R) P) dQR)) dPQ

------------------------------------------------------------------------
-- Equality rule-form helpers.

-- prRefl : a = a, derived from Step.axRefl via fromDeriv.

prRefl : (a : Term) {hyp : Formula} ->
         Provable hyp (atomic (eqn a a))
prRefl a = fromDeriv (axRefl a)

-- prTrans : from a = b and a = c, derive b = c.  (Note: matches
-- Guard ax 4 form; not the standard "from a=b and b=c get a=c" — for
-- that, use prTrans + prSym.)

prTransLeft : (a b c : Term) {hyp : Formula} ->
              Provable hyp (atomic (eqn a b)) ->
              Provable hyp (atomic (eqn a c)) ->
              Provable hyp (atomic (eqn b c))
prTransLeft a b c dab dac =
  mp (mp (axEqTrans a b c) dab) dac

-- prSym : from a = b, derive b = a.
-- Use prTransLeft with a = b and a = a (via prRefl).

prSym : (a b : Term) {hyp : Formula} ->
        Provable hyp (atomic (eqn a b)) ->
        Provable hyp (atomic (eqn b a))
prSym a b dab = prTransLeft a b a dab (prRefl a)

-- prTrans : standard transitivity.  From a = b and b = c, derive a = c.
-- Via prSym then prTransLeft.

prTrans : (a b c : Term) {hyp : Formula} ->
          Provable hyp (atomic (eqn a b)) ->
          Provable hyp (atomic (eqn b c)) ->
          Provable hyp (atomic (eqn a c))
prTrans a b c dab dbc =
  prTransLeft b a c (prSym a b dab) dbc

-- prCong1 : congruence for unary functor.

prCong1 : (f : Fun1) (a b : Term) {hyp : Formula} ->
          Provable hyp (atomic (eqn a b)) ->
          Provable hyp (atomic (eqn (ap1 f a) (ap1 f b)))
prCong1 f a b dab = mp (axEqCong1 f a b) dab

-- prCongL : congruence for binary functor (left arg).

prCongL : (g : Fun2) (a b c : Term) {hyp : Formula} ->
          Provable hyp (atomic (eqn a b)) ->
          Provable hyp (atomic (eqn (ap2 g a c) (ap2 g b c)))
prCongL g a b c dab = mp (axEqCongL g a b c) dab

-- prCongR : congruence for binary functor (right arg).

prCongR : (g : Fun2) (a b c : Term) {hyp : Formula} ->
          Provable hyp (atomic (eqn a b)) ->
          Provable hyp (atomic (eqn (ap2 g c a) (ap2 g c b)))
prCongR g a b c dab = mp (axEqCongR g a b c) dab
