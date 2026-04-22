{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.ProvableSound -- soundness of the Provable layer wrt Deriv.
--
-- The propositional Provable layer (Guard.Provable) sits above the
-- equational Deriv (Guard.Step).  Its constructors are sound: every
-- Provable derivation tree can be interpreted, given an ambient Deriv
-- hypothesis, as a Deriv-level fact (modulo classical interpretation
-- of negation).
--
-- This file provides:
--
--   sem        : Formula -> Equation -> Set
--                A semantic interpretation of formulas, parameterised
--                by an ambient Deriv hypothesis.
--                  sem (atomic eq) ambient = Deriv ambient eq
--                  sem (not P)     ambient = sem P ambient -> Empty
--                  sem (P imp Q)   ambient = sem P ambient -> sem Q ambient
--
--   provSound  : sem hyp ambient -> Provable hyp Q -> sem Q ambient
--                Soundness: any Provable derivation, given a sem-witness
--                for its hypothesis, evaluates to a sem-witness for its
--                conclusion at the chosen ambient.
--
--   provSoundTriv : Provable (atomic Triv) Q -> sem Q Triv
--                Specialisation to hyp = atomic Triv (the trivially-true
--                formula).  Witness for sem (atomic Triv) Triv is axRefl O.
--
-- Negation is interpreted classically (axNeg becomes valid via emptyElim
-- on the Empty inhabitant from notQ q).  The Provable layer's only
-- "classical" axiom is axNeg; everything else is intuitionistic.
--
-- No postulates, no holes.  Compiles under --safe --without-K
-- --exact-split.

module Guard.ProvableSound where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.Formula
open import Guard.Provable

------------------------------------------------------------------------
-- Semantic interpretation of Formula at a chosen ambient Deriv
-- hypothesis.

sem : Formula -> Equation -> Set
sem (atomic eq) ambient = Deriv ambient eq
sem (not P)     ambient = sem P ambient -> Empty
sem (P imp Q)   ambient = sem P ambient -> sem Q ambient

------------------------------------------------------------------------
-- Helper: classical axNeg interpretation.
--
-- (~P) -> (~Q) -> Q -> P
-- Given notP, notQ, q: from (notQ q) we get Empty, then emptyElim.

private
  classicalNeg : {ambient : Equation} (P Q : Formula) ->
                 (sem P ambient -> Empty) ->
                 (sem Q ambient -> Empty) ->
                 sem Q ambient ->
                 sem P ambient
  classicalNeg P Q notP notQ q = emptyElim (notQ q)

------------------------------------------------------------------------
-- Helper: equality axiom interpretations.

private
  semEqTrans : {ambient : Equation} (a b c : Term) ->
               Deriv ambient (eqn a b) ->
               Deriv ambient (eqn a c) ->
               Deriv ambient (eqn b c)
  semEqTrans a b c dab dac = ruleTrans (ruleSym dab) dac

  semEqCong1 : {ambient : Equation} (f : Fun1) (a b : Term) ->
               Deriv ambient (eqn a b) ->
               Deriv ambient (eqn (ap1 f a) (ap1 f b))
  semEqCong1 f a b dab = cong1 f dab

  semEqCongL : {ambient : Equation} (g : Fun2) (a b c : Term) ->
               Deriv ambient (eqn a b) ->
               Deriv ambient (eqn (ap2 g a c) (ap2 g b c))
  semEqCongL g a b c dab = congL g c dab

  semEqCongR : {ambient : Equation} (g : Fun2) (a b c : Term) ->
               Deriv ambient (eqn a b) ->
               Deriv ambient (eqn (ap2 g c a) (ap2 g c b))
  semEqCongR g a b c dab = congR g c dab

------------------------------------------------------------------------
-- Soundness.

provSound : {hyp : Formula} {ambient : Equation} {Q : Formula} ->
            sem hyp ambient ->
            Provable hyp Q ->
            sem Q ambient

provSound semHyp (fromDeriv d) = d
provSound semHyp ruleHypP      = semHyp

provSound semHyp (axK P Q) = \p _ -> p

provSound semHyp (axS P Q R) = \f g x -> f x (g x)

provSound semHyp (axNeg P Q) = classicalNeg P Q

provSound semHyp (axEqTrans a b c) = semEqTrans a b c
provSound semHyp (axEqCong1 f a b) = semEqCong1 f a b
provSound semHyp (axEqCongL g a b c) = semEqCongL g a b c
provSound semHyp (axEqCongR g a b c) = semEqCongR g a b c

provSound semHyp (mp pq p) = (provSound semHyp pq) (provSound semHyp p)

------------------------------------------------------------------------
-- Specialisation: hyp = atomic Triv (the trivially-true formula).
--
-- Triv = eqn O O.  The sem-witness for sem (atomic Triv) Triv is
-- a Deriv Triv (eqn O O), discharged by axRefl O.

private
  Triv : Equation
  Triv = eqn O O

provSoundTriv : {Q : Formula} ->
                Provable (atomic Triv) Q ->
                sem Q Triv
provSoundTriv = provSound (axRefl O)

------------------------------------------------------------------------
-- Convenience: extract a Deriv at the ambient from a Provable proof of
-- an atomic equation.

provExtract : {hyp : Formula} {ambient : Equation} {eq : Equation} ->
              sem hyp ambient ->
              Provable hyp (atomic eq) ->
              Deriv ambient eq
provExtract semHyp dProv = provSound semHyp dProv

provExtractTriv : {eq : Equation} ->
                  Provable (atomic Triv) (atomic eq) ->
                  Deriv Triv eq
provExtractTriv = provSoundTriv
