{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.ProvableLemmas -- derived theorems and the deduction theorem.
--
-- Step 3 of GUARD-BRA-TEMPLATE.md.  The deduction theorem is the
-- critical milestone; per Guard 1963 page 11 (Exercise 19) it is a
-- standard meta-theorem of any propositional system with K + S +
-- modus ponens (Hilbert-Bernays / Church).  The Agda proof is
-- structural induction on Provable.
--
-- Note: deductionThm's mp case triggers a CoverageNoExactSplit
-- warning (one warning, ignorable).  This is intrinsic to pattern
-- matching on the mp constructor whose conclusion-index Q is unified
-- with the deduction-theorem's target Q via metavariable resolution
-- rather than constructor injectivity.  The function is correct;
-- only Agda's case-tree reduction is slightly less predictable for
-- this case.  Downstream uses do not depend on case-tree reduction.
--
-- No postulates, no holes.

module Guard.ProvableLemmas where

open import Guard.Base
open import Guard.Term
open import Guard.Formula
open import Guard.Provable

------------------------------------------------------------------------
-- provI: P imp P, derivable as I = S K K.
--
--   axS P (P imp P) P : (P ⊃ ((P imp P) ⊃ P)) ⊃ ((P ⊃ (P imp P)) ⊃ (P ⊃ P))
--   axK P (P imp P)   : P ⊃ ((P imp P) ⊃ P)
--   mp (axS) (axK)    : (P ⊃ (P imp P)) ⊃ (P ⊃ P)
--   axK P P           : P ⊃ (P ⊃ P)
--   mp prev (axK P P) : P ⊃ P

provI : (P : Formula) {hyp : Formula} -> Provable hyp (P imp P)
provI P {hyp} =
  mp (mp (axS P (P imp P) P) (axK P (P imp P))) (axK P P)

------------------------------------------------------------------------
-- Deduction theorem.
--
-- Per Guard 1963 page 11, Exercise 19: deduction theorem for BRA is
-- a standard meta-theorem derivable from K, S, and modus ponens.
-- Proof by structural induction on the Provable derivation tree.

-- A small helper to fold the mp case via axS chaining.

private
  dedThmMp : (P R Q : Formula) {hyp : Formula} ->
             Provable hyp (P imp (R imp Q)) ->
             Provable hyp (P imp R) ->
             Provable hyp (P imp Q)
  dedThmMp P R Q dPRQ dPR =
    mp (mp (axS P R Q) dPRQ) dPR

deductionThm : (P Q : Formula) {hyp : Formula} ->
               Provable P Q ->
               Provable hyp (P imp Q)

------------------------------------------------------------------------
-- Case analysis on the Provable proof tree.

-- (1) fromDeriv d : Provable P (atomic eq), where d is a polymorphic
-- Deriv.  Output: Provable hyp (P imp atomic eq).
-- Strategy: re-apply fromDeriv at hyp to get Provable hyp (atomic eq),
-- then wrap with axK to lift over the antecedent P.

deductionThm P (atomic eq) (fromDeriv d) =
  mp (axK (atomic eq) P) (fromDeriv d)

-- (2) ruleHypP : Provable P P (the hypothesis is the conclusion).
-- Output: Provable hyp (P imp P) = provI P.

deductionThm P .P ruleHypP = provI P

-- (3) axK P' Q' : Provable P (P' imp (Q' imp P')).
-- Output: Provable hyp (P imp (P' imp (Q' imp P'))).
-- Strategy: axK at the same axiom, lifted by axK over P.

deductionThm P .(P' imp (Q' imp P')) (axK P' Q') =
  mp (axK (P' imp (Q' imp P')) P) (axK P' Q')

-- (4) axS P' Q' R' : similar to axK case.

deductionThm P
  .((P' imp (Q' imp R')) imp ((P' imp Q') imp (P' imp R')))
  (axS P' Q' R') =
  mp (axK ((P' imp (Q' imp R')) imp ((P' imp Q') imp (P' imp R'))) P)
     (axS P' Q' R')

-- (5) axNeg P' Q' : similar.

deductionThm P .((not P') imp ((not Q') imp (Q' imp P'))) (axNeg P' Q') =
  mp (axK ((not P') imp ((not Q') imp (Q' imp P'))) P)
     (axNeg P' Q')

-- (6-9) Equality axioms (Guard ax 4-7): each lifts via axK over P.

deductionThm P
  .((atomic (eqn a b)) imp ((atomic (eqn a c)) imp (atomic (eqn b c))))
  (axEqTrans a b c) =
  mp (axK ((atomic (eqn a b)) imp ((atomic (eqn a c)) imp (atomic (eqn b c)))) P)
     (axEqTrans a b c)

deductionThm P
  .((atomic (eqn a b)) imp (atomic (eqn (ap1 f a) (ap1 f b))))
  (axEqCong1 f a b) =
  mp (axK ((atomic (eqn a b)) imp (atomic (eqn (ap1 f a) (ap1 f b)))) P)
     (axEqCong1 f a b)

deductionThm P
  .((atomic (eqn a b)) imp (atomic (eqn (ap2 g a c) (ap2 g b c))))
  (axEqCongL g a b c) =
  mp (axK ((atomic (eqn a b)) imp (atomic (eqn (ap2 g a c) (ap2 g b c)))) P)
     (axEqCongL g a b c)

deductionThm P
  .((atomic (eqn a b)) imp (atomic (eqn (ap2 g c a) (ap2 g c b))))
  (axEqCongR g a b c) =
  mp (axK ((atomic (eqn a b)) imp (atomic (eqn (ap2 g c a) (ap2 g c b)))) P)
     (axEqCongR g a b c)

-- (10) mp pq p : Provable P Q derived from Provable P (R imp Q) and
-- Provable P R.  IH on pq gives Provable hyp (P imp (R imp Q)); IH on
-- p gives Provable hyp (P imp R).  Combine via dedThmMp.

deductionThm P Q (mp {R} pq p) =
  dedThmMp P R Q (deductionThm P (R imp Q) pq) (deductionThm P R p)
