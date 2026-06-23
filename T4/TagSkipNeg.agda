{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.TagSkipNeg -- NEG-FORM tag-test skips: a cascade test SKIPS (= O) whenever
-- the recovered label is KNOWN-DIFFERENT (a bare  neg (label = natCode k) ), via
-- natEqF_complete.  The shipped  testEq_skip / testAdZeS_skip / testAdSuS_skip
-- are keyed on a LITERAL  m  with a  NatNeqWitness ; these neg-form variants take
-- the symbolic inequality directly, as needed by the object course-of-values
-- tag dispatch (where the "other" tags are only known to be != the target).
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.TagSkipNeg where

open import T4.Base

open import BRA3.SubT.NatEq using ( natEqF )
open import T4.NatEqReflect using ( natEqF_complete )
open import T4.BinTree      using ( nIdx )
open import T4.DerSrc       using ( testEq )
open import T4.DerTriS      using ( adLeftTag ; testAdZeS ; testAdSuS )

------------------------------------------------------------------------
-- Generic: a  C natEqF lbl (constN k)  test skips when  lbl input != natCode k .

private
  skip_neg_generic : (lbl : Fun1) (k : Nat) (input : Term) ->
    Deriv (neg (eqF (ap1 lbl input) (natCode k))) ->
    Deriv (eqF (ap1 (C natEqF lbl (constN k)) input) O)
  skip_neg_generic lbl k input neq =
    ruleTrans (ax_C natEqF lbl (constN k) input)
      (ruleTrans (congR natEqF (ap1 lbl input) (constN_eq k input))
                 (mp (natEqF_complete (ap1 lbl input) (natCode k)) neq))

------------------------------------------------------------------------
-- The three instantiations (nIdx for wfStep/triStep cascade; adLeftTag for Ad).

testEq_skip_neg : (k : Nat) (input : Term) ->
  Deriv (neg (eqF (ap1 nIdx input) (natCode k))) ->
  Deriv (eqF (ap1 (testEq k) input) O)
testEq_skip_neg k input neq = skip_neg_generic nIdx k input neq

testAdZeS_skip_neg : (input : Term) ->
  Deriv (neg (eqF (ap1 adLeftTag input) (natCode 0))) ->
  Deriv (eqF (ap1 testAdZeS input) O)
testAdZeS_skip_neg input neq = skip_neg_generic adLeftTag 0 input neq

testAdSuS_skip_neg : (input : Term) ->
  Deriv (neg (eqF (ap1 adLeftTag input) (natCode 1))) ->
  Deriv (eqF (ap1 testAdSuS input) O)
testAdSuS_skip_neg input neq = skip_neg_generic adLeftTag 1 input neq
