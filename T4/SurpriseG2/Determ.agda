{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SurpriseG2.Determ -- runProg-functional / same-fuel determinism.
--
-- BRA  Fun2  application is functional: any two derivations
-- showing  ap2 F a b  equals two RHS values force those RHS to be equal.
-- This is just  ax_eqTrans  +  ruleSym  (Guard axiom 4); no new fact.
--
-- For the Kritchman-Raz pigeonhole base case we need:
--
--   runProg_det :
--     Deriv (eqF (ap2 runProg p n) (ap1 s a)) ->
--     Deriv (eqF (ap2 runProg p n) (ap1 s b)) ->
--     Deriv (eqF (ap1 s a) (ap1 s b))
--
-- (same program, SAME fuel  n ).  In our setting the two Describes facts
-- coming from the pigeonhole step share the open fuel slot  var 0 , so
-- after a common  ruleInst 0 t  the fuels coincide and the lemma applies
-- as-is.  We do NOT need the broader monotonicity statement
-- ( different fuels) -- the design doc's mention of  n1 / n2  is the
-- *unresolved* form before instantiating the open fuel.
--
-- ( T4.Definable  defines an exact-halt-time variant pinning the
-- monotonicity in BRA; we side-step that here because the open-fuel
-- form lets us share fuel by instantiation, which is all the pigeonhole
-- step needs.)

module T4.SurpriseG2.Determ where

open import T4.Base
open import T4.Kdef using ( runProg )

------------------------------------------------------------------------
-- runProg_det : same program, same fuel -> outputs agree (s-wrapped).
--
-- Proof: from  runProg p n = s a  and  runProg p n = s b , by  ruleSym
-- on the first and  ruleTrans  we get  s a = s b .

runProg_det :
  (p n a b : Term) ->
  Deriv (eqF (ap2 runProg p n) (ap1 s a)) ->
  Deriv (eqF (ap2 runProg p n) (ap1 s b)) ->
  Deriv (eqF (ap1 s a) (ap1 s b))
runProg_det p n a b ha hb =
  ruleTrans (ruleSym ha) hb

-- (No s-cancellation primitive in BRA -- we keep the s-wrapped equation
-- and discharge meta-distinct cases via  ax_succ_nonzero  applied after
-- meta-induction on the Nat difference.  See SurpriseG2.NumNeq.)
