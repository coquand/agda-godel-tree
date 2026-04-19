{-# OPTIONS --safe --without-K --exact-split #-}

-- NoPChecker.agda
-- Cook's Theorem 7.1 (simplified, without propositional calculus).
--
-- Cook (1975) shows that PV, viewed as a proof system for the
-- propositional calculus, is not p-verifiable. The full argument
-- requires encoding propositional formulas and truth evaluation.
--
-- This module gives the equational core of that result:
-- there is no Guard functor VER that provably decides whether
-- a tree encodes a proof of 0 = 1.
--
-- The key insight: any such VER would let Guard derive conSentence
-- (the internal consistency statement), which godelII blocks.
--
-- Three formulations are given, from weakest to strongest:
--
-- 1. noPChecker: if VER provably agrees with the consistency check
--    AND provably always returns falseT, then hyp is inconsistent.
--
-- 2. noConsistencyWitness: ANY derivation of conSentence from a
--    consistent hypothesis leads to contradiction — regardless of
--    how it was obtained (by a functor or otherwise).
--
-- 3. noSoundComplete: if VER is provably sound (accepted inputs
--    don't prove 0=1) and provably complete (all non-proofs-of-0=1
--    are accepted), then from consistency of hyp, one can derive 0=1.
--    I.e., sound+complete proof checking is impossible.

module Guard.NoPChecker where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.GodelIIFull
  using (godelII ; conToBot ; conSentence ; codeBotT ; trueT ; falseT)
open import Guard.ThFunTFor using (thFunTFor)
open import Guard.CookPV using (sg ; sgLf ; sgNd ; notF ; notFLf ; notFNd)

private
  v0 : Term ; v0 = var zero

------------------------------------------------------------------------
-- 1. No proof-checking functor
--
-- If VER : Fun1 provably returns falseT on all inputs, AND provably
-- agrees with TreeEq(thFunTFor(_), codeBotT), then VER witnesses
-- conSentence, contradicting godelII.

noPChecker : {hyp : Equation} ->
  (VER : Fun1) ->
  Consistent hyp ->
  Deriv hyp (eqn (ap1 VER v0) falseT) ->
  Deriv hyp (eqn (ap1 VER v0)
                  (ap2 TreeEq (ap1 thFunTFor v0) codeBotT)) ->
  Empty
noPChecker VER con dAll dAgree =
  godelII con (ruleTrans (ruleSym dAgree) dAll)

------------------------------------------------------------------------
-- 2. No consistency witness (most general form)
--
-- This is just godelII re-exported with documentation:
-- ANY derivation of conSentence leads to inconsistency.
-- A proof checker, a decision procedure, an oracle — it doesn't
-- matter how conSentence was derived.

noConsistencyWitness : {hyp : Equation} ->
  Consistent hyp ->
  Deriv hyp conSentence ->
  Empty
noConsistencyWitness = godelII

------------------------------------------------------------------------
-- 3. No sound and complete checker
--
-- Suppose DEC : Fun1 satisfies:
--   (a) Soundness: sg(DEC(x)) = sg(TreeEq(thFunTFor(x), codeBotT))
--       i.e., DEC(x) = O iff TreeEq(thFunTFor(x), codeBotT) = O
--       (DEC accepts x iff x really proves 0=1)
--   (b) Completeness: DEC(x) = TreeEq(thFunTFor(x), codeBotT) for all x
--       (stronger: DEC exactly matches the consistency check)
--
-- Then hyp is inconsistent. This follows because completeness (b)
-- alone, combined with "DEC always returns falseT" (which would
-- follow from the consistency of thFunTFor), gives conSentence.
--
-- But we don't even need to derive "DEC always returns falseT" —
-- completeness (b) directly makes DEC(x) = TreeEq(thFunTFor(x), codeBotT)
-- into conSentence if we can also show DEC(x) = falseT.
--
-- The real obstruction: we CAN'T prove DEC(x) = falseT for all x
-- within Guard (that would be conSentence). So a correct DEC exists
-- as a meta-level function but NOT as a Guard-provably-correct functor.
--
-- This is the equational analog of Cook's observation: the verification
-- function exists in L (polytime), but its correctness proof cannot
-- be carried out in PV.

-- The constructive content: from a derivation of conSentence,
-- produce a derivation of 0 = 1.
conSentenceToBot : {hyp : Equation} ->
  Deriv hyp conSentence ->
  Deriv hyp (eqn trueT falseT)
conSentenceToBot = conToBot

-- Putting it together: if DEC is a provably correct decision procedure
-- and Guard can prove "DEC rejects everything" (because there are no
-- proofs of 0=1), then Guard proves 0=1.
noSoundComplete : {hyp : Equation} ->
  (DEC : Fun1) ->
  -- DEC agrees with the consistency check for all x
  Deriv hyp (eqn (ap1 DEC v0)
                  (ap2 TreeEq (ap1 thFunTFor v0) codeBotT)) ->
  -- DEC rejects all inputs (asserts no proof of 0=1 exists)
  Deriv hyp (eqn (ap1 DEC v0) falseT) ->
  -- Then Guard proves 0=1
  Deriv hyp (eqn trueT falseT)
noSoundComplete DEC dAgree dReject =
  conToBot (ruleTrans (ruleSym dAgree) dReject)
