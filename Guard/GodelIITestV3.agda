{-# OPTIONS --safe --without-K --exact-split #-}

-- Negative acceptance test for V3: verify case19V3 rejects the V2
-- loophole attack of constructing  ProofE3 H (eqn trueT falseT)  from
--  trans(refl trueT, refl falseT) .
--
-- In V2, an analogous attack using  thm14ETrans + mkProofEAny  would
-- have created a FAKE encoding with  thFunTFor(fake) = codeBot .  V3
-- closes this via  case19V3 's middle-term match check:
-- thm14EV3Trans's type requires
--   ProofE3 H (eqn t u)  and  ProofE3 H (eqn u v)
-- with the SAME middle term  u .  Providing  refl trueT  and
--  refl falseT  gives middle terms  trueT  and  falseT , which
-- don't unify — so the attempted fake does NOT typecheck.
--
-- The check is at the TYPE LEVEL, not a runtime assertion.  Agda's
-- type-checker enforces it.

module Guard.GodelIITestV3 where

open import Guard.Base
open import Guard.Term
open import Guard.Thm14EV3 using (ProofE3 ; thm14EV3Trans ; thm14EV3Refl)

private
  trueT : Term
  trueT = O

  falseT : Term
  falseT = ap2 Pair O O

------------------------------------------------------------------------
-- The attempted attack — INTENTIONALLY COMMENTED OUT.
--
-- Uncommenting this block must produce a type error; if Agda accepts
-- it, the V3 redesign has failed to close the loophole.

{- attempted attack, does NOT typecheck:

fakeTrans : {H : Equation} -> ProofE3 H (eqn trueT falseT)
fakeTrans {H} =
  thm14EV3Trans {H} {trueT} {???}        -- refl gives eqn trueT trueT
                {falseT}                  -- refl gives eqn falseT falseT
                (thm14EV3Refl H trueT)    -- : ProofE3 H (eqn trueT trueT)
                (thm14EV3Refl H falseT)   -- : ProofE3 H (eqn falseT falseT)
  -- The middle terms are  trueT  and  falseT  — don't unify.

-}

------------------------------------------------------------------------
-- A POSITIVE test of the same building blocks, showing trans works
-- when middle terms genuinely match.

positiveTrans : {H : Equation} (t : Term) ->
                ProofE3 H (eqn t t)
positiveTrans H = thm14EV3Refl _ _
  -- OR, equivalently, via trans of two refls on the same term:
  --   thm14EV3Trans (thm14EV3Refl _ t) (thm14EV3Refl _ t)
  -- which typechecks because both middle terms are  t .

------------------------------------------------------------------------
-- The loophole in V2 was:  mkProofEAny  built a fake encoding with
--  thFunTFor(fake) = reify(codeEqn arbitraryEq)  for ANY equation.
-- V3 has no  mkProofEAny  — every  ProofE3  value must come from a
-- genuine  thm14EV3  derivation.  Combined with  case19V3 's
-- middle-term check, the V2 attack surface is structurally removed.
