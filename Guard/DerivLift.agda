{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.DerivLift -- transport Deriv Triv X to Deriv H X for any H.
--
-- Since  Triv = eqn O O  is derivable under any hypothesis H via
-- axRefl O , any Deriv Triv X can be transported to Deriv H X by
-- mechanically substituting  ruleHyp{Triv}  with  axRefl O  throughout
-- the derivation tree.  All other Deriv constructors are polymorphic
-- in hyp and need no adjustment.
--
-- This is the key "lift" function for composing Triv-level theorems
-- (like dCon, dConStrong, any Triv-provable fact) into derivations
-- under arbitrary hypotheses.  It unlocks Rose-style chains that
-- require using Triv-level consistency premises inside sub-derivations
-- with non-Triv hypotheses.
--
-- No postulates, no holes.

module Guard.DerivLift where

open import Guard.Base
open import Guard.Term
open import Guard.Step

------------------------------------------------------------------------
-- Triv abbreviation.

private
  TrivEqn : Equation
  TrivEqn = eqn O O

------------------------------------------------------------------------
-- The lift function.
--
-- Given a derivation under  Triv = eqn O O , transport it to any hyp H
-- by replacing each  ruleHyp : Deriv Triv Triv  with  axRefl O :
-- Deriv H (eqn O O) = Deriv H Triv .
--
-- All other Deriv constructors are polymorphic in the hyp parameter
-- (they work for any hyp), so the transport is structurally direct.

lift : {H : Equation} {X : Equation} ->
       Deriv TrivEqn X -> Deriv H X

lift (axI t)               = axI t
lift (axFst a b)           = axFst a b
lift (axSnd a b)           = axSnd a b
lift (axConst a b)         = axConst a b
lift (axComp f g t)        = axComp f g t
lift (axComp2 h f g t)     = axComp2 h f g t
lift (axLift f a b)        = axLift f a b
lift (axPost f h a b)      = axPost f h a b
lift (axFan h1 h2 h a b)   = axFan h1 h2 h a b
lift (axKT t x)            = axKT t x
lift (axRecLf z s)         = axRecLf z s
lift (axRecNd z s a b)     = axRecNd z s a b
lift (axRecPLf s p)        = axRecPLf s p
lift (axRecPNd s p a b)    = axRecPNd s p a b
lift (axIfLfL a b)         = axIfLfL a b
lift (axIfLfN x y a b)     = axIfLfN x y a b
lift axTreeEqLL            = axTreeEqLL
lift (axTreeEqLN a b)      = axTreeEqLN a b
lift (axTreeEqNL a b)      = axTreeEqNL a b
lift (axTreeEqNN a1 a2 b1 b2) = axTreeEqNN a1 a2 b1 b2
lift (axGoodstein a b)     = axGoodstein a b
lift (axRefl t)            = axRefl t
lift (ruleSym d)           = ruleSym (lift d)
lift (ruleTrans d1 d2)     = ruleTrans (lift d1) (lift d2)
lift (cong1 f d)           = cong1 f (lift d)
lift (congL g x d)         = congL g x (lift d)
lift (congR g x d)         = congR g x (lift d)
lift (ruleInst x t d)      = ruleInst x t (lift d)
lift ruleHyp               = axRefl O
  -- The key case: ruleHyp at Triv gives Deriv Triv (eqn O O).
  -- We replace it with axRefl O : Deriv H (eqn O O) for any H.
lift (ruleF f g z s dfO dfP dgO dgP) =
  ruleF f g z s (lift dfO) (lift dfP) (lift dgO) (lift dgP)

------------------------------------------------------------------------
-- Summary
--
-- lift : {H X : Equation} -> Deriv TrivEqn X -> Deriv H X
--
-- Any Triv-provable equation is provable under any hypothesis H,
-- because Triv = eqn O O is derivable from axRefl O (which needs no
-- hypothesis).  The lift function mechanically transports the proof
-- tree.
--
-- Usage:
--   Given  dCon : Deriv Triv ConTrivRose  and a sub-derivation under
--   H_enc,  lift dCon : Deriv H_enc ConTrivRose  is usable directly.
--
--   Given  dConStrong : Deriv Triv ConTrivRoseStrong  analogously.
--
-- This unlocks Rose-style chains where consistency-under-Triv is
-- composed with hypothetical-H_enc-style reasoning.
