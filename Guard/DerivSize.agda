{-# OPTIONS --safe --without-K --exact-split #-}

module Guard.DerivSize where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.GodelII using (treeEqSelfAll ; treeEqSelf)

------------------------------------------------------------------------
-- Natural number addition

natAdd : Nat -> Nat -> Nat
natAdd zero    m = m
natAdd (suc n) m = suc (natAdd n m)

------------------------------------------------------------------------
-- Derivation size (number of constructor applications)
--
-- Each axiom costs 1.
-- Each rule costs 1 + sum of sub-derivation sizes.

derivSize : {hyp : Equation} {eq : Equation} -> Deriv hyp eq -> Nat
derivSize (axI _)              = suc zero
derivSize (axFst _ _)          = suc zero
derivSize (axSnd _ _)          = suc zero
derivSize (axConst _ _)        = suc zero
derivSize (axComp _ _ _)       = suc zero
derivSize (axComp2 _ _ _ _)    = suc zero
derivSize (axLift _ _ _)       = suc zero
derivSize (axPost _ _ _ _)     = suc zero
derivSize (axFan _ _ _ _ _)    = suc zero
derivSize (axKT _ _)           = suc zero
derivSize (axRecLf _ _)        = suc zero
derivSize (axRecNd _ _ _ _)    = suc zero
derivSize (axIfLfL _ _)        = suc zero
derivSize (axIfLfN _ _ _ _)    = suc zero
derivSize axTreeEqLL           = suc zero
derivSize (axTreeEqLN _ _)     = suc zero
derivSize (axTreeEqNL _ _)     = suc zero
derivSize (axTreeEqNN _ _ _ _) = suc zero
derivSize (axRefl _)           = suc zero
derivSize (ruleSym d)          = suc (derivSize d)
derivSize (ruleTrans d1 d2)    = suc (natAdd (derivSize d1) (derivSize d2))
derivSize (cong1 _ d)          = suc (derivSize d)
derivSize (congL _ _ d)        = suc (derivSize d)
derivSize (congR _ _ d)        = suc (derivSize d)
derivSize (ruleInst _ _ d)     = suc (derivSize d)
derivSize ruleHyp              = suc zero
derivSize (ruleF _ _ _ _ d1 d2 d3 d4) =
  suc (natAdd (derivSize d1)
      (natAdd (derivSize d2)
      (natAdd (derivSize d3) (derivSize d4))))

------------------------------------------------------------------------
-- Schema F proof: constant size
--
-- treeEqSelfAll proves TreeEq(t,t) = O for all t via Schema F.
-- treeEqSelf t instantiates it for a specific t.
--
-- Both have derivation size independent of hyp and t.
--
-- Breakdown:
--   teIRed    : 7  (axComp2 + 2*axI + congL + congR + 2*ruleTrans)
--   teSelfRed : 31 (Fan/Post/Lift reduction chain)
--   fBase     : 9  (teIRed O + axTreeEqLL + ruleTrans)
--   fStep     : 61 (teIRed + axTreeEqNN + teSelfRed + congruences)
--   gBase     : 1  (axKT)
--   gStep     : 41 (axKT + teSelfRed + axIfLfL + congruences)
--   ruleF     : 1 + 9 + 61 + 1 + 41 = 113
--   treeEqSelf: 113 + ruleInst + axKT + ruleSym(teIRed) + 2*ruleTrans = 125

private
  n5   : Nat ; n5   = suc (suc (suc (suc (suc zero))))
  n10  : Nat ; n10  = natAdd n5 n5
  n13  : Nat ; n13  = natAdd n10 (suc (suc (suc zero)))
  n25  : Nat ; n25  = natAdd n13 (natAdd n10 (suc (suc zero)))
  n50  : Nat ; n50  = natAdd n25 n25
  n100 : Nat ; n100 = natAdd n50 n50
  sz113 : Nat ; sz113 = natAdd n100 n13
  sz125 : Nat ; sz125 = natAdd sz113 (natAdd n10 (suc (suc zero)))

-- treeEqSelfAll uses exactly 113 inference steps
schemaFAllSize : {hyp : Equation} ->
  Eq (derivSize (treeEqSelfAll {hyp})) sz113
schemaFAllSize = refl

-- treeEqSelf t uses exactly 125 inference steps, for any term t
schemaFSelfSize : (t : Term) -> {hyp : Equation} ->
  Eq (derivSize (treeEqSelf t {hyp})) sz125
schemaFSelfSize t = refl
