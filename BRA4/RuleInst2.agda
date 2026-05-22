{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.RuleInst2 -- re-export of BRA3.RuleInst2 (Church Standard
-- Metatheorem VII).
--
-- BRA4's Deriv layer is the same as BRA3's (BRA4.Base re-exports
-- BRA3.Base/Term/Formula/Deriv).  RuleInst2 is purely a Deriv-level
-- derived theorem (no thmT/code dependency), so it ports verbatim
-- to BRA4 without changes.
--
-- Public API (mirrored from BRA3.RuleInst2):
--
--   ruleInst2 :
--     (k1 : Nat) (t1 : Term) (k2 : Nat) (t2 : Term) ->
--     Eq (natEq k1 k2) false ->
--     {P : Formula} -> Deriv P -> Deriv (simSubstF k1 t1 k2 t2 P)
--
--   simSubstT / simSubstF -- the simultaneous-sub functions.
--   freshC + above-max lemmas -- the freshness machinery.
--   three_step_T / three_step_F -- decomposition lemmas.
--   maxVarT / maxVarF -- bound on free vars in a Term / Formula.
--   NatLe + lemmas (le-zero, le-suc, le-refl, le-trans, ...).
--
-- USE.  This module is the foundation for BRA4.SbtFresh and
-- BRA4.ThmTCompleteAxEqTransUniv : both of those derive freshness-
-- style stability lemmas at the thmT level.

module BRA4.RuleInst2 where

open import BRA4.Base

open import BRA3.RuleInst2 public
