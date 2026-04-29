{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.Tag
--
-- Tag constants for the proof-code alphabet used by  thmT  and  encode .
-- One Nat per primitive of  BRA/Deriv.agda  (40 total, matching
-- BRA/DERIV-AUDIT.md).
--
-- Convention: every tag value is  >= suc zero  ( = 1 ).
-- Reason:  natCode 0 = lf  reifies to  O ; the discriminator
--  Fst (Fst p1)  in  BRA/Thm/StepProto.agda 's step function would be
--  Fst O , which has no defining axiom, so any tag = 0 would block
-- top-level dispatch.  See StepProto.agda's header for derivation.
--
-- Values used: 1 .. 40 .  Code-of-Functor tags  natCode 26 .. 33  in
-- BRA/Term.agda overlap numerically with proof tags  ruleTrans ..
-- axEqCongR , but the overlap is harmless: code-of-Functor values
-- live as inner subtrees of proof payloads, never as the  Fst  of
--  thmT 's input.  The dispatch chain TreeEq-tests at  Fst p1  only
-- against proof tags, where code-of-Functor values cannot appear.
-- Pruning the overlap would require shifting proof tags to 35+,
-- adding ~4 lines of  suc  per tag definition; not worth it.
--
-- Each tag is defined as  suc  of the previous one: keeps the file
-- compact and the natCode normalisations cheap (Agda does not need
-- to expand 40 nested  suc  literals; the  suc  chain is structurally
-- shared at the type-checker's name table).

module BRA.Thm.Tag where

open import BRA.Base using (Nat ; zero ; suc)

------------------------------------------------------------------------
-- Combinator defining equations (10 tags, 1..10).

tagAxI       : Nat
tagAxI       = suc zero

tagAxFst     : Nat
tagAxFst     = suc tagAxI

tagAxSnd     : Nat
tagAxSnd     = suc tagAxFst

tagAxConst   : Nat
tagAxConst   = suc tagAxSnd

tagAxComp    : Nat
tagAxComp    = suc tagAxConst

tagAxComp2   : Nat
tagAxComp2   = suc tagAxComp

tagAxLift    : Nat
tagAxLift    = suc tagAxComp2

tagAxPost    : Nat
tagAxPost    = suc tagAxLift

tagAxFan     : Nat
tagAxFan     = suc tagAxPost

tagAxKT      : Nat
tagAxKT      = suc tagAxFan

------------------------------------------------------------------------
-- Tree recursion + IfLf (6 tags, 11..16).

tagAxRecLf   : Nat
tagAxRecLf   = suc tagAxKT

tagAxRecNd   : Nat
tagAxRecNd   = suc tagAxRecLf

tagAxRecPLf  : Nat
tagAxRecPLf  = suc tagAxRecNd

tagAxRecPNd  : Nat
tagAxRecPNd  = suc tagAxRecPLf

tagAxIfLfL   : Nat
tagAxIfLfL   = suc tagAxRecPNd

tagAxIfLfN   : Nat
tagAxIfLfN   = suc tagAxIfLfL

------------------------------------------------------------------------
-- TreeEq + Goodstein (5 tags, 17..21).

tagAxTreeEqLL : Nat
tagAxTreeEqLL = suc tagAxIfLfN

tagAxTreeEqLN : Nat
tagAxTreeEqLN = suc tagAxTreeEqLL

tagAxTreeEqNL : Nat
tagAxTreeEqNL = suc tagAxTreeEqLN

tagAxTreeEqNN : Nat
tagAxTreeEqNN = suc tagAxTreeEqNL

tagAxGoodstein : Nat
tagAxGoodstein = suc tagAxTreeEqNN

------------------------------------------------------------------------
-- Structural equational rules (6 tags, 22..27).

tagAxRefl    : Nat
tagAxRefl    = suc tagAxGoodstein

tagRuleSym   : Nat
tagRuleSym   = suc tagAxRefl

tagRuleTrans : Nat
tagRuleTrans = suc tagRuleSym

tagCong1     : Nat
tagCong1     = suc tagRuleTrans

tagCongL     : Nat
tagCongL     = suc tagCong1

tagCongR     : Nat
tagCongR     = suc tagCongL

------------------------------------------------------------------------
-- Equality congruence axioms Ax 4-7 (4 tags, 28..31).

tagAxEqTrans : Nat
tagAxEqTrans = suc tagCongR

tagAxEqCong1 : Nat
tagAxEqCong1 = suc tagAxEqTrans

tagAxEqCongL : Nat
tagAxEqCongL = suc tagAxEqCong1

tagAxEqCongR : Nat
tagAxEqCongR = suc tagAxEqCongL

------------------------------------------------------------------------
-- Propositional axioms (5 tags, 32..36).

tagAxK       : Nat
tagAxK       = suc tagAxEqCongR

tagAxS       : Nat
tagAxS       = suc tagAxK

tagAxNeg     : Nat
tagAxNeg     = suc tagAxS

tagAxExFalso : Nat
tagAxExFalso = suc tagAxNeg

tagAxContrapos : Nat
tagAxContrapos = suc tagAxExFalso

------------------------------------------------------------------------
-- Recursive inference rules (3 tags, 37..39).
--
-- These primitives take Deriv sub-proofs as arguments; their
-- encodings splice sub-proof Trees as children of the encoding node.
-- See  BRA/Thm/Parts/Mp.agda  for the prototype shape.

tagMp        : Nat
tagMp        = suc tagAxContrapos

tagRuleInst  : Nat
tagRuleInst  = suc tagMp

tagRuleIndBT : Nat
tagRuleIndBT = suc tagRuleInst

------------------------------------------------------------------------
-- Safe-default axioms for Theorem 12 totality (4 tags, 40..43).

tagAxFstLf  : Nat
tagAxFstLf  = suc tagRuleIndBT

tagAxSndLf  : Nat
tagAxSndLf  = suc tagAxFstLf

tagAxIfLfLL : Nat
tagAxIfLfLL = suc tagAxSndLf

tagAxIfLfNL : Nat
tagAxIfLfNL = suc tagAxIfLfLL

------------------------------------------------------------------------
-- Simultaneous double-substitution tag (1 tag, 44).
--
-- Used by  body_ruleInst2  to dispatch  thmT  to  subT2  for
-- simultaneous substitution at TWO variables.  Required for
-- Theorem 12 at shape-dispatched / multi-variable Fun1's like
-- Fst, Snd whose defining axiom has two free vars.

tagRuleInst2 : Nat
tagRuleInst2 = suc tagAxIfLfNL

------------------------------------------------------------------------
-- Schema F (ruleF) was a primitive Deriv constructor demotable to
-- ruleIndBT + structural rules; removed in 2026-04-26 refactor.
-- See BRA/REFACTOR-PLAN.md .
