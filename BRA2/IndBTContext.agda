{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.IndBTContext -- one-hole proof contexts for the structural
-- rules of  DerivTBounded .
--
-- T4 of BRA2/NEXT-SESSION-RANKDECREMENT.md (post-T3 plan).
--
-- An  IndBTFrame Fin Fout  is a one-step structural-rule context:
-- given a derivation of  Fin  (with some rank, level), it produces
-- a derivation of  Fout  by applying ONE structural rule.
-- An  IndBTContext Fin Fout  is a sequence of frames composed
-- together (a "path" through structural rules).
--
-- The motivation is the rank-decrement programme: given a
-- DerivTBounded (suc r) l bot  whose proof tree contains a topmost
-- indBT, the structural rules ABOVE the indBT (between it and the
-- root  bot ) form an  IndBTContext FindBT bot  where  FindBT  is
-- the indBT's conclusion.  The rank-decrement strategy ("find-and-
-- replace") becomes:
--   1. Find a topmost indBT and the context to bot.
--   2. Replace the indBT with a rank-r equivalent (still proving FindBT).
--   3. Plug the replacement back through the context to recover bot.
--
-- This module delivers (1) the type definitions, (2) plug operations
-- mapping a derivation through a frame / context.  The actual
-- "find" and "replace" operations are deferred to T5 / future work.
--
-- Structural rules represented (the 7 non-rank-introducing
-- constructors that pass through atomic-formula derivations):
--   * ruleSymB                 (symF)
--   * ruleTransB (left hole)   (transLF u v + d_other)
--   * ruleTransB (right hole)  (transRF t u + d_other)
--   * cong1B / congLB / congRB (cong1F / congLF / congRF)
--   * mpB (left hole, P imp Q) (mpLF + d_arg)
--   * mpB (right hole, P)      (mpRF + d_imp)
--   * ruleInstB                (instF)
--
-- Atomic axioms, axRefl, axEq*, axK/S/Neg, indBT*: NOT frames.
-- These are leaves of the proof tree.

module BRA2.IndBTContext where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
import BRA2.DerivTBounded as B
open import BRA2.DerivTBounded using (DerivTBounded)

------------------------------------------------------------------------
-- IndBTFrame Fin Fout : a one-step structural-rule context.
--
-- Each frame represents an application of a structural rule with the
-- "hole" at one of its premises and the OTHER premises (if any)
-- supplied as fixed derivations carried in the frame.

data IndBTFrame : Formula -> Formula -> Set where

  -- ruleSymB : preserves rank, swaps t and u.
  symF :
    (t u : Term) ->
    IndBTFrame (atomic (eqn t u)) (atomic (eqn u t))

  -- ruleTransB with the hole on the LEFT premise.  The right
  -- premise (eqn u v) is supplied as d_other.
  transLF :
    {r2 l2 : Nat} (t u v : Term) ->
    DerivTBounded r2 l2 (atomic (eqn u v)) ->
    IndBTFrame (atomic (eqn t u)) (atomic (eqn t v))

  -- ruleTransB with the hole on the RIGHT premise.  The left
  -- premise (eqn t u) is supplied as d_other.
  transRF :
    {r1 l1 : Nat} (t u v : Term) ->
    DerivTBounded r1 l1 (atomic (eqn t u)) ->
    IndBTFrame (atomic (eqn u v)) (atomic (eqn t v))

  cong1F :
    (f : Fun1) (t u : Term) ->
    IndBTFrame (atomic (eqn t u))
                (atomic (eqn (ap1 f t) (ap1 f u)))

  congLF :
    (g : Fun2) (t u x : Term) ->
    IndBTFrame (atomic (eqn t u))
                (atomic (eqn (ap2 g t x) (ap2 g u x)))

  congRF :
    (g : Fun2) (x t u : Term) ->
    IndBTFrame (atomic (eqn t u))
                (atomic (eqn (ap2 g x t) (ap2 g x u)))

  -- mpB with the hole on the LEFT premise (the implication).  The
  -- argument premise is supplied as d_arg.
  mpLF :
    {r2 l2 : Nat} (P Q : Formula) ->
    DerivTBounded r2 l2 P ->
    IndBTFrame (P imp Q) Q

  -- mpB with the hole on the RIGHT premise (the antecedent).  The
  -- implication premise is supplied as d_imp.
  mpRF :
    {r1 l1 : Nat} (P Q : Formula) ->
    DerivTBounded r1 l1 (P imp Q) ->
    IndBTFrame P Q

  instF :
    (x : Nat) (t : Term) (P : Formula) ->
    IndBTFrame P (substF x t P)

------------------------------------------------------------------------
-- A "plugged" derivation: existential rank/level wrapping a
-- DerivTBounded.  Used as the result of plugFrame / plugContext.

record PluggedDeriv (F : Formula) : Set where
  constructor mkPlugged
  field
    pluggedRank  : Nat
    pluggedLevel : Nat
    pluggedDeriv : DerivTBounded pluggedRank pluggedLevel F
open PluggedDeriv public

------------------------------------------------------------------------
-- Plug a derivation into a frame.  Each clause is one direct
-- structural-rule application.

plugFrame :
  {Fin Fout : Formula} {r l : Nat} ->
  IndBTFrame Fin Fout ->
  DerivTBounded r l Fin ->
  PluggedDeriv Fout
plugFrame {r = r} {l = l} (symF _ _) d =
  mkPlugged r l (B.ruleSymB d)
plugFrame (transLF _ _ _ d2) d =
  mkPlugged _ _ (B.ruleTransB d d2)
plugFrame (transRF _ _ _ d1) d =
  mkPlugged _ _ (B.ruleTransB d1 d)
plugFrame {r = r} {l = l} (cong1F f _ _) d =
  mkPlugged r l (B.cong1B f d)
plugFrame {r = r} {l = l} (congLF g _ _ x) d =
  mkPlugged r l (B.congLB g x d)
plugFrame {r = r} {l = l} (congRF g x _ _) d =
  mkPlugged r l (B.congRB g x d)
plugFrame (mpLF _ _ d_arg) d =
  mkPlugged _ _ (B.mpB d d_arg)
plugFrame (mpRF _ _ d_imp) d =
  mkPlugged _ _ (B.mpB d_imp d)
plugFrame {r = r} {l = l} (instF x t _) d =
  mkPlugged r l (B.ruleInstB x t d)

------------------------------------------------------------------------
-- IndBTContext Fin Fout : a sequence of frames composing from
-- Fin to Fout, applied in order (innermost first).

data IndBTContext : Formula -> Formula -> Set where
  emptyCtx :
    (F : Formula) ->
    IndBTContext F F
  consCtx :
    {F1 F2 F3 : Formula} ->
    IndBTFrame F1 F2 ->         -- innermost frame, applied first
    IndBTContext F2 F3 ->       -- rest of the path, outward
    IndBTContext F1 F3

------------------------------------------------------------------------
-- Plug a derivation through a context: apply each frame in order.

plugContext :
  {Fin Fout : Formula} {r l : Nat} ->
  IndBTContext Fin Fout ->
  DerivTBounded r l Fin ->
  PluggedDeriv Fout
plugContext {r = r} {l = l} (emptyCtx _) d =
  mkPlugged r l d
plugContext (consCtx frame rest) d =
  let p   = plugFrame frame d
      r'  = pluggedRank p
      l'  = pluggedLevel p
      d'  = pluggedDeriv p
  in plugContext rest d'

------------------------------------------------------------------------
-- Singleton context: a single frame as a context.

singletonCtx :
  {F1 F2 : Formula} ->
  IndBTFrame F1 F2 ->
  IndBTContext F1 F2
singletonCtx {F1} {F2} frame = consCtx frame (emptyCtx F2)

------------------------------------------------------------------------
-- Concatenation of contexts.  ctx1 ++ ctx2 = first apply ctx1, then ctx2.

appendCtx :
  {F1 F2 F3 : Formula} ->
  IndBTContext F1 F2 ->
  IndBTContext F2 F3 ->
  IndBTContext F1 F3
appendCtx (emptyCtx _)         ctx2 = ctx2
appendCtx (consCtx frame rest) ctx2 = consCtx frame (appendCtx rest ctx2)
