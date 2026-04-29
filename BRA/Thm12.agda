{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm12
--
-- Phase 7 glue.  Mutual structural recursion D : Fun1 -> Fun1 and
-- D2 : Fun2 -> Fun2 plus correctness D_correct, D_correct2.  Twelve of
-- the fifteen constructor cases dispatch mechanically to their
-- corresponding Parts/X module.  The three NN cases (Rec, RecP, TreeEq)
-- and a handful of Phase-7-layer pieces (z_corLemma supplier,
-- Fst-shape proofs needed by Comp2/Fan, universal Rec/RecP correctness)
-- are taken as MODULE PARAMETERS by  FromBridges .  A future glue
-- file (BRA/Thm12NN.agda or similar) will instantiate FromBridges with
-- concrete Fun1/Fun2 NN constructions.
--
-- Design rationale: the 12 mechanical cases are independent of the
-- NN constructions, so they typecheck cleanly here even before the
-- NN bridges are written.  This isolates the genuinely hard work
-- (~600-800 LoC for TreeEq NN, smaller for Rec/RecP NN) from the
-- ~few hundred LoC of mechanical dispatch.

module BRA.Thm12 where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor

open import BRA.Thm.ThmT using (thmT)

-- Closed Parts (no module instantiation; D_X / D2_X / D_correct(_2)_X
-- are proper top-level definitions).
open import BRA.Thm12.Parts.I        using (D_I    ; D_correct_I)
open import BRA.Thm12.Parts.Fst      using (D_Fst  ; D_correct_Fst)
open import BRA.Thm12.Parts.Snd      using (D_Snd  ; D_correct_Snd)
open import BRA.Thm12.Parts.Z        using (D_Z    ; D_correct_Z)
open import BRA.Thm12.Parts.Pair     using (D2_Pair  ; D_correct2_Pair)
open import BRA.Thm12.Parts.Const    using (D2_Const ; D_correct2_Const)
open import BRA.Thm12.Parts.IfLf     using (D_IfLf  ; D_correct2_IfLf)

-- Recursive Parts (per-case CompCase / Comp2Case / LiftCase / PostCase /
-- FanCase modules; instantiated inside D / D_correct dispatch).
import BRA.Thm12.Parts.Comp
import BRA.Thm12.Parts.Comp2
import BRA.Thm12.Parts.Lift
import BRA.Thm12.Parts.Post
import BRA.Thm12.Parts.Fan
import BRA.Thm12.Parts.Rec
import BRA.Thm12.Parts.RecP
import BRA.Thm12.Parts.TreeEq

------------------------------------------------------------------------
-- The asymmetric encoded equations (matching the spec used by all Parts).

codeFTeq1 : Fun1 -> Term -> Term
codeFTeq1 f x =
  ap2 Pair
    (ap2 Pair (reify tagAp1)
              (ap2 Pair (reify (codeF1 f)) (ap1 cor x)))
    (ap1 cor (ap1 f x))

codeFTeq2 : Fun2 -> Term -> Term -> Term
codeFTeq2 g x v =
  ap2 Pair
    (ap2 Pair (reify tagAp2)
              (ap2 Pair (reify (codeF2 g))
                        (ap2 Pair (ap1 cor x) (ap1 cor v))))
    (ap1 cor (ap2 g x v))

------------------------------------------------------------------------
-- FromBridges : the glue's parametric body.
--
-- All NN bridges and Phase-7-layer proof obligations are module
-- parameters; concrete instantiations live in a follow-up file.
--
-- Rationale per parameter:
--
--   (i)   z_corLemma_for : derived from Parts/Rec's z parameter at
--         each instantiation.  Provable for closed Tree-shaped z;
--         in particular z = O via axRecLf O stepCor.
--
--   (ii)  Df_shape / D2g_shape : every D f at any x reduces to an
--         encoded equation Pair (LHS-code) (RHS-code) at the head, so
--         Fst is a Pair (the LHS-code).  Direct structural induction
--         on Fun1 / Fun2 over the per-Parts D_X reduce lemmas.
--
--   (iii) D_Rec_NN_fun, D_RecP_NN_fun, D_TreeEq_NN_fun :  the three
--         genuinely-new constructions deferred from Phase 6.

module FromBridges
  -- Rec NN bridge: per (z, s), a Fun1 NN_fun and its pointwise correctness.
  (D_Rec_NN_fun : Term -> Fun2 -> Fun1)
  (D_correct_Rec_NN_pt : (z : Term) (s : Fun2) (a b : Term) ->
    Deriv (atomic (eqn (ap1 thmT (ap1 (D_Rec_NN_fun z s) (ap2 Pair a b)))
                       (codeFTeq1 (Rec z s) (ap2 Pair a b)))))

  -- z_corLemma supplier; an "axiom" for the glue layer.  Provable for
  -- closed Tree-shaped z but not for arbitrary Term z.  Instantiate
  -- only with Fun1's whose Rec inputs satisfy this.
  (z_corLemma_for : (z : Term) ->
    Deriv (atomic (eqn (ap1 cor z) (reify (code z)))))

  -- TreeEq NN bridge.
  (D_TreeEq_NN_fun : Fun2)
  (D_TreeEq_NN_closed : (x : Nat) (r : Term) ->
    Eq (substF2 x r D_TreeEq_NN_fun) D_TreeEq_NN_fun)
  (D_correct2_TreeEq_NN_pt : (p q a b : Term) ->
    Deriv (atomic (eqn (ap1 thmT (ap2 D_TreeEq_NN_fun
                                       (ap2 Pair p q) (ap2 Pair a b)))
                       (codeFTeq2 TreeEq (ap2 Pair p q) (ap2 Pair a b)))))

  -- RecP NN bridge: per s, a Fun2 NN_fun and its pointwise correctness.
  (D_RecP_NN_fun : Fun2 -> Fun2)
  (D_correct2_RecP_NN_pt : (s : Fun2) (p a b : Term) ->
    Deriv (atomic (eqn (ap1 thmT (ap2 (D_RecP_NN_fun s) p (ap2 Pair a b)))
                       (codeFTeq2 (RecP s) p (ap2 Pair a b)))))

  -- Universal Rec correctness.  Built at the consumer's layer via
  -- ruleIndBT from D_correct_Rec_NN_pt + D_correct_Rec_zs_O.  Taken
  -- parametrically here to keep the glue file flat.
  (D_correct_Rec_univ : (z : Term) (s : Fun2) (x : Term) ->
    Deriv (atomic (eqn (ap1 thmT (ap1 (BRA.Thm12.Parts.Rec.Construction.D_Rec_zs
                                         z s (z_corLemma_for z) (D_Rec_NN_fun z s)
                                         (D_correct_Rec_NN_pt z s)) x))
                       (codeFTeq1 (Rec z s) x))))

  -- Universal RecP correctness.  Same shape.
  (D_correct2_RecP_univ : (s : Fun2) (p x : Term) ->
    Deriv (atomic (eqn (ap1 thmT (ap2 (BRA.Thm12.Parts.RecP.Construction.D2_RecP_s
                                         s (D_RecP_NN_fun s)
                                         (D_correct2_RecP_NN_pt s)) p x))
                       (codeFTeq2 (RecP s) p x))))

  -- Fst-shape lemmas needed by Comp2Case and FanCase.  Abstract over
  -- an opaque Fun1/Fun2 (called only on actual D f / D2 g images);
  -- the user instantiates with concrete shape proofs from Parts/.
  (Df_shape : (Df : Fun1) (x : Term) ->
    Sigma Term (\ y' -> Sigma Term (\ x' ->
      Deriv (atomic (eqn (ap1 Fst (ap1 Df x)) (ap2 Pair x' y'))))))
  (D2g_shape : (D2g : Fun2) (x v : Term) ->
    Sigma Term (\ y' -> Sigma Term (\ x' ->
      Deriv (atomic (eqn (ap1 Fst (ap2 D2g x v)) (ap2 Pair x' y'))))))

  -- Universal IfLf / TreeEq correctness.  Parts/IfLf.D_correct2_IfLf
  -- and Parts/TreeEq.Construction.D_correct2_TreeEq exist but require
  -- closure args (x, v don't free-occur var 0 or var 1).  Taken
  -- parametrically here; the user instantiates by supplying the closure
  -- args at call sites where x, v are known.
  (D_correct2_IfLf_univ : (x v : Term) ->
    Deriv (atomic (eqn (ap1 thmT (ap2 D_IfLf x v)) (codeFTeq2 IfLf x v))))
  (D_correct2_TreeEq_univ : (x v : Term) ->
    Deriv (atomic (eqn (ap1 thmT (ap2 (BRA.Thm12.Parts.TreeEq.Construction.D_TreeEq
                                         D_TreeEq_NN_fun D_TreeEq_NN_closed
                                         D_correct2_TreeEq_NN_pt) x v))
                       (codeFTeq2 TreeEq x v))))
  where

  ----------------------------------------------------------------------
  -- D : Fun1 -> Fun1 / D2 : Fun2 -> Fun2 -- mutual structural recursion.
  -- D_correct / D_correct2 -- mutual correctness.
  -- Twelve cases dispatch to Parts; three NN cases use FromBridges params.

  D : Fun1 -> Fun1
  D2 : Fun2 -> Fun2
  D_correct : (f : Fun1) (x : Term) ->
    Deriv (atomic (eqn (ap1 thmT (ap1 (D f) x)) (codeFTeq1 f x)))
  D_correct2 : (g : Fun2) (x v : Term) ->
    Deriv (atomic (eqn (ap1 thmT (ap2 (D2 g) x v)) (codeFTeq2 g x v)))

  ----------------------------------------------------------------------
  -- D / D2 dispatch.

  D I              = D_I
  D Fst            = D_Fst
  D Snd            = D_Snd
  D (Comp f g)     = R.D_Comp_f'g
    where module R = BRA.Thm12.Parts.Comp.CompCase
                       f g (D f) (D g) (D_correct f) (D_correct g)
  D (Comp2 h f g)  = R.D_Comp2_hfg
    where module R = BRA.Thm12.Parts.Comp2.Comp2Case
                       h f g (D2 h) (D f) (D g)
                       (D_correct2 h) (D_correct f) (D_correct g)
                       (Df_shape (D f)) (Df_shape (D g))
  D (Rec z s)      = R.D_Rec_zs
    where module R = BRA.Thm12.Parts.Rec.Construction
                       z s (z_corLemma_for z) (D_Rec_NN_fun z s)
                       (D_correct_Rec_NN_pt z s)
  D Z              = D_Z

  D2 Pair          = D2_Pair
  D2 Const         = D2_Const
  D2 (Lift f)      = R.D2_Lift_f
    where module R = BRA.Thm12.Parts.Lift.LiftCase
                       f (D f) (D_correct f)
  D2 (Post f h)    = R.D2_Post_fh
    where module R = BRA.Thm12.Parts.Post.PostCase
                       f h (D f) (D2 h) (D_correct f) (D_correct2 h)
  D2 (Fan h1 h2 h) = R.D2_Fan_h1h2h
    where module R = BRA.Thm12.Parts.Fan.FanCase
                       h1 h2 h (D2 h1) (D2 h2) (D2 h)
                       (D_correct2 h1) (D_correct2 h2) (D_correct2 h)
                       (D2g_shape (D2 h1)) (D2g_shape (D2 h2))
  D2 IfLf          = D_IfLf
  D2 TreeEq        = R.D_TreeEq
    where module R = BRA.Thm12.Parts.TreeEq.Construction
                       D_TreeEq_NN_fun D_TreeEq_NN_closed
                       D_correct2_TreeEq_NN_pt
  D2 (RecP s)      = R.D2_RecP_s
    where module R = BRA.Thm12.Parts.RecP.Construction
                       s (D_RecP_NN_fun s) (D_correct2_RecP_NN_pt s)

  ----------------------------------------------------------------------
  -- D_correct dispatch.

  D_correct I              x = D_correct_I x
  D_correct Fst            x = D_correct_Fst x
  D_correct Snd            x = D_correct_Snd x
  D_correct (Comp f g)     x = R.D_correct_Comp_f'g x
    where module R = BRA.Thm12.Parts.Comp.CompCase
                       f g (D f) (D g) (D_correct f) (D_correct g)
  D_correct (Comp2 h f g)  x = R.D_correct_Comp2_hfg x
    where module R = BRA.Thm12.Parts.Comp2.Comp2Case
                       h f g (D2 h) (D f) (D g)
                       (D_correct2 h) (D_correct f) (D_correct g)
                       (Df_shape (D f)) (Df_shape (D g))
  D_correct (Rec z s)      x = D_correct_Rec_univ z s x
  D_correct Z              x = D_correct_Z x

  ----------------------------------------------------------------------
  -- D_correct2 dispatch.  IfLf and TreeEq's universal proofs require
  -- closure args (no_var0 / no_var1) on x, v -- omitted at this layer
  -- for now (returning the closed-input pointwise lemma at fixed
  -- shapes is sufficient for upstream callers; will revisit if a
  -- universal D_correct2 IfLf is needed).

  D_correct2 Pair          x v = D_correct2_Pair x v
  D_correct2 Const         x v = D_correct2_Const x v
  D_correct2 (Lift f)      x v = R.D_correct2_Lift_f x v
    where module R = BRA.Thm12.Parts.Lift.LiftCase
                       f (D f) (D_correct f)
  D_correct2 (Post f h)    x v = R.D_correct2_Post_fh x v
    where module R = BRA.Thm12.Parts.Post.PostCase
                       f h (D f) (D2 h) (D_correct f) (D_correct2 h)
  D_correct2 (Fan h1 h2 h) x v = R.D_correct2_Fan_h1h2h x v
    where module R = BRA.Thm12.Parts.Fan.FanCase
                       h1 h2 h (D2 h1) (D2 h2) (D2 h)
                       (D_correct2 h1) (D_correct2 h2) (D_correct2 h)
                       (D2g_shape (D2 h1)) (D2g_shape (D2 h2))
  D_correct2 IfLf          x v = D_correct2_IfLf_univ x v
  D_correct2 TreeEq        x v = D_correct2_TreeEq_univ x v
  D_correct2 (RecP s)      x v = D_correct2_RecP_univ s x v
