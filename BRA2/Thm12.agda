{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm12 -- Theorem 12 as a mutual structural recursion on Fun1 / Fun2.
--
--   thm12_F1 : (f : Fun1) -> Thm12_F1_Result f
--   thm12_F2 : (g : Fun2) -> Thm12_F2_Result g
--
-- One clause per Fun1 / Fun2 constructor.  After Phase 3 of the treeRec
-- refactor, Rec and RecP are no longer constructors (they are Agda
-- functions on top of treeRec), so they have no clauses here.
--
-- The atomic cases (I, Fst, Snd, Z, Pair, Const) and IfLf are closed
-- top-level definitions in BRA2.Thm12.Parts.  The composite cases
-- (Comp, Comp2, Lift, Post, Fan) dispatch to per-case modules.  The
-- recursive primitives (treeRec, TreeEq) take their NN-input bundles
-- and universal correctness as module parameters.

module BRA2.Thm12 where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.DerivThreshold
open import BRA2.Cor

open import BRA2.Thm.ThmT using (thmT)
open import BRA2.SubstClosure using (Fun1_closed ; Fun2_closed)

-- Closed Parts (no module instantiation).
open import BRA2.Thm12.Parts.I        using (D_I     ; D_correct_I)
open import BRA2.Thm12.Parts.Fst      using (D_Fst   ; D_correct_Fst)
open import BRA2.Thm12.Parts.Snd      using (D_Snd   ; D_correct_Snd)
open import BRA2.Thm12.Parts.Z        using (D_Z     ; D_correct_Z)
open import BRA2.Thm12.Parts.Pair     using (D2_Pair  ; D_correct2_Pair)
open import BRA2.Thm12.Parts.Const    using (D2_Const ; D_correct2_Const)
import BRA2.Thm12.Parts.IfLf
open BRA2.Thm12.Parts.IfLf using (D_IfLf)

-- Recursive Parts (per-case modules; instantiated in the where-blocks).
import BRA2.Thm12.Parts.Comp
import BRA2.Thm12.Parts.Comp2
import BRA2.Thm12.Parts.Lift
import BRA2.Thm12.Parts.Post
import BRA2.Thm12.Parts.Fan
import BRA2.Thm12.Parts.TreeEq

-- Internal treeRec construction (D2 + universal correctness via
-- doubly-lifted dispatchers + ruleIndBT).
import BRA2.Th12TreeRecInternal

-- Concrete TreeEq closure (NN bundle + universal correctness via
-- nested ruleIndBT2).
import BRA2.Th12TreeEqClose

------------------------------------------------------------------------
-- Encoded equation specs (the asymmetric Theorem 12 conclusion forms).

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
-- Result records.

record Thm12_F1_Result (f : Fun1) : Set where
  constructor mkR1
  field
    Df    : Fun1
    proof : (x : Term) ->
      Deriv (atomic (eqn (ap1 thmT (ap1 Df x)) (codeFTeq1 f x)))

record Thm12_F2_Result (g : Fun2) : Set where
  constructor mkR2
  field
    Dg    : Fun2
    proof : (x v : Term) ->
      Deriv (atomic (eqn (ap1 thmT (ap2 Dg x v)) (codeFTeq2 g x v)))

------------------------------------------------------------------------
-- Mutual structural recursion thm12_F1 / thm12_F2 as a parametric
-- module.  treeRec is now fully internalised
-- (BRA2.Th12TreeRecInternal.Construction); only TreeEq / IfLf
-- substitution-closure assumptions remain as FromBridges parameters
-- (Pair case to universal lift, discharged via ruleIndBT at the
-- consumer site).

module FromBridges where
  -- Closure-free: both IfLf and TreeEq deliver truly universal
  -- (x v : Term) -> Deriv ... wrappers via the pickFresh trick
  -- (BRA2.MaxVar).  No module parameters remain.

  ----------------------------------------------------------------------
  -- The two mutually-recursive functions.

  thm12_F1 : (f : Fun1) -> Thm12_F1_Result f
  thm12_F2 : (g : Fun2) -> Thm12_F2_Result g

  ----------------------------------------------------------------------
  -- Fun1 cases (6 total: 4 atomic + 2 composite).

  thm12_F1 I   = mkR1 D_I    D_correct_I
  thm12_F1 Fst = mkR1 D_Fst  D_correct_Fst
  thm12_F1 Snd = mkR1 D_Snd  D_correct_Snd
  thm12_F1 Z   = mkR1 D_Z    D_correct_Z

  thm12_F1 (Comp f g) = mkR1 R.D_Comp_f'g R.D_correct_Comp_f'g
    where
      rf = thm12_F1 f
      rg = thm12_F1 g
      module R = BRA2.Thm12.Parts.Comp.CompCase
                   f g (Thm12_F1_Result.Df rf) (Thm12_F1_Result.Df rg)
                   (Thm12_F1_Result.proof rf) (Thm12_F1_Result.proof rg)

  thm12_F1 (Comp2 h f g) = mkR1 R.D_Comp2_hfg R.D_correct_Comp2_hfg
    where
      rh = thm12_F2 h
      rf = thm12_F1 f
      rg = thm12_F1 g
      module R = BRA2.Thm12.Parts.Comp2.Comp2Case
                   h f g (Thm12_F2_Result.Dg rh)
                   (Thm12_F1_Result.Df rf) (Thm12_F1_Result.Df rg)
                   (Thm12_F2_Result.proof rh)
                   (Thm12_F1_Result.proof rf) (Thm12_F1_Result.proof rg)

  ----------------------------------------------------------------------
  -- Fun2 cases (8 total: 4 atomic + 4 composite).

  thm12_F2 Pair  = mkR2 D2_Pair  D_correct2_Pair
  thm12_F2 Const = mkR2 D2_Const D_correct2_Const
  thm12_F2 IfLf  = mkR2 D_IfLf BRA2.Thm12.Parts.IfLf.D_correct2_IfLf

  thm12_F2 (Lift f) = mkR2 R.D2_Lift_f R.D_correct2_Lift_f
    where
      rf = thm12_F1 f
      module R = BRA2.Thm12.Parts.Lift.LiftCase
                   f (Thm12_F1_Result.Df rf) (Thm12_F1_Result.proof rf)

  thm12_F2 (Post f h) = mkR2 R.D2_Post_fh R.D_correct2_Post_fh
    where
      rf = thm12_F1 f
      rh = thm12_F2 h
      module R = BRA2.Thm12.Parts.Post.PostCase
                   f h (Thm12_F1_Result.Df rf) (Thm12_F2_Result.Dg rh)
                   (Thm12_F1_Result.proof rf) (Thm12_F2_Result.proof rh)

  thm12_F2 (Fan h1 h2 h) = mkR2 R.D2_Fan_h1h2h R.D_correct2_Fan_h1h2h
    where
      r1 = thm12_F2 h1
      r2 = thm12_F2 h2
      r  = thm12_F2 h
      module R = BRA2.Thm12.Parts.Fan.FanCase
                   h1 h2 h (Thm12_F2_Result.Dg r1) (Thm12_F2_Result.Dg r2)
                   (Thm12_F2_Result.Dg r)
                   (Thm12_F2_Result.proof r1) (Thm12_F2_Result.proof r2)
                   (Thm12_F2_Result.proof r)

  thm12_F2 TreeEq = mkR2 D_TreeEq_C D_correct2_TreeEq_C
    where
      open BRA2.Th12TreeEqClose
        renaming (D_TreeEq to D_TreeEq_C ; D_correct2_TreeEq to D_correct2_TreeEq_C)

  thm12_F2 (treeRec f s) = mkR2 R.D2_treeRec_fs R.D_correct2_treeRec_fs
    where
      rf = thm12_F1 f
      rs = thm12_F2 s
      module R = BRA2.Th12TreeRecInternal.Construction
                   f s (Thm12_F1_Result.Df rf) (Thm12_F1_Result.proof rf)
                       (Thm12_F2_Result.Dg rs) (Thm12_F2_Result.proof rs)
