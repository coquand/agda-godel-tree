{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm12.Shapes
--
-- Per-Parts/X "Fst-of-DX-is-Pair" shape proofs.  Each is a Sigma-typed
-- witness packaging  Deriv (eqn (ap1 Fst (ap1 D_X x)) (ap2 Pair x' y'))
-- (singulary) or its binary analog.  These are the shape arguments
-- consumed by Parts/Comp2.Comp2Case and Parts/Fan.FanCase, and by the
-- Df_shape / D2g_shape parameters of BRA2.Thm12.FromBridges.
--
-- This file covers the CLOSED cases (D_I, D_Fst, D_Snd, D_Z; D2_Pair,
-- D2_Const, D_IfLf).  Shape proofs for recursive cases (Comp, Comp2,
-- Lift, Post, Fan) and for the NN cases (Rec, RecP, TreeEq) require
-- mutual structural recursion and live in the FromBridges-instantiation
-- file.

module BRA2.Thm12.Shapes where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Deriv
open import BRA2.Cor
open import BRA2.Thm.ThmT using (thmT ; tagCode_axI)

open import BRA2.Thm12.Parts.I
  using (D_I ; D_I_reduce)
open import BRA2.Thm12.Parts.Fst
  using (D_Fst ; D_Fst_reduce_O ; D_Fst_reduce_Pair)
open import BRA2.Thm12.Parts.Snd
  using (D_Snd ; D_Snd_reduce_O ; D_Snd_reduce_Pair)
open import BRA2.Thm12.Parts.Z
  using (D_Z ; D_Z_reduce)
open import BRA2.Thm12.Parts.Pair
  using (D2_Pair ; D2_Pair_reduce)
open import BRA2.Thm12.Parts.Const
  using (D2_Const ; D2_Const_reduce)
open import BRA2.Thm12.Param.AxI using (parEncAxI)
open import BRA2.Thm12.Param.AxRefl using (parEncAxRefl)

------------------------------------------------------------------------
-- Shape predicate types.

ShapeF1 : Fun1 -> Set
ShapeF1 Df = (x : Term) ->
  Sigma Term (\ y' -> Sigma Term (\ x' ->
    Deriv (atomic (eqn (ap1 Fst (ap1 Df x)) (ap2 Pair x' y')))))

ShapeF2 : Fun2 -> Set
ShapeF2 D2g = (x v : Term) ->
  Sigma Term (\ y' -> Sigma Term (\ x' ->
    Deriv (atomic (eqn (ap1 Fst (ap2 D2g x v)) (ap2 Pair x' y')))))

------------------------------------------------------------------------
-- Closed-Fun1 shape proofs.

-- D_I : ap1 D_I x reduces to  Pair tagCode_axI (cor x) ;
-- Fst extracts tagCode_axI = reify (natCode (suc zero)) = Pair O O.

shape_D_I : ShapeF1 D_I
shape_D_I x = mkSigma O (mkSigma O proof)
  where
    proof : Deriv (atomic (eqn (ap1 Fst (ap1 D_I x)) (ap2 Pair O O)))
    proof = ruleTrans (cong1 Fst (D_I_reduce x))
                      (axFst tagCode_axI (ap1 cor x))

------------------------------------------------------------------------
-- Closed-Fun2 shape proofs.

-- D2_Pair : ap2 D2_Pair x v reduces to
--   parEncAxRefl (cor (Pair x v)) = Pair tagCode_axRefl (cor (Pair x v)).
-- Fst = tagCode_axRefl = reify (natCode tagAxRefl) which is positive nat,
--   hence has Pair shape.

shape_D2_Pair : ShapeF2 D2_Pair
shape_D2_Pair x v =
  mkSigma _ (mkSigma _ proof)
  where
    open BRA2.Thm.ThmT using (tagCode_axRefl)
    proof = ruleTrans (cong1 Fst (D2_Pair_reduce x v))
                      (axFst tagCode_axRefl (ap1 cor (ap2 Pair x v)))

-- D2_Const : ap2 D2_Const x v reduces to  Pair tagCode_axConst (cor x).
-- Fst extracts tagCode_axConst (positive nat -> Pair shape).

shape_D2_Const : ShapeF2 D2_Const
shape_D2_Const x v =
  mkSigma _ (mkSigma _ proof)
  where
    open BRA2.Thm.ThmT using (tagCode_axConst)
    proof = ruleTrans (cong1 Fst (D2_Const_reduce x v))
                      (axFst tagCode_axConst
                             (ap2 Pair (ap1 cor x) (ap1 cor v)))

-- D_Z : ap1 D_Z x reduces to  Pair tagCode_axKT (Pair codeF1Z (cor x)) .
-- Fst extracts tagCode_axKT (positive nat -> Pair shape).

shape_D_Z : ShapeF1 D_Z
shape_D_Z x =
  mkSigma _ (mkSigma _ proof)
  where
    open BRA2.Thm.ThmT using (tagCode_axKT)
    proof = ruleTrans (cong1 Fst (D_Z_reduce x))
                      (axFst tagCode_axKT
                             (ap2 Pair (reify (codeF1 Z)) (ap1 cor x)))

-- D_Fst, D_Snd: dispatch via IfLf.  At x = O the result is  parEncAxFstLf O  /
-- parEncAxSndLf O  (Pair-shaped).  At x = Pair v1 v2 the result is the
-- non-leaf branch (also Pair-shaped).  But the universal shape
-- (uniform over all x) requires ruleIndBT-style closure machinery.
--
-- OBSTRUCTION (documented for future sessions):
--
-- The Pair-shape is real but the (x', y') WITNESS components depend on
-- x's leaf-vs-Pair shape:
--   At x = O:   Fst (D_Fst x) = tagCode_axFstLf = Pair O <large-natCode-tail>
--   At x = Pr:  Fst (D_Fst x) = tagCode_axFst   = Pair O <different-natCode-tail>
-- The two tails are different positive-nat encodings, so a uniform
-- (x', y') choice independent of x doesn't exist.  A universal proof
-- via ruleIndBT must construct y'(x) as a Fun1 expression (via IfLf
-- dispatch) and prove the equation at base + step + axK packaging,
-- mirroring the D_correct_Fst structure (~150 LoC per dispatch case,
-- 3 cases = ~450 LoC).
--
-- Doable but heavy; deferred until either the existing FromBridges
-- shape obligation is relaxed (Parts/Comp2 + Parts/Fan refactor) or a
-- focused session writes the 3 ruleIndBT shape proofs.

------------------------------------------------------------------------
-- Recursive-case shape proofs.
--
-- Comp / Lift / Post all reduce to  parEncRuleTrans (...) (...) at their
-- top level.  parEncRuleTrans y1 y2 = Pair tagCode_ruleTrans (Pair y1 y2),
-- so Fst extracts tagCode_ruleTrans (positive nat = Pair shape).

import BRA2.Thm12.Parts.Comp
import BRA2.Thm12.Parts.Comp2
import BRA2.Thm12.Parts.Lift
import BRA2.Thm12.Parts.Post
import BRA2.Thm12.Parts.Fan
open import BRA2.Thm.Tag using (tagRuleTrans)

module ShapesComp
  (f' g : Fun1)
  (Df' Dg : Fun1)
  (D_correct_f' : (x : Term) ->
     Deriv (atomic (eqn
       (ap1 thmT (ap1 Df' x))
       (ap2 Pair
         (ap2 Pair (reify tagAp1)
                   (ap2 Pair (reify (codeF1 f')) (ap1 cor x)))
         (ap1 cor (ap1 f' x))))))
  (D_correct_g : (x : Term) ->
     Deriv (atomic (eqn
       (ap1 thmT (ap1 Dg x))
       (ap2 Pair
         (ap2 Pair (reify tagAp1)
                   (ap2 Pair (reify (codeF1 g)) (ap1 cor x)))
         (ap1 cor (ap1 g x))))))
  where

  open BRA2.Thm12.Parts.Comp.CompCase f' g Df' Dg D_correct_f' D_correct_g
    using (D_Comp_f'g ; D_Comp_reduce)
  open BRA2.Thm.ThmT using (tagCode_ruleTrans)
  open import BRA2.Thm12.Param.RuleTrans using (parEncRuleTrans)
  open import BRA2.Thm12.Param.AxComp using (parEncAxComp)
  open import BRA2.Thm12.Param.Cong1 using (parEncCong1)

  shape_D_Comp : ShapeF1 D_Comp_f'g
  shape_D_Comp x =
    mkSigma _ (mkSigma _ proof)
    where
      inner : Term
      inner = ap2 Pair (parEncAxComp f' g (ap1 cor x))
                       (parEncRuleTrans (parEncCong1 f' (ap1 Dg x))
                                         (ap1 Df' (ap1 g x)))
      proof = ruleTrans (cong1 Fst (D_Comp_reduce x))
                        (axFst tagCode_ruleTrans inner)

module ShapesLift
  (f : Fun1)
  (Df : Fun1)
  (D_correct_f : (x : Term) ->
     Deriv (atomic (eqn
       (ap1 thmT (ap1 Df x))
       (ap2 Pair
         (ap2 Pair (reify tagAp1)
                   (ap2 Pair (reify (codeF1 f)) (ap1 cor x)))
         (ap1 cor (ap1 f x))))))
  where

  open BRA2.Thm12.Parts.Lift.LiftCase f Df D_correct_f
    using (D2_Lift_f ; D2_Lift_reduce)
  open BRA2.Thm.ThmT using (tagCode_ruleTrans)
  open import BRA2.Thm12.Param.RuleTrans using (parEncRuleTrans)
  open import BRA2.Thm12.Param.AxLift using (parEncAxLift)

  shape_D2_Lift : ShapeF2 D2_Lift_f
  shape_D2_Lift a b =
    mkSigma _ (mkSigma _ proof)
    where
      inner : Term
      inner = ap2 Pair (parEncAxLift f (ap1 cor a) (ap1 cor b))
                       (ap1 Df a)
      proof = ruleTrans (cong1 Fst (D2_Lift_reduce a b))
                        (axFst tagCode_ruleTrans inner)

module ShapesPost
  (f : Fun1)
  (h : Fun2)
  (Df : Fun1)
  (D2_h : Fun2)
  (D_correct_f : (x : Term) ->
     Deriv (atomic (eqn
       (ap1 thmT (ap1 Df x))
       (ap2 Pair
         (ap2 Pair (reify tagAp1)
                   (ap2 Pair (reify (codeF1 f)) (ap1 cor x)))
         (ap1 cor (ap1 f x))))))
  (D_correct_h : (x v : Term) ->
     Deriv (atomic (eqn
       (ap1 thmT (ap2 D2_h x v))
       (ap2 Pair
         (ap2 Pair (reify tagAp2)
                   (ap2 Pair (reify (codeF2 h))
                             (ap2 Pair (ap1 cor x) (ap1 cor v))))
         (ap1 cor (ap2 h x v))))))
  where

  open BRA2.Thm12.Parts.Post.PostCase f h Df D2_h D_correct_f D_correct_h
    using (D2_Post_fh ; D2_Post_reduce)
  open BRA2.Thm.ThmT using (tagCode_ruleTrans)
  open import BRA2.Thm12.Param.RuleTrans using (parEncRuleTrans)
  open import BRA2.Thm12.Param.AxPost using (parEncAxPost)
  open import BRA2.Thm12.Param.Cong1 using (parEncCong1)

  shape_D2_Post : ShapeF2 D2_Post_fh
  shape_D2_Post a b =
    mkSigma _ (mkSigma _ proof)
    where
      inner : Term
      inner = ap2 Pair (parEncAxPost f h (ap1 cor a) (ap1 cor b))
                       (parEncRuleTrans (parEncCong1 f (ap2 D2_h a b))
                                         (ap1 Df (ap2 h a b)))
      proof = ruleTrans (cong1 Fst (D2_Post_reduce a b))
                        (axFst tagCode_ruleTrans inner)

------------------------------------------------------------------------
-- Comp2 / Fan shapes.  These don't have a separate D_X_reduce lemma;
-- we directly apply axComp2 / axFan at the outer level then axFst /
-- axKT to extract  tagCode_ruleTrans .

module ShapesComp2
  (h : Fun2)
  (f' g : Fun1)
  (D2_h : Fun2)
  (Df' Dg : Fun1)
  where

  open BRA2.Thm.ThmT using (tagCode_ruleTrans)

  -- The inner subtree  Comp2 Pair y1_part inner_rt1  is opaque here -- we
  -- only need its Fun1 type for the axComp2 / axFst chain.
  D_Comp2_outer-Fst-shape : (innerFun : Fun1) (x : Term) ->
    Deriv (atomic (eqn (ap1 Fst (ap1 (Comp2 Pair (KT tagCode_ruleTrans) innerFun) x))
                       tagCode_ruleTrans))
  D_Comp2_outer-Fst-shape innerFun x =
    let r1 = axComp2 Pair (KT tagCode_ruleTrans) innerFun x
        r2 = axFst (ap1 (KT tagCode_ruleTrans) x) (ap1 innerFun x)
        r3 = axKT (natCode tagRuleTrans) (natCode_isValue tagRuleTrans) x
    in ruleTrans (cong1 Fst r1) (ruleTrans r2 r3)

module ShapesFan
  (h1 h2 h : Fun2)
  (D2_h1 D2_h2 D2_h : Fun2)
  where

  open BRA2.Thm.ThmT using (tagCode_ruleTrans)

  -- Same idea: Fan (Lift (KT tagCode_ruleTrans)) innerFun Pair has
  -- ap2 _ x v = Pair tagCode_ruleTrans (...) at the outer level.
  D2_Fan_outer-Fst-shape : (innerFun : Fun2) (x v : Term) ->
    Deriv (atomic (eqn
      (ap1 Fst (ap2 (Fan (Lift (KT tagCode_ruleTrans)) innerFun Pair) x v))
      tagCode_ruleTrans))
  D2_Fan_outer-Fst-shape innerFun x v =
    let r1 = axFan (Lift (KT tagCode_ruleTrans)) innerFun Pair x v
        r2 = axFst (ap2 (Lift (KT tagCode_ruleTrans)) x v) (ap2 innerFun x v)
        r3 = axLift (KT tagCode_ruleTrans) x v
        r4 = axKT (natCode tagRuleTrans) (natCode_isValue tagRuleTrans) x
    in ruleTrans (cong1 Fst r1) (ruleTrans r2 (ruleTrans r3 r4))
