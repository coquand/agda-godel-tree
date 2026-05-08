{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm12.ShapeAdapters -- per-x / per-(x,v) shape adapters for the
-- atomic dispatching primitives.
--
-- Each adapter converts a universal-form shape Deriv (with var 0 / var 1
-- free) to the per-x / per-(x,v) ShapeF1 / ShapeF2 form needed by
-- BRA2.Thm12.FromBridges' Comp2 / Fan dispatchers.
--
-- The four atomic shape lemmas (shape_D_F1_Fst_var0 etc.) live in their
-- own files and are imported here.

module BRA2.Thm12.ShapeAdapters where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Deriv
open import BRA2.Thm12.Shapes using (ShapeF1 ; ShapeF2)

open import BRA2.Thm12.Parts.Fst    using (D_Fst)
open import BRA2.Thm12.Parts.Snd    using (D_Snd)
open import BRA2.Thm12.Parts.IfLf   using (D_IfLf)
import BRA2.Thm12.Parts.TreeEq
open import BRA2.Th12TreeEqNNFun
  using (D_TreeEq_NN_fun ; D_TreeEq_NN_closed)
module CB = BRA2.Thm12.Parts.TreeEq.ConstructionBase
              D_TreeEq_NN_fun D_TreeEq_NN_closed
open CB using (D_TreeEq)

open import BRA2.Thm12.ShapeF1Fst    using (shape_D_F1_Fst_var0)
open import BRA2.Thm12.ShapeF1Snd    using (shape_D_F1_Snd_var0)
open import BRA2.Thm12.ShapeF2IfLf   using (shape_D_F2_IfLf_var01)
open import BRA2.Thm12.ShapeF2TreeEq using (shape_D_F2_TreeEq_var01)

------------------------------------------------------------------------
-- Per-x adapter for D_Fst.

shape_D_Fst : (x : Term) ->
  Sigma Term (\ y' -> Sigma Term (\ x' ->
    Deriv (atomic (eqn (ap1 Fst (ap1 D_Fst x)) (ap2 Pair x' y')))))
shape_D_Fst x =
  mkSigma (ap1 Snd (ap1 Fst (ap1 D_Fst x)))
   (mkSigma (ap1 Fst (ap1 Fst (ap1 D_Fst x)))
    (ruleInst zero x shape_D_F1_Fst_var0))

------------------------------------------------------------------------
-- Per-x adapter for D_Snd.

shape_D_Snd : (x : Term) ->
  Sigma Term (\ y' -> Sigma Term (\ x' ->
    Deriv (atomic (eqn (ap1 Fst (ap1 D_Snd x)) (ap2 Pair x' y')))))
shape_D_Snd x =
  mkSigma (ap1 Snd (ap1 Fst (ap1 D_Snd x)))
   (mkSigma (ap1 Fst (ap1 Fst (ap1 D_Snd x)))
    (ruleInst zero x shape_D_F1_Snd_var0))

------------------------------------------------------------------------
-- Per-(x, v) adapter for D_IfLf.

shape_D_IfLf : (x v : Term) ->
  Sigma Term (\ y' -> Sigma Term (\ x' ->
    Deriv (atomic (eqn (ap1 Fst (ap2 D_IfLf x v)) (ap2 Pair x' y')))))
shape_D_IfLf x v =
  mkSigma (ap1 Snd (ap1 Fst (ap2 D_IfLf x v)))
   (mkSigma (ap1 Fst (ap1 Fst (ap2 D_IfLf x v)))
    (ruleInst (suc zero) v
      (ruleInst zero x shape_D_F2_IfLf_var01)))

------------------------------------------------------------------------
-- Per-(x, v) adapter for Construction.D_TreeEq (instantiated with
-- Th12TreeEqNNFun's specific D_TreeEq_NN_fun).

shape_D_TreeEq : (x v : Term) ->
  Sigma Term (\ y' -> Sigma Term (\ x' ->
    Deriv (atomic (eqn (ap1 Fst (ap2 D_TreeEq x v)) (ap2 Pair x' y')))))
shape_D_TreeEq x v =
  mkSigma (ap1 Snd (ap1 Fst (ap2 D_TreeEq x v)))
   (mkSigma (ap1 Fst (ap1 Fst (ap2 D_TreeEq x v)))
    (ruleInst (suc zero) v
      (ruleInst zero x shape_D_F2_TreeEq_var01)))
