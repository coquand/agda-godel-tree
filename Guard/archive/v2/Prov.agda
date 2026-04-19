{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.Prov: a provability-modality layer on top of Thm14E.
--
-- Conceptual frame inspired by Dijk & Gietelink-Oldenziel,
-- "Goedel's Incompleteness after Joyal" (arXiv 2004.10482):
--
--   Prov eq       -- internal provability of eq: "[] eq"
--   necessitation -- H |- eq  ==>  [] eq (given an encoding of H)
--   diagContradict -- the shared Cantor-diagonal tail of Goedel I/II
--
-- Existing files (GodelII.agda, GodelIIFull.agda, Thm14E.agda) are
-- unchanged; this module is an additional, modal-style wrapper.

module Guard.Prov where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.ThFun using (codeEqn)
open import Guard.ThFunTFor using (thFunTFor)
open import Guard.Thm14E using (ProofE ; thm14E)
open import Guard.ProofEAny using (mkProofEAny)
open import Guard.GodelII using (treeEqSelf)

------------------------------------------------------------------------
-- Tree-level truth values (shared with GodelIIFull).

trueT : Term
trueT = O

falseT : Term
falseT = ap2 Pair O O

------------------------------------------------------------------------
-- Prov eq: "eq is internally provable".
--
-- The encoding witness t satisfies
--     thFunTFor(t) = reify(codeEqn eq)
-- in every hypothesis context; this is Rose's Theorem 14 result,
-- equivalently the Hilbert-Bernays derivability condition DC1.

record Prov (eq : Equation) : Set where
  constructor mkProv
  field
    enc  : Term
    corr : {hyp : Equation} ->
           Deriv hyp (eqn (ap1 thFunTFor enc) (reify (codeEqn eq)))
open Prov public

------------------------------------------------------------------------
-- Necessitation (DC1):  H |- eq  ==>  Prov eq.
--
-- The premise ProofE H supplies an encoding of the hypothesis H;
-- this is how thm14E propagates ruleHyp through the derivation.

necessitation : {H eq : Equation} -> ProofE H -> Deriv H eq -> Prov eq
necessitation ph d =
  let pe = thm14E d ph
  in mkProv (ap2 Pair (reify (fst pe)) (reify (fst (snd pe))))
            (fst (snd (snd (snd pe))))

-- Convenience form for an arbitrary equational hypothesis eqn A B.
necessitateAny : (A B : Term) {eq : Equation} ->
                 Deriv (eqn A B) eq -> Prov eq
necessitateAny A B d = necessitation (mkProofEAny A B) d

------------------------------------------------------------------------
-- Internal Cantor diagonal.
--
-- If TreeEq(c, c) = falseT is derivable, then so is trueT = falseT.
-- This is the common tail of Goedel I and Goedel II: the Goedel
-- sentence / Con sentence is instantiated so that its LHS becomes
-- TreeEq(c, c), and then reflexivity of TreeEq collapses it to trueT.

diagContradict : {hyp : Equation} (c : Term) ->
  Deriv hyp (eqn (ap2 TreeEq c c) falseT) ->
  Deriv hyp (eqn trueT falseT)
diagContradict c d = ruleTrans (ruleSym (treeEqSelf c)) d
