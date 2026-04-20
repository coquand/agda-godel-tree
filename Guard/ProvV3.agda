{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.ProvV3: V3 provability modality.
--
-- Prov3 H eq        -- eq is internally provable from H via thmT (reify (codeEqn H))
-- necessitation     -- ProofE3 H eq  ==>  Prov3 H eq
-- diagContradict    -- Cantor-diagonal collapse
-- trueT / falseT / codeBotT  -- internal truth values + the ⊥ code
--
-- This is the V3 analog of Guard.archive.v2.Prov .  Unlike V2's Prov
-- (which stays hypothesis-free because  thFunTFor  is hCode-agnostic),
-- Prov3 explicitly records the hypothesis  H  whose code is embedded
-- in  thmT .

module Guard.ProvV3 where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.ThFun using (codeEqn)
open import Guard.ThFunTForV3 using (thmT)
open import Guard.TreeEqSelf using (treeEqSelf)
open import Guard.Thm14EV3 using (ProofE3 ; encT ; corr)

------------------------------------------------------------------------
-- Tree-level truth values and the ⊥ code.

trueT : Term
trueT = O

falseT : Term
falseT = ap2 Pair O O

codeBot : Tree
codeBot = codeEqn (eqn trueT falseT)

codeBotT : Term
codeBotT = reify codeBot

------------------------------------------------------------------------
-- Prov3 H eq: internal provability of  eq  under hypothesis-code  H .
--
-- The witness  enc  is a specific Term satisfying
--   ap1 (thmT (reify (codeEqn H))) enc = reify (codeEqn eq)
-- under any ambient Deriv hypothesis — the V3 analog of Hilbert-Bernays
-- derivability condition DC1.

record Prov3 (H eq : Equation) : Set where
  constructor mkProv3
  field
    enc  : Term
    corr : {hyp : Equation} ->
           Deriv hyp (eqn (ap1 (thmT (reify (codeEqn H))) enc)
                          (reify (codeEqn eq)))
open Prov3 public

------------------------------------------------------------------------
-- Necessitation (DC1):  ProofE3 H eq  ==>  Prov3 H eq .

necessitation : {H eq : Equation} -> ProofE3 H eq -> Prov3 H eq
necessitation pe = mkProv3 (encT pe) (corr pe)

------------------------------------------------------------------------
-- Internal Cantor diagonal.
--
-- If  TreeEq(c, c) = falseT  is derivable, then so is  trueT = falseT .

diagContradict : {hyp : Equation} (c : Term) ->
  Deriv hyp (eqn (ap2 TreeEq c c) falseT) ->
  Deriv hyp (eqn trueT falseT)
diagContradict c d = ruleTrans (ruleSym (treeEqSelf c)) d
