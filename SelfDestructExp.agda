{-# OPTIONS --without-K --exact-split #-}

module SelfDestructExp where

open import ChwistekSyntax
open import ChwistekProvability
open import ChwistekCodeLogic
open import ChwistekCodeQuant
open import ChwistekGodelSentence
open import ChwistekGodelProof
open import ChwistekSoundness
open import ChwistekGodel2Genuine
open import CExpPair
open import SelfDestruct

------------------------------------------------------------------------
-- sdExp: the self-destruct template as a CExpP
------------------------------------------------------------------------

-- Helper: Code constant as CExpP
k : Code -> CExpP
k = clitP

sdExp : CExpP -> CExpP
sdExp e =
  let
    encCCheckLitE = cpair (k (catom n18)) (cpair (k (catom n17)) e)
    step1E = cpair (k (catom n37g)) (cpair e e)
    step2E = cpair (k (catom n36g))
                   (cpair encCCheckLitE (k (encFormula GoedelSentence)))
    step3E = k (cnode (catom n36g)
                      (cnode encCSubPhi (encFormula GoedelSentence)))
    step4E = cpair (k (catom n39g)) step3E
    step5E = cpair (k (catom n38g)) (cpair step2E step4E)
  in cpair (k (catom n33)) (cpair step1E step5E)

------------------------------------------------------------------------
-- Fuel for sdExp evaluation
------------------------------------------------------------------------

-- Deepest cpair nesting path (through step2E/encCCheckLitE):
--   root(1) -> inner(2) -> step5E(3) -> inner(4) -> step2E(5) ->
--   inner(6) -> encCCheckLitE(7) -> inner(8) -> leaf
-- 8 cpair layers. clitP needs fuel >= 1. Total: 9.
-- For general e at fuel m: need m + 8.

nine : Nat
nine = suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))

------------------------------------------------------------------------
-- sdExp for closed codes (clitP p): proof by direct computation
------------------------------------------------------------------------

-- When e = clitP p, every leaf of sdExp (clitP p) is clitP of some
-- code. evalGP at fuel 9 evaluates through all 8 cpair layers,
-- replacing each cpair with cnode and each clitP c with c.
-- The result is just (sdCode p).

sdExp-clit-correct :
  (p : Code) ->
  Eq (evalGP nine (sdExp (clitP p))) (just (sdCode p))
sdExp-clit-correct p = refl

-- TODO: test whether refl works. If not, build the proof using
-- evalGP-cpair for each layer. The proof is finite (8 applications
-- of evalGP-cpair + reflexivity for clitP leaves).
