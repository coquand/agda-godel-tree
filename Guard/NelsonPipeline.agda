{-# OPTIONS --safe --without-K --exact-split #-}

-- NelsonPipeline.agda
-- The full Nelson pipeline: from a specific Deriv proof, through
-- encoding, through WC, to semantic soundness — all inside Deriv.
--
-- Demonstrates Nelson's "for each specific proof" strategy:
-- we do NOT prove WC universally, but show that for the specific
-- proof Trans(Refl(x), Refl(x)), the matching condition is
-- automatically satisfied and semantic soundness follows.
--
-- Pipeline:
--   1. axRefl(x) encodes as Pair(tag17T, Pair(x, O))
--   2. nelsonAxRefl: thFunTFor(enc) = Pair(x, x)
--   3. Matching: Snd(Pair(x,x)) = x = Fst(Pair(x,x))
--   4. wcTrans applies with this match
--   5. semSound gives semantic truth
--
-- This is the Agda formalization of: for this specific proof,
-- the system internally verifies its own semantic soundness.

module Guard.NelsonPipeline where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.ThFunTForDefs
open import Guard.ThFunTFor
open import Guard.EvalCode
open import Guard.NelsonDispatch
open import Guard.NelsonAxRefl using (nelsonAxRefl)
open import Guard.NelsonRuleTransFull using (nelsonRuleTransFull)
open import Guard.NelsonRuleSym using (nelsonRuleSym)
open import Guard.WellChained
open import Guard.GodelII using (treeEqSelf)

private
  tag17T : Term ; tag17T = reify (natCode n17)
  tag18T : Term ; tag18T = reify (natCode n18)
  tag19T : Term ; tag19T = reify (natCode n19)
  tagVarT : Term ; tagVarT = ap2 Pair (ap2 Pair (ap2 Pair O O) O) O
  v0 : Term ; v0 = var zero

  -- The encoding of axRefl(v0)
  encRefl : Term
  encRefl = ap2 Pair tag17T (ap2 Pair v0 O)

  -- Pair-Pair decomposition of encRefl for use in wcTrans
  -- encRefl = Pair(tag17T, Pair(v0, O))
  -- tag17T = Pair(O, reify(natCode 16))
  -- So encRefl = Pair(Pair(O, reify(natCode 16)), Pair(v0, O))
  --            = Pair(Pair(a1, a2), b1)
  -- where a1 = O, a2 = reify(natCode 16), b1 = Pair(v0, O)
  rn16 : Term ; rn16 = reify (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))
  a1R : Term ; a1R = O
  a2R : Term ; a2R = rn16
  b1R : Term ; b1R = ap2 Pair v0 O

------------------------------------------------------------------------
-- Step 1: The matching condition for Trans(Refl(x), Refl(x))
--
-- nelsonAxRefl: thFunTFor(encRefl) = Pair(v0, v0)
-- Snd(thFunTFor(encRefl)) = Snd(Pair(v0, v0)) = v0
-- Fst(thFunTFor(encRefl)) = Fst(Pair(v0, v0)) = v0
-- Match: Snd(thFunTFor(sp1)) = Fst(thFunTFor(sp2))
-- Both are v0, so this is axRefl(v0).

matchReflRefl : {hyp : Equation} ->
  Deriv hyp (eqn (ap1 Snd (ap1 thFunTFor encRefl))
                  (ap1 Fst (ap1 thFunTFor encRefl)))
matchReflRefl =
  let nar = nelsonAxRefl
      -- Snd(thFunTFor(encRefl)) = Snd(Pair(v0, v0)) = v0
      sndR = ruleTrans (cong1 Snd nar) (axSnd v0 v0)
      -- Fst(thFunTFor(encRefl)) = Fst(Pair(v0, v0)) = v0
      fstR = ruleTrans (cong1 Fst nar) (axFst v0 v0)
      -- v0 = v0 by axRefl
  in ruleTrans sndR (ruleSym fstR)

------------------------------------------------------------------------
-- Step 2: Build the WC witness
--
-- wcTrans needs encRefl decomposed as Pair(Pair(a1,a2), b1).
-- encRefl = Pair(tag17T, Pair(v0, O))
--         = Pair(Pair(O, rn16), Pair(v0, O))
-- So a1=O, a2=rn16, b1=Pair(v0, O).
-- Both sub-proofs are wcRefl.

-- First, verify that encRefl = Pair(Pair(a1R, a2R), b1R)
-- tag17T = reify(natCode 17) = reify(nd(lf, natCode 16))
--        = Pair(O, reify(natCode 16)) = Pair(a1R, a2R)
-- So encRefl = Pair(Pair(a1R, a2R), b1R) definitionally. ✓

wcReflRefl : {hyp : Equation} ->
  WC (ap2 Pair tag19T (ap2 Pair encRefl encRefl)) hyp
wcReflRefl =
  wcTrans a1R a2R b1R a1R a2R b1R wcRefl wcRefl matchReflRefl

------------------------------------------------------------------------
-- Step 3: Semantic soundness via semSound

semSoundReflRefl : {hyp : Equation} ->
  let enc = ap2 Pair tag19T (ap2 Pair encRefl encRefl)
  in Deriv hyp (eqn (ap1 evalCode (ap1 Fst (ap1 thFunTFor enc)))
                     (ap1 evalCode (ap1 Snd (ap1 thFunTFor enc))))
semSoundReflRefl = semSound _ wcReflRefl

------------------------------------------------------------------------
-- Step 4: TreeEq corollary — the full statement
--
-- For the specific proof Trans(Refl(x), Refl(x)):
-- TreeEq(evalCode(Fst(thFunTFor(enc))), evalCode(Snd(thFunTFor(enc)))) = O

semSoundReflReflTreeEq : {hyp : Equation} ->
  let enc = ap2 Pair tag19T (ap2 Pair encRefl encRefl)
  in Deriv hyp (eqn (ap2 TreeEq (ap1 evalCode (ap1 Fst (ap1 thFunTFor enc)))
                                 (ap1 evalCode (ap1 Snd (ap1 thFunTFor enc))))
                    O)
semSoundReflReflTreeEq =
  let enc = ap2 Pair tag19T (ap2 Pair encRefl encRefl)
      eq = semSoundReflRefl
  in ruleTrans (congL TreeEq (ap1 evalCode (ap1 Snd (ap1 thFunTFor enc))) eq)
               (treeEqSelf (ap1 evalCode (ap1 Snd (ap1 thFunTFor enc))))

------------------------------------------------------------------------
-- Step 5: A more complex pipeline — Sym(Trans(Refl, Refl))
--
-- Shows the pipeline composes: build WC for a deeper proof tree,
-- then semSound handles it automatically.

wcSymTransRefl : {hyp : Equation} ->
  let encTR = ap2 Pair tag19T (ap2 Pair encRefl encRefl)
  in WC (ap2 Pair tag18T (ap2 Pair tagVarT encTR)) hyp
wcSymTransRefl =
  let -- encTR = Pair(tag19T, Pair(encRefl, encRefl))
      -- tag19T = Pair(O, reify(natCode 18))
      -- So encTR = Pair(Pair(O, reify(natCode 18)), Pair(encRefl, encRefl))
      -- Decomposition: Pair(Pair(a1, a2), b)
      -- where a1 = O, a2 = reify(natCode 18), b = Pair(encRefl, encRefl)
      -- For wcSym, we need WC(Pair(s1, s2)) where
      -- encTR = Pair(s1, s2)
      -- s1 = Pair(O, reify(natCode 18)) = tag19T? No...
      -- Actually encTR = ap2 Pair tag19T (ap2 Pair encRefl encRefl)
      -- s1 = tag19T, s2 = Pair(encRefl, encRefl)
      -- But wcSym needs WC(Pair(s1, s2)) = WC(encTR) = wcReflRefl ✓
      rn18 = reify (natCode n18)
  in wcSym (ap2 Pair a1R rn18)
           (ap2 Pair encRefl encRefl)
           wcReflRefl

semSoundSymTransRefl : {hyp : Equation} ->
  let encTR = ap2 Pair tag19T (ap2 Pair encRefl encRefl)
      enc = ap2 Pair tag18T (ap2 Pair tagVarT encTR)
  in Deriv hyp (eqn (ap1 evalCode (ap1 Fst (ap1 thFunTFor enc)))
                     (ap1 evalCode (ap1 Snd (ap1 thFunTFor enc))))
semSoundSymTransRefl = semSound _ wcSymTransRefl
