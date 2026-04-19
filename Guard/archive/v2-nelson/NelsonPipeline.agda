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

module Guard.Nelson.NelsonPipeline where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.ThFunTForDefs
open import Guard.ThFunTFor
open import Guard.Nelson.EvalCode
open import Guard.Nelson.NelsonDispatch
open import Guard.Nelson.NelsonAxRefl using (nelsonAxRefl)
open import Guard.Nelson.NelsonRuleTransFull using (nelsonRuleTransFull)
open import Guard.Nelson.NelsonRuleSym using (nelsonRuleSym)
open import Guard.Nelson.NelsonAxI using (nelsonAxI)
open import Guard.Nelson.NelsonAxReflGen using (nelsonAxReflGen)
open import Guard.Nelson.WellChained
open import Guard.Nelson.EvalCodeMkAp1 using (evalCodeMkAp1)
open import Guard.Nelson.EvalCodeCorrect using (evalCodeO ; evalCodeIO)
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

------------------------------------------------------------------------
-- Step 6: Cong1 pipeline — Cong1(tagVarT, Refl(x))
--
-- Uses tagVarT = Pair(Pair(Pair(O,O),O),O) as a dummy functor code.
-- This demonstrates that evalCode strips arbitrary functors:
-- evalCode(mkAp1(tagVarT, L)) = evalCode(L) for any L.
--
-- fCode = tagVarT = Pair(Pair(Pair(O,O),O),O)
-- Pair-Pair decomposition: f1=Pair(O,O), f2=O, f3=O

private
  tag20T : Term ; tag20T = reify (natCode n20)
  ppOO : Term ; ppOO = ap2 Pair O O

  -- TreeEq(tagVarT, O) = Pair(O,O)
  tagVarMissO : {hyp : Equation} ->
    Deriv hyp (eqn (ap2 TreeEq tagVarT O) ppOO)
  tagVarMissO = axTreeEqNL (ap2 Pair ppOO O) O

  -- TreeEq(tagVarT, tagAp1T) = Pair(O,O)
  -- tagAp1T = Pair(O, Pair(O,O))
  -- tagVarT = Pair(Pair(Pair(O,O),O),O)
  -- TreeEq(Pair(Pair(Pair(O,O),O),O), Pair(O, Pair(O,O)))
  --   = IfLf(TreeEq(Pair(Pair(O,O),O), O), Pair(TreeEq(O, Pair(O,O)), Pair(O,O)))
  --   = IfLf(Pair(O,O), ...) = Pair(O,O)
  tagAp1T' : Term ; tagAp1T' = reify tagAp1
  tagVarMissAp1 : {hyp : Equation} ->
    Deriv hyp (eqn (ap2 TreeEq tagVarT tagAp1T') ppOO)
  tagVarMissAp1 =
    ruleTrans (axTreeEqNN (ap2 Pair ppOO O) O O (ap2 Pair O O))
    (ruleTrans (congL IfLf (ap2 Pair (ap2 TreeEq O (ap2 Pair O O)) ppOO)
                 (axTreeEqNL ppOO O))
               (axIfLfN O O (ap2 TreeEq O (ap2 Pair O O)) ppOO))

wcCong1Refl : {hyp : Equation} ->
  WC (ap2 Pair tag20T (ap2 Pair tagVarT encRefl)) hyp
wcCong1Refl =
  wcCong1 ppOO O O tag17T (ap2 Pair v0 O) wcRefl tagVarMissO tagVarMissAp1

semSoundCong1Refl : {hyp : Equation} ->
  let enc = ap2 Pair tag20T (ap2 Pair tagVarT encRefl)
  in Deriv hyp (eqn (ap1 evalCode (ap1 Fst (ap1 thFunTFor enc)))
                     (ap1 evalCode (ap1 Snd (ap1 thFunTFor enc))))
semSoundCong1Refl = semSound _ wcCong1Refl

------------------------------------------------------------------------
-- Step 7: Trans(axI(codeOT), axRefl(codeOT)) via WC
--
-- Uses wcAxI + wcTransO to compose an axI sub-proof (O-tagged)
-- with an axRefl sub-proof (PairPair-tagged) via Trans.
--
-- encAxI = Pair(O, Pair(codeOT, O))
--   O-Pair decomposition: Pair(O, Pair(Pair(O,O), O))
--   e1=O, e2=O, e3=O
--
-- encAxRefl = Pair(tag17T, Pair(codeOT, O))
--   PairPair decomposition: a1=O, a2=rn16, d1=Pair(codeOT, O)

private
  tag0T : Term ; tag0T = reify (natCode n0)
  codeOT : Term ; codeOT = ap2 Pair O O
  codeIF : Term ; codeIF = reify (codeF1 I)

  encAxI : Term
  encAxI = ap2 Pair tag0T (ap2 Pair codeOT O)

  encAxReflC : Term
  encAxReflC = ap2 Pair tag17T (ap2 Pair codeOT O)

  -- wcAxI for codeOT: need evalCode(mkAp1(codeIF, codeOT)) = evalCode(codeOT)
  -- evalCode(mkAp1(codeIF, codeOT)) = evalCode(codeIOT) = O  [evalCodeIO]
  -- evalCode(codeOT) = O  [evalCodeO]
  ecAxISide : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 evalCode (ap2 Pair tagAp1T' (ap2 Pair codeIF codeOT)))
                   (ap1 evalCode codeOT))
  ecAxISide = ruleTrans evalCodeIO (ruleSym evalCodeO)

wcAxICO : {hyp : Equation} -> WC encAxI hyp
wcAxICO = wcAxI codeOT ecAxISide

-- axRefl(codeOT): need WC for Pair(tag17T, Pair(codeOT, O))
-- But wcRefl uses v0 = var zero, not codeOT.
-- We need a generalized wcRefl or a new constructor.
-- For now, use the generalized Nelson proof directly.
-- Actually, we need WC(encAxReflC). Let me add wcReflGen.

-- Matching condition: Snd(thFunTFor(encAxI)) = Fst(thFunTFor(encAxReflC))
-- nelsonAxI(codeOT): thFunTFor(encAxI) = Pair(mkAp1(codeIF, codeOT), codeOT)
-- nelsonAxReflGen(codeOT): thFunTFor(encAxReflC) = Pair(codeOT, codeOT)
-- Snd = codeOT = Fst
matchAxIReflC : {hyp : Equation} ->
  Deriv hyp (eqn (ap1 Snd (ap1 thFunTFor encAxI))
                  (ap1 Fst (ap1 thFunTFor encAxReflC)))
matchAxIReflC =
  let mkApTerm = ap2 Pair tagAp1T' (ap2 Pair codeIF codeOT)
      sndSp1 = ruleTrans (cong1 Snd (nelsonAxI codeOT)) (axSnd mkApTerm codeOT)
      fstSp2 = ruleTrans (cong1 Fst (nelsonAxReflGen codeOT)) (axFst codeOT codeOT)
  in ruleTrans sndSp1 (ruleSym fstSp2)

-- Build the WC witness using wcTransO
-- encAxI = Pair(O, Pair(Pair(O,O), O)) — O-Pair with e1=O, e2=O, e3=O
-- encAxReflC = Pair(Pair(O, rn16), Pair(codeOT, O)) — PairPair with c1=O, c2=rn16, d1=Pair(codeOT, O)
wcTransAxIRefl : {hyp : Equation} ->
  WC (ap2 Pair tag19T (ap2 Pair encAxI encAxReflC)) hyp
wcTransAxIRefl =
  wcTransO O O O O rn16 (ap2 Pair codeOT O)
    wcAxICO
    (wcReflGen codeOT)
    matchAxIReflC

semSoundTransAxIRefl : {hyp : Equation} ->
  let enc = ap2 Pair tag19T (ap2 Pair encAxI encAxReflC)
  in Deriv hyp (eqn (ap1 evalCode (ap1 Fst (ap1 thFunTFor enc)))
                     (ap1 evalCode (ap1 Snd (ap1 thFunTFor enc))))
semSoundTransAxIRefl = semSound _ wcTransAxIRefl
