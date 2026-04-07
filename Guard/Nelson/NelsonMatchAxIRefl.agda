{-# OPTIONS --safe --without-K --exact-split #-}

-- NelsonMatchAxIRefl.agda
-- Demonstrates the "each specific proof" strategy for a non-trivial case:
-- Trans(axI(code(O)), axRefl(code(O))).
--
-- sp1 = enc_axI(codeOT)  = Pair(tag0T, Pair(codeOT, O))
-- sp2 = enc_axRefl(codeOT) = Pair(tag17T, Pair(codeOT, O))
--
-- Nelson sub-proofs:
--   thFunTFor(sp1) = Pair(codeIOT, codeOT)   [nelsonAxI]
--   thFunTFor(sp2) = Pair(codeOT, codeOT)     [nelsonAxReflGen]
--
-- Match: Snd(thFunTFor(sp1)) = codeOT = Fst(thFunTFor(sp2))
--
-- STRUCTURAL FINDING:
-- Tag-0 (axI) encodings have reify(natCode 0) = O, making
-- sp1 = Pair(O, data) which is NOT Pair-Pair-tagged. This means
-- nelsonRuleTransFull (which requires Pair-Pair-tagged sub-proofs
-- for the inner passthrough) cannot compose with tag-0 directly.
-- Tags >= 1 are Pair-Pair-tagged (natCode(suc n) = nd(lf, natCode n)).
--
-- For the specific proof, we verify semantic soundness of each
-- sub-proof directly, using the Nelson proofs and evalCode.

module Guard.Nelson.NelsonMatchAxIRefl where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.ThFunTForDefs
open import Guard.ThFunTFor
open import Guard.Nelson.EvalCode
open import Guard.Nelson.NelsonDispatch
open import Guard.Nelson.NelsonAxI using (nelsonAxI)
open import Guard.Nelson.NelsonAxReflGen using (nelsonAxReflGen)
open import Guard.Nelson.EvalCodeCorrect using (evalCodeO ; evalCodeIO)

private
  tag0T  : Term ; tag0T  = reify (natCode n0)
  tag17T : Term ; tag17T = reify (natCode n17)
  codeOT : Term ; codeOT = ap2 Pair O O
  codeIF : Term ; codeIF = reify (codeF1 I)
  codeIOT : Term ; codeIOT = ap2 Pair tagAp1T (ap2 Pair codeIF codeOT)

  sp1 : Term ; sp1 = ap2 Pair tag0T (ap2 Pair codeOT O)
  sp2 : Term ; sp2 = ap2 Pair tag17T (ap2 Pair codeOT O)

------------------------------------------------------------------------
-- Step 1: Matching condition (provable for this specific proof)
--
-- Snd(thFunTFor(sp1)) = codeOT = Fst(thFunTFor(sp2))

matchAxIRefl : {hyp : Equation} ->
  Deriv hyp (eqn (ap1 Snd (ap1 thFunTFor sp1))
                  (ap1 Fst (ap1 thFunTFor sp2)))
matchAxIRefl =
  let sndSp1 = ruleTrans (cong1 Snd (nelsonAxI codeOT))
                          (axSnd codeIOT codeOT)
      fstSp2 = ruleTrans (cong1 Fst (nelsonAxReflGen codeOT))
                          (axFst codeOT codeOT)
  in ruleTrans sndSp1 (ruleSym fstSp2)

------------------------------------------------------------------------
-- Step 2: Semantic soundness of each sub-proof (ground verification)
--
-- For sp1 (axI at codeOT):
--   evalCode(Fst(thFunTFor(sp1))) = evalCode(codeIOT) = O
--   evalCode(Snd(thFunTFor(sp1))) = evalCode(codeOT) = O

semTrueSp1 : {hyp : Equation} ->
  Deriv hyp (eqn (ap1 evalCode (ap1 Fst (ap1 thFunTFor sp1)))
                 (ap1 evalCode (ap1 Snd (ap1 thFunTFor sp1))))
semTrueSp1 =
  let fstR = ruleTrans (cong1 Fst (nelsonAxI codeOT)) (axFst codeIOT codeOT)
      sndR = ruleTrans (cong1 Snd (nelsonAxI codeOT)) (axSnd codeIOT codeOT)
  in ruleTrans (cong1 evalCode fstR)
     (ruleTrans evalCodeIO
     (ruleTrans (ruleSym evalCodeO)
                (ruleSym (cong1 evalCode sndR))))

-- For sp2 (axRefl at codeOT):
--   evalCode(Fst(thFunTFor(sp2))) = evalCode(codeOT) = O
--   evalCode(Snd(thFunTFor(sp2))) = evalCode(codeOT) = O

semTrueSp2 : {hyp : Equation} ->
  Deriv hyp (eqn (ap1 evalCode (ap1 Fst (ap1 thFunTFor sp2)))
                 (ap1 evalCode (ap1 Snd (ap1 thFunTFor sp2))))
semTrueSp2 =
  let fstR = ruleTrans (cong1 Fst (nelsonAxReflGen codeOT)) (axFst codeOT codeOT)
      sndR = ruleTrans (cong1 Snd (nelsonAxReflGen codeOT)) (axSnd codeOT codeOT)
  in ruleTrans (cong1 evalCode fstR)
               (ruleSym (cong1 evalCode sndR))

------------------------------------------------------------------------
-- Step 3: Semantic chain via matching + IH
--
-- The full chain for Trans(sp1, sp2):
-- evalCode(Fst(thFunTFor(sp1))) = O   [via semTrueSp1 + evalCodeIO]
-- evalCode(Snd(thFunTFor(sp1))) = O   [via evalCodeO]
-- bridge: Snd(thFunTFor(sp1)) = Fst(thFunTFor(sp2))  [matchAxIRefl]
-- evalCode(Fst(thFunTFor(sp2))) = O
-- evalCode(Snd(thFunTFor(sp2))) = O   [via semTrueSp2]
--
-- Combined: all four evalCode results are O.
-- This IS the semantic soundness of the Trans proof — we just
-- can't state it in terms of thFunTFor(enc) because tag-0 blocks
-- the inner passthrough.

allEvalO : {hyp : Equation} ->
  Deriv hyp (eqn (ap2 TreeEq (ap1 evalCode (ap1 Fst (ap1 thFunTFor sp1)))
                              (ap1 evalCode (ap1 Snd (ap1 thFunTFor sp2))))
                 O)
allEvalO =
  let fstSp1 = ruleTrans (cong1 Fst (nelsonAxI codeOT)) (axFst codeIOT codeOT)
      sndSp2 = ruleTrans (cong1 Snd (nelsonAxReflGen codeOT)) (axSnd codeOT codeOT)
  in ruleTrans (congL TreeEq (ap1 evalCode (ap1 Snd (ap1 thFunTFor sp2)))
                 (ruleTrans (cong1 evalCode fstSp1) evalCodeIO))
     (ruleTrans (congR TreeEq O (ruleTrans (cong1 evalCode sndSp2) evalCodeO))
                axTreeEqLL)
