{-# OPTIONS --safe --without-K --exact-split #-}

-- EvalCodeCorrect.agda
-- Proves the EqTrue predicate works for axI at ground term O.
--
-- evalCode(code(O)) = O
-- evalCode(code(I(O))) = O
-- Combined: TreeEq(evalCode(L), evalCode(R)) = O for the axI output.
--
-- This is the corrected Experiment E for ground terms.

module Guard.Nelson.EvalCodeCorrect where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.ThFunTForDefs
open import Guard.ThFunTFor
open import Guard.Nelson.EvalCode
open import Guard.Nelson.NelsonDispatch
open import Guard.Nelson.NelsonAxI
open import Guard.Nelson.NelsonExtractors
open import Guard.ThFunTForCorrectDefs

private
  poo : Term ; poo = ap2 Pair O O

  -- code(O) as a Term: reify(nd(lf, lf)) = Pair(O, O)
  codeOT : Term ; codeOT = ap2 Pair O O

  -- code(I(O)) as a Term
  codeIT : Term ; codeIT = reify (codeF1 I)
  codeIOT : Term ; codeIOT = ap2 Pair tagAp1T (ap2 Pair codeIT codeOT)

  tag0T : Term ; tag0T = reify (natCode n0)

  -- Fst component of codeIT
  -- codeF1 I = nd(natCode 26, lf)
  -- reify = Pair(reify(natCode 26), O)
  -- So Fst(codeIT) = reify(natCode 26)
  codeITfst : Term ; codeITfst = reify (natCode n25)
  -- Wait: natCode 26 = suc n25, natCode (suc n25) = nd lf (natCode n25)
  -- reify(nd lf (natCode n25)) = Pair(O, reify(natCode n25))
  -- So reify(natCode 26) = Pair(O, reify(natCode n25))
  -- And Fst(codeIT) = Pair(O, reify(natCode n25)) which is a Pair

  -- Actually let me just compute reify(natCode 26) directly
  n26 : Nat ; n26 = suc n25
  rn26 : Term ; rn26 = reify (natCode n26)

  ------------------------------------------------------------------------
  -- Helper: evalStep dispatch on specific (tag, data, recs)

  -- isTagO reduction
  isTagORed : (tag data' recs : Term) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap2 isTagO (ap2 Pair tag data') recs)
                   (ap2 TreeEq tag O))
  isTagORed tag data' recs =
    ruleTrans (fanRed (Lift Fst) (kF2 O) TreeEq (ap2 Pair tag data') recs)
    (ruleTrans (congL TreeEq (ap2 (kF2 O) (ap2 Pair tag data') recs)
                 (ruleTrans (liftRed Fst (ap2 Pair tag data') recs)
                            (axFst tag data')))
               (congR TreeEq tag (constF2Red O (ap2 Pair tag data') recs)))

  -- isTagAp1 reduction
  isTagAp1Red : (tag data' recs : Term) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap2 isTagAp1 (ap2 Pair tag data') recs)
                   (ap2 TreeEq tag tagAp1T))
  isTagAp1Red tag data' recs =
    ruleTrans (fanRed (Lift Fst) (kF2 tagAp1T) TreeEq (ap2 Pair tag data') recs)
    (ruleTrans (congL TreeEq (ap2 (kF2 tagAp1T) (ap2 Pair tag data') recs)
                 (ruleTrans (liftRed Fst (ap2 Pair tag data') recs)
                            (axFst tag data')))
               (congR TreeEq tag (constF2Red tagAp1T (ap2 Pair tag data') recs)))

  -- tagAp1T self-equality: TreeEq(tagAp1T, tagAp1T) = O
  -- tagAp1T = Pair(O, Pair(O, O))
  tagAp1Self : {hyp : Equation} -> Deriv hyp (eqn (ap2 TreeEq tagAp1T tagAp1T) O)
  tagAp1Self =
    ruleTrans (axTreeEqNN O (ap2 Pair O O) O (ap2 Pair O O))
    (ruleTrans (congL IfLf (ap2 Pair (ap2 TreeEq (ap2 Pair O O) (ap2 Pair O O)) poo) axTreeEqLL)
    (ruleTrans (axIfLfL (ap2 TreeEq (ap2 Pair O O) (ap2 Pair O O)) poo)
    (ruleTrans (axTreeEqNN O O O O)
    (ruleTrans (congL IfLf (ap2 Pair (ap2 TreeEq O O) poo) axTreeEqLL)
    (ruleTrans (axIfLfL (ap2 TreeEq O O) poo) axTreeEqLL)))))

  -- tagAp1Case reduction: tagAp1Case(orig, recs) = Snd(Snd(recs))
  tagAp1CaseRed : (orig recs : Term) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap2 tagAp1Case orig recs) (ap1 Snd (ap1 Snd recs)))
  tagAp1CaseRed orig recs =
    ruleTrans (axPost Snd (Post Snd sndArg2) orig recs)
    (cong1 Snd (ruleTrans (axPost Snd sndArg2 orig recs)
                          (cong1 Snd (sndArg2Red orig recs))))

  -- TreeEq(codeIT, tagAp1T) = Pair(O,O)
  -- codeIT = Pair(rn26, O), tagAp1T = Pair(O, Pair(O,O))
  -- = IfLf(TreeEq(rn26, O), Pair(TreeEq(O, Pair(O,O)), Pair(O,O)))
  -- rn26 = Pair(O, reify(natCode n25)), so TreeEq(rn26, O) = Pair(O,O) by axTreeEqNL
  -- IfLf(Pair(O,O), Pair(X, Y)) = Y = Pair(O,O) by axIfLfN
  codeITneqAp1 : {hyp : Equation} -> Deriv hyp (eqn (ap2 TreeEq codeIT tagAp1T) poo)
  codeITneqAp1 =
    ruleTrans (axTreeEqNN rn26 O O (ap2 Pair O O))
    (ruleTrans (congL IfLf (ap2 Pair (ap2 TreeEq O (ap2 Pair O O)) poo)
                 (axTreeEqNL O (reify (natCode n25))))
               (axIfLfN O O (ap2 TreeEq O (ap2 Pair O O)) poo))

------------------------------------------------------------------------
-- Lemma 1: evalCode(codeOT) = O
-- codeOT = Pair(O, O). Fst = O = tagO. Hit tagO case, return O.

evalCodeO : {hyp : Equation} ->
  Deriv hyp (eqn (ap1 evalCode codeOT) O)
evalCodeO =
  let recs = ap2 Pair (ap1 evalCode O) (ap1 evalCode O)
      -- RecNd: evalCode(Pair(O,O)) = evalStep(Pair(O,O), Pair(evalCode(O), evalCode(O)))
      step1 = axRecNd O evalStep O O
      -- evalCode(O) = O (base case)
      baseO = axRecLf O evalStep
      -- recs = Pair(O, O)
      recsRed = ruleTrans (congL Pair (ap1 evalCode O) baseO) (congR Pair O baseO)
      -- evalStep(Pair(O,O), Pair(O,O)):
      -- isTagO: TreeEq(O, O) = O → hit → tagOCase → O
      tagOHit = branchHit isTagO tagOCase (branch isTagAp1 tagAp1Case sndArg2)
                  codeOT poo
                  (ruleTrans (isTagORed O O poo) axTreeEqLL)
      caseO = constF2Red O codeOT poo
      step2 = ruleTrans (congR evalStep codeOT recsRed)
                         (ruleTrans tagOHit caseO)
  in ruleTrans step1 step2

------------------------------------------------------------------------
-- Lemma 2: evalCode(Pair(codeIT, codeOT)) passthrough
-- codeIT tag is neither tagO nor tagAp1, so falls through to sndArg2.
-- Result: Pair(evalCode(codeIT), evalCode(codeOT))

evalCodeInner : {hyp : Equation} ->
  Deriv hyp (eqn (ap1 evalCode (ap2 Pair codeIT codeOT))
                 (ap2 Pair (ap1 evalCode codeIT) (ap1 evalCode codeOT)))
evalCodeInner =
  let orig = ap2 Pair codeIT codeOT
      recs = ap2 Pair (ap1 evalCode codeIT) (ap1 evalCode codeOT)
      -- RecNd
      step1 = axRecNd O evalStep codeIT codeOT
      -- isTagO miss: codeIT = Pair(rn26, O) is a Pair
      missO = branchMiss isTagO tagOCase (branch isTagAp1 tagAp1Case sndArg2)
                orig recs
                (ruleTrans (isTagORed codeIT codeOT recs)
                           (axTreeEqNL rn26 O))
      -- isTagAp1 miss: TreeEq(codeIT, tagAp1T) = Pair(O,O)
      missAp1 = branchMiss isTagAp1 tagAp1Case sndArg2
                  orig recs
                  (ruleTrans (isTagAp1Red codeIT codeOT recs) codeITneqAp1)
      -- sndArg2(orig, recs) = recs
      deflt = sndArg2Red orig recs
  in ruleTrans step1 (ruleTrans missO (ruleTrans missAp1 deflt))

------------------------------------------------------------------------
-- Lemma 3: evalCode(codeIOT) = O
-- codeIOT = Pair(tagAp1T, Pair(codeIT, codeOT))
-- tagO miss (tagAp1T is a Pair), tagAp1 hit, tagAp1Case gives Snd(Snd(recs)).
-- Snd(recs) = evalCode(Pair(codeIT, codeOT)) = Pair(evalCode(codeIT), evalCode(codeOT))
-- Snd(Snd(recs)) = evalCode(codeOT) = O

evalCodeIO : {hyp : Equation} ->
  Deriv hyp (eqn (ap1 evalCode codeIOT) O)
evalCodeIO =
  let innerP = ap2 Pair codeIT codeOT
      origT = ap2 Pair tagAp1T innerP
      recsT = ap2 Pair (ap1 evalCode tagAp1T) (ap1 evalCode innerP)
      -- RecNd
      step1 = axRecNd O evalStep tagAp1T innerP
      -- isTagO miss: tagAp1T = Pair(O, Pair(O,O))
      missO = branchMiss isTagO tagOCase (branch isTagAp1 tagAp1Case sndArg2)
                origT recsT
                (ruleTrans (isTagORed tagAp1T innerP recsT)
                           (axTreeEqNL O (ap2 Pair O O)))
      -- isTagAp1 hit: TreeEq(tagAp1T, tagAp1T) = O
      hitAp1 = branchHit isTagAp1 tagAp1Case sndArg2
                 origT recsT
                 (ruleTrans (isTagAp1Red tagAp1T innerP recsT) tagAp1Self)
      -- tagAp1Case: Snd(Snd(recsT))
      caseRed = tagAp1CaseRed origT recsT
      -- step1 chain: evalCode(codeIOT) = Snd(Snd(recsT))
      toSndSnd = ruleTrans step1 (ruleTrans missO (ruleTrans hitAp1 caseRed))

      -- Snd(recsT) = evalCode(innerP)
      sndRecsT = axSnd (ap1 evalCode tagAp1T) (ap1 evalCode innerP)
      -- evalCode(innerP) = Pair(evalCode(codeIT), evalCode(codeOT)) [passthrough]
      innerPT = evalCodeInner
      -- Snd(evalCode(innerP)) = Snd(Pair(evalCode(codeIT), evalCode(codeOT)))
      --                       = evalCode(codeOT)
      sndInner = ruleTrans (cong1 Snd innerPT)
                           (axSnd (ap1 evalCode codeIT) (ap1 evalCode codeOT))
      -- Snd(Snd(recsT)) = Snd(evalCode(innerP)) = evalCode(codeOT) = O
      chain = ruleTrans (cong1 Snd sndRecsT) (ruleTrans sndInner evalCodeO)
  in ruleTrans toSndSnd chain

------------------------------------------------------------------------
-- Main theorem: EqTrue holds for axI at ground term O.
--
-- nelsonAxI(codeOT): thFunTFor(enc) = Pair(codeIOT, codeOT)
-- evalCode(codeIOT) = O  [Lemma 3]
-- evalCode(codeOT) = O   [Lemma 1]
-- TreeEq(O, O) = O        [axTreeEqLL]

eqTrueAxI : {hyp : Equation} ->
  let enc = ap2 Pair (reify (natCode n0)) (ap2 Pair codeOT O)
  in Deriv hyp (eqn (ap2 TreeEq (ap1 evalCode (ap1 Fst (ap1 thFunTFor enc)))
                                 (ap1 evalCode (ap1 Snd (ap1 thFunTFor enc))))
                    O)
eqTrueAxI =
  let enc = ap2 Pair (reify (natCode n0)) (ap2 Pair codeOT O)
      -- nelsonAxI codeOT : thFunTFor(enc) = Pair(codeIOT', codeOT)
      -- where codeIOT' = Pair(tagAp1T, Pair(codeIF, codeOT))
      -- Note: codeIF = reify(codeF1 I) = codeIT ✓
      result = nelsonAxI codeOT
      -- Fst(thFunTFor(enc)) = codeIOT
      fstR = ruleTrans (cong1 Fst result)
                       (axFst (ap2 Pair (reify tagAp1) (ap2 Pair codeIT codeOT)) codeOT)
      -- Snd(thFunTFor(enc)) = codeOT
      sndR = ruleTrans (cong1 Snd result)
                       (axSnd (ap2 Pair (reify tagAp1) (ap2 Pair codeIT codeOT)) codeOT)
      -- evalCode(Fst(thFunTFor(enc))) = evalCode(codeIOT) = O
      evalL = ruleTrans (cong1 evalCode fstR) evalCodeIO
      -- evalCode(Snd(thFunTFor(enc))) = evalCode(codeOT) = O
      evalR = ruleTrans (cong1 evalCode sndR) evalCodeO
      -- TreeEq(evalCode(L), evalCode(R)) = TreeEq(O, O) = O
  in ruleTrans (congL TreeEq (ap1 evalCode (ap1 Snd (ap1 thFunTFor enc))) evalL)
     (ruleTrans (congR TreeEq O evalR)
                axTreeEqLL)
