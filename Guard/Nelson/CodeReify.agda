{-# OPTIONS --safe --without-K --exact-split #-}

module Guard.Nelson.CodeReify where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce

------------------------------------------------------------------------
-- codeReify : Fun1
--
-- Computes code(reify(t)) from a tree t presented as reify(t).
-- Satisfies: ap1 codeReify (reify t) = reify (code (reify t))
--
-- Base: codeReify(O) = reify(code O) = reify(nd lf lf) = Pair(O, O)
-- Step: codeReify(Pair(a, b)) = reify(code(ap2 Pair (reify a') (reify b')))
--   where a' and b' are the subtrees.
--   code(ap2 Pair X Y) = nd tagAp2 (nd (codeF2 Pair) (nd (code X) (code Y)))
--   At the object level, code X = codeReify(a) and code Y = codeReify(b)
--   (by recursion).
--   So: = reify(nd tagAp2 (nd (codeF2 Pair) (nd (codeReify a) (codeReify b))))
--       = Pair(reify tagAp2, Pair(reify(codeF2 Pair), Pair(codeReify a, codeReify b)))
--       = Pair(tagAp2R, Pair(pairCFR, recs))
--
-- The step function only uses recs (= Pair(codeReify a, codeReify b))
-- and constants. No orig, no free variables.

private
  tagAp2R : Term
  tagAp2R = reify tagAp2

  pairCFR : Term
  pairCFR = reify (codeF2 Pair)

  poo : Term
  poo = ap2 Pair O O

-- Step function: (orig, recs) -> Pair(tagAp2R, Pair(pairCFR, recs))
-- Uses only recs and constants.

codeReifyStep : Fun2
codeReifyStep = Fan (Lift (KT tagAp2R)) (Fan (Lift (KT pairCFR)) (Post Snd Pair) Pair) Pair

-- codeReify : Fun1
codeReify : Fun1
codeReify = Rec poo codeReifyStep

------------------------------------------------------------------------
-- Reduction lemmas

-- Base case: codeReify(O) = Pair(O, O) = reify(code O)
codeReifyBase : {hyp : Equation} ->
  Deriv hyp (eqn (ap1 codeReify O) poo)
codeReifyBase = axRecLf poo codeReifyStep

-- Step case: codeReify(Pair(a, b)) = Pair(tagAp2R, Pair(pairCFR, Pair(codeReify a, codeReify b)))
codeReifyStep' : (a b : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap1 codeReify (ap2 Pair a b))
                 (ap2 Pair tagAp2R (ap2 Pair pairCFR (ap2 Pair (ap1 codeReify a) (ap1 codeReify b)))))
codeReifyStep' a b =
  let orig : Term ; orig = ap2 Pair a b
      recs : Term ; recs = ap2 Pair (ap1 codeReify a) (ap1 codeReify b)
  in ruleTrans (axRecNd poo codeReifyStep a b)
     (ruleTrans (fanRed (Lift (KT tagAp2R)) (Fan (Lift (KT pairCFR)) (Post Snd Pair) Pair) Pair orig recs)
     (ruleTrans (congL Pair (ap2 (Fan (Lift (KT pairCFR)) (Post Snd Pair) Pair) orig recs)
                       (ruleTrans (liftRed (KT tagAp2R) orig recs) (axKT tagAp2R orig)))
     (congR Pair tagAp2R
       (ruleTrans (fanRed (Lift (KT pairCFR)) (Post Snd Pair) Pair orig recs)
       (ruleTrans (congL Pair (ap2 (Post Snd Pair) orig recs)
                         (ruleTrans (liftRed (KT pairCFR) orig recs) (axKT pairCFR orig)))
       (congR Pair pairCFR
         (ruleTrans (postRed Snd Pair orig recs) (axSnd orig recs))))))))

------------------------------------------------------------------------
-- Correctness: ap1 codeReify (reify t) = reify (code (reify t))
--
-- Proof by structural induction on t : Tree.

codeReifyCorrect : (t : Tree) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap1 codeReify (reify t)) (reify (code (reify t))))
codeReifyCorrect lf = codeReifyBase
codeReifyCorrect (nd a b) =
  -- reify(nd a b) = Pair(reify a, reify b)
  -- code(reify(nd a b)) = code(ap2 Pair (reify a) (reify b))
  --   = nd tagAp2 (nd (codeF2 Pair) (nd (code(reify a)) (code(reify b))))
  -- reify of that = Pair(tagAp2R, Pair(pairCFR, Pair(reify(code(reify a)), reify(code(reify b)))))
  --
  -- codeReify(Pair(reify a, reify b))
  --   = Pair(tagAp2R, Pair(pairCFR, Pair(codeReify(reify a), codeReify(reify b))))
  -- By IH: codeReify(reify a) = reify(code(reify a))
  --        codeReify(reify b) = reify(code(reify b))
  -- So the terms match.
  ruleTrans (codeReifyStep' (reify a) (reify b))
  (ruleTrans (congR Pair tagAp2R
    (congR Pair pairCFR
      (ruleTrans (congL Pair (ap1 codeReify (reify b)) (codeReifyCorrect a))
                 (congR Pair (reify (code (reify a))) (codeReifyCorrect b)))))
  (axRefl _))
