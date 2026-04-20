{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.CodeOfReify -- an object-level "code of reify" operator.
--
-- cor : Fun1  such that  ap1 cor (reify t) = reify (code (reify t))
-- for every tree t.
--
-- Key observation: reify produces only O and (ap2 Pair ...) terms,
-- so cor can be built with plain Rec over that restricted subset.
-- No new primitive is needed.
--
-- Used by the classical Gödel I diagonal (one free variable) to
-- internalise the code-of-reify identity.  Ryan's proof avoids this
-- because "sub" is a PR function on Gödel numbers and the
-- numeral-for-Gödel-number bridge is PR too; in our tree setting,
-- cor plays the role of that bridge.

module Guard.CodeOfReify where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce

------------------------------------------------------------------------
-- Constants used by the step function.

private
  poo : Term
  poo = ap2 Pair O O

  tagAp2T : Term
  tagAp2T = reify tagAp2

  -- reify (codeF2 Pair) = Pair (reify (natCode 26)) O.  We leave this
  -- expression unfolded; Agda normalises it when needed.
  pairCodeF2T : Term
  pairCodeF2T = reify (codeF2 Pair)

------------------------------------------------------------------------
-- step_cor : Fun2
--
-- At orig = Pair a b (= reify(nd A B)) with recs = Pair (cor a) (cor b),
--   step_cor orig recs = Pair tagAp2T (Pair pairCodeF2T recs)
-- which equals reify (nd tagAp2 (nd (codeF2 Pair) (nd (code a) (code b))))
-- once the IH replaces cor(a), cor(b) with reify(code a), reify(code b).

stepCor : Fun2
stepCor = Fan (Lift (KT tagAp2T))
              (Fan (Lift (KT pairCodeF2T))
                   (Post Snd Pair)
                   Pair)
              Pair

cor : Fun1
cor = Rec poo stepCor

------------------------------------------------------------------------
-- stepCorRed: reduction of stepCor at generic (orig, recs).

stepCorRed : (orig recs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 stepCor orig recs)
                 (ap2 Pair tagAp2T (ap2 Pair pairCodeF2T recs)))
stepCorRed orig recs =
  let inner = Fan (Lift (KT pairCodeF2T)) (Post Snd Pair) Pair
      innerRed : Deriv _ (eqn (ap2 inner orig recs)
                              (ap2 Pair pairCodeF2T recs))
      innerRed =
        ruleTrans (fanRed (Lift (KT pairCodeF2T)) (Post Snd Pair) Pair orig recs)
        (ruleTrans (congL Pair (ap2 (Post Snd Pair) orig recs)
                     (constF2Red pairCodeF2T orig recs))
                   (congR Pair pairCodeF2T
                     (ruleTrans (postRed Snd Pair orig recs)
                                (axSnd orig recs))))
  in ruleTrans (fanRed (Lift (KT tagAp2T)) inner Pair orig recs)
     (ruleTrans (congL Pair (ap2 inner orig recs)
                  (constF2Red tagAp2T orig recs))
                (congR Pair tagAp2T innerRed))

------------------------------------------------------------------------
-- Main lemma: cor(reify t) = reify(code(reify t)) for every tree t.
--
-- Proved by induction on t.  The base and step cases unfold by
-- Rec's two axioms plus stepCorRed, with the nd-case completed by
-- the inductive hypotheses on a and b.

corOfReify : (t : Tree) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap1 cor (reify t)) (reify (code (reify t))))
corOfReify lf = axRecLf poo stepCor
corOfReify (nd a b) {hyp} =
  let reifyA = reify a
      reifyB = reify b
      orig   = ap2 Pair reifyA reifyB       -- = reify (nd a b)
      corA   = ap1 cor reifyA
      corB   = ap1 cor reifyB
      recs   = ap2 Pair corA corB
      rA     = reify (code reifyA)
      rB     = reify (code reifyB)
      ihA    : Deriv hyp (eqn corA rA)
      ihA    = corOfReify a
      ihB    : Deriv hyp (eqn corB rB)
      ihB    = corOfReify b
      -- Step 1: ap1 cor orig = ap2 stepCor orig recs (by axRecNd).
      s1     : Deriv hyp (eqn (ap1 cor orig) (ap2 stepCor orig recs))
      s1     = axRecNd poo stepCor reifyA reifyB
      -- Step 2: ap2 stepCor orig recs = Pair tagAp2T (Pair pairCodeF2T recs).
      s2     : Deriv hyp (eqn (ap2 stepCor orig recs)
                              (ap2 Pair tagAp2T (ap2 Pair pairCodeF2T recs)))
      s2     = stepCorRed orig recs
      -- Step 3: replace (cor a, cor b) in recs via IHs.
      recsR  = ap2 Pair rA rB
      s3     : Deriv hyp (eqn (ap2 Pair pairCodeF2T recs)
                              (ap2 Pair pairCodeF2T recsR))
      s3     = congR Pair pairCodeF2T
                 (ruleTrans (congL Pair corB ihA)
                            (congR Pair rA ihB))
      s4     : Deriv hyp (eqn (ap2 Pair tagAp2T (ap2 Pair pairCodeF2T recs))
                              (ap2 Pair tagAp2T (ap2 Pair pairCodeF2T recsR)))
      s4     = congR Pair tagAp2T s3
      -- Final goal: reify (code (ap2 Pair reifyA reifyB))
      --           = ap2 Pair tagAp2T (ap2 Pair pairCodeF2T recsR)
      -- which holds definitionally since
      --   code (ap2 Pair a b) = nd tagAp2 (nd (codeF2 Pair) (nd (code a)(code b)))
      -- and reify-nd distributes to ap2-Pair componentwise.
  in ruleTrans s1 (ruleTrans s2 s4)
