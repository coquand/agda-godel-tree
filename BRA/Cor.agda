{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Cor -- our tree-based analog of Guard's  num  (Exercise 24 [7],
-- guard15.pdf p.14).
--
-- Guard's  num  is a 1-ary BRA functor such that  num(n) is the
-- Gödel number of the numeral  s^n(0) .  Its domain is numerals,
-- not arbitrary BRA terms.
--
-- In our tree-based BRA (leaf | nd(a,b) replacing 0 | S(x)), the
-- analog is  cor : Fun1  satisfying
--
--     cor(reify t)  =  reify (code (reify t))    for every  Tree  t .
--
-- i.e.  cor  takes a reified tree (our analog of a numeral) and
-- returns its Gödel code (again a reified tree).  On non-tree-shaped
-- Terms (variables, open  ap1 / ap2  applications)  cor  neither
-- reduces nor needs to reduce, mirroring Guard's  num  which is
-- defined on numerals only.
--
--  cor  is built from  Rec  plus the  Fan / Lift / KT / Post / Pair
-- combinators of BRA.Term; no new primitives.
--
-- No postulates, no holes.

module BRA.Cor where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.StepReduce

------------------------------------------------------------------------
-- Constants used by the step function.

private
  tagAp2T : Term
  tagAp2T = reify tagAp2

  pairCodeF2T : Term
  pairCodeF2T = reify (codeF2 Pair)

------------------------------------------------------------------------
-- step_cor and cor.

stepCor : Fun2
stepCor = Fan (Lift (KT tagAp2T))
              (Fan (Lift (KT pairCodeF2T))
                   (Post Snd Pair)
                   Pair)
              Pair

cor : Fun1
cor = Rec falseT stepCor

------------------------------------------------------------------------
-- stepCorRed: reduction of stepCor at generic (orig, recs).

stepCorRed : (orig recs : Term) ->
  Deriv (atomic (eqn (ap2 stepCor orig recs)
                      (ap2 Pair tagAp2T (ap2 Pair pairCodeF2T recs))))
stepCorRed orig recs =
  let inner = Fan (Lift (KT pairCodeF2T)) (Post Snd Pair) Pair
      innerRed : Deriv (atomic (eqn (ap2 inner orig recs)
                                     (ap2 Pair pairCodeF2T recs)))
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

corOfReify : (t : Tree) ->
  Deriv (atomic (eqn (ap1 cor (reify t)) (reify (code (reify t)))))
corOfReify lf = axRecLf falseT stepCor
corOfReify (nd a b) =
  let reifyA = reify a
      reifyB = reify b
      orig   = ap2 Pair reifyA reifyB
      corA   = ap1 cor reifyA
      corB   = ap1 cor reifyB
      recs   = ap2 Pair corA corB
      rA     = reify (code reifyA)
      rB     = reify (code reifyB)
      ihA    : Deriv (atomic (eqn corA rA))
      ihA    = corOfReify a
      ihB    : Deriv (atomic (eqn corB rB))
      ihB    = corOfReify b
      s1     : Deriv (atomic (eqn (ap1 cor orig) (ap2 stepCor orig recs)))
      s1     = axRecNd falseT stepCor reifyA reifyB
      s2     : Deriv (atomic (eqn (ap2 stepCor orig recs)
                                   (ap2 Pair tagAp2T (ap2 Pair pairCodeF2T recs))))
      s2     = stepCorRed orig recs
      recsR  = ap2 Pair rA rB
      s3     : Deriv (atomic (eqn (ap2 Pair pairCodeF2T recs)
                                   (ap2 Pair pairCodeF2T recsR)))
      s3     = congR Pair pairCodeF2T
                 (ruleTrans (congL Pair corB ihA)
                            (congR Pair rA ihB))
      s4     : Deriv (atomic (eqn (ap2 Pair tagAp2T (ap2 Pair pairCodeF2T recs))
                                   (ap2 Pair tagAp2T (ap2 Pair pairCodeF2T recsR))))
      s4     = congR Pair tagAp2T s3
  in ruleTrans s1 (ruleTrans s2 s4)
