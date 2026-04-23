{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.CorDef -- definition of the BRA functor  cor  (Guard's  num ,
-- Def 10, guard15.pdf p.13).
--
--  cor  is a BRA Fun1 whose intended behaviour is
--
--     cor(t)  =  reify (code t)      for every  Term  t .
--
-- Rule 1 of Def 10 ( cor(O) = reify(code O) = O ) is realised by
-- computation: evaluating  ap1 cor O  via  axRecLf falseT stepCor
-- gives  falseT , which happens to equal  reify(code O) = O  only after
-- a transit through the IH; see  Guard.CodeOfReifyUnify.corOfReify .
-- Rules 2-4 (on  var ,  ap1  and  ap2  shapes) are stipulated as
-- DerivF constructors  axCorVar ,  axCorAp1 ,  axCorAp2  in
-- Guard.DerivF — they cannot be obtained from  Rec  alone because
-- Rec only reduces on  O  and  Pair  shapes.
--
-- This module lives between  Guard.Term  and  Guard.DerivF  so that
-- DerivF's axioms can reference  cor  by name.  Downstream modules
-- (CodeOfReifyUnify and callers) import  cor  /  stepCor  from here.
--
-- Separating the functor definition from the derivation relation
-- mirrors Guard's treatment of  num  as a defined functor inside BRA,
-- not an additional axiom (guard15.pdf, Def 10).  See
-- Guard/NEXT-SESSION-EX24.md "Path A step 1".

module Guard.CorDef where

open import Guard.Base
open import Guard.Term

------------------------------------------------------------------------
-- Constants used by the Rec step.

tagAp2T : Term
tagAp2T = reify tagAp2

pairCodeF2T : Term
pairCodeF2T = reify (codeF2 Pair)

------------------------------------------------------------------------
-- Fallback term used as the Rec base.  Any closed term works; we use
--  falseT = ap2 Pair O O  to match Guard.DerivF.falseT .

falseT : Term
falseT = ap2 Pair O O

------------------------------------------------------------------------
-- step_cor : Fun2.
--
-- At  orig = Pair a b  (i.e.  reify (nd A B) ) with recs = Pair (cor a)
-- (cor b) ,  ap2 stepCor orig recs  reduces to
--
--     Pair tagAp2T (Pair pairCodeF2T recs) .
--
-- After the induction hypothesis replaces  cor a  and  cor b  with
-- reify(code a) and reify(code b), this is exactly reify(code (Pair a
-- b)).  See  Guard.CodeOfReifyUnify.stepCorRed  for the detailed
-- reduction proof.

stepCor : Fun2
stepCor = Fan (Lift (KT tagAp2T))
              (Fan (Lift (KT pairCodeF2T))
                   (Post Snd Pair)
                   Pair)
              Pair

------------------------------------------------------------------------
-- cor : Fun1 = Rec falseT stepCor.

cor : Fun1
cor = Rec falseT stepCor
