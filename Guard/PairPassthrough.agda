{-# OPTIONS --safe --without-K --exact-split #-}

module Guard.PairPassthrough where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.ThFunTFor
open import Guard.ThFunTForDefs
open import Guard.ThFunTForCases0
open import Guard.ThFunTForCases1
open import Guard.ThFunTForCases2
open import Guard.ThFunTForCases3
open import Guard.ThFunTForCorrectDefs

------------------------------------------------------------------------
-- When the first element of a Pair is itself a Pair, all tagCheck
-- comparisons against natCode values return Pair O O.
--
-- TreeEq(Pair(Pair(a1,a2), b), reify(natCode n)) = Pair O O for all n.

private
  poo : Term
  poo = ap2 Pair O O

-- n=0: TreeEq(Pair(x,y), O) = Pair O O
-- n>=1: TreeEq(Pair(Pair(a1,a2), b), Pair(O, Z))
--     = IfLf(TreeEq(Pair(a1,a2), O), Pair(TreeEq(b, Z), Pair(O,O)))
--     = IfLf(Pair O O, ...) = Pair O O

pairPairVsNat : (a1 a2 b : Term) (n : Nat) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 TreeEq (ap2 Pair (ap2 Pair a1 a2) b) (reify (natCode n))) poo)
pairPairVsNat a1 a2 b zero = axTreeEqNL (ap2 Pair a1 a2) b
pairPairVsNat a1 a2 b (suc n) =
  ruleTrans (axTreeEqNN (ap2 Pair a1 a2) b O (reify (natCode n)))
  (ruleTrans (congL IfLf (ap2 Pair (ap2 TreeEq b (reify (natCode n))) poo)
               (axTreeEqNL a1 a2))
             (axIfLfN O O (ap2 TreeEq b (reify (natCode n))) poo))

------------------------------------------------------------------------
-- When tag = Pair(O, Pair(Pair(c1,c2), d)), all natCode checks miss.
-- This covers encAxI sub-proofs where the first element starts with O
-- but the inner data part is Pair-tagged (code t is always nd).

oPairPairVsNat : (c1 c2 d : Term) (n : Nat) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 TreeEq (ap2 Pair O (ap2 Pair (ap2 Pair c1 c2) d)) (reify (natCode n))) poo)
oPairPairVsNat c1 c2 d zero = axTreeEqNL O (ap2 Pair (ap2 Pair c1 c2) d)
oPairPairVsNat c1 c2 d (suc n) =
  ruleTrans (axTreeEqNN O (ap2 Pair (ap2 Pair c1 c2) d) O (reify (natCode n)))
  (ruleTrans (congL IfLf (ap2 Pair (ap2 TreeEq (ap2 Pair (ap2 Pair c1 c2) d) (reify (natCode n))) poo) axTreeEqLL)
  (ruleTrans (axIfLfL (ap2 TreeEq (ap2 Pair (ap2 Pair c1 c2) d) (reify (natCode n))) poo)
             (pairPairVsNat c1 c2 d n)))

oPairBranchMiss : (c1 c2 d x : Term) (n : Nat) (caseN tail : Fun2) (recs : Term) ->
  {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (branch (tagCheck n) caseN tail)
                       (ap2 Pair (ap2 Pair O (ap2 Pair (ap2 Pair c1 c2) d)) x) recs)
                 (ap2 tail (ap2 Pair (ap2 Pair O (ap2 Pair (ap2 Pair c1 c2) d)) x) recs))
oPairBranchMiss c1 c2 d x n caseN tail recs =
  branchMiss (tagCheck n) caseN tail
    (ap2 Pair (ap2 Pair O (ap2 Pair (ap2 Pair c1 c2) d)) x) recs
    (ruleTrans (tagCheckRed n (ap2 Pair O (ap2 Pair (ap2 Pair c1 c2) d)) x recs)
               (oPairPairVsNat c1 c2 d n))

-- Combined: tagCheck miss for Pair(Pair(a1,a2),b) as tag
pairBranchMiss : (a1 a2 b x : Term) (n : Nat) (caseN tail : Fun2) (recs : Term) ->
  {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (branch (tagCheck n) caseN tail)
                       (ap2 Pair (ap2 Pair (ap2 Pair a1 a2) b) x) recs)
                 (ap2 tail (ap2 Pair (ap2 Pair (ap2 Pair a1 a2) b) x) recs))
pairBranchMiss a1 a2 b x n caseN tail recs =
  branchMiss (tagCheck n) caseN tail
    (ap2 Pair (ap2 Pair (ap2 Pair a1 a2) b) x) recs
    (ruleTrans (tagCheckRed n (ap2 Pair (ap2 Pair a1 a2) b) x recs)
               (pairPairVsNat a1 a2 b n))
