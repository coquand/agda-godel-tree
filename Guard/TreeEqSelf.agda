{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.TreeEqSelf — standalone proof of  TreeEq(t, t) = O  via Schema F.
--
-- Extracted from Guard.GodelII so that V3 infrastructure can depend on it
-- without transitively importing Guard.Thm14E (which has pattern matches
-- that break once new Deriv constructors are added).

module Guard.TreeEqSelf where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce

private
  poo : Term
  poo = ap2 Pair O O

  v0  : Term
  v0  = var zero

  v1T : Term
  v1T = var (suc zero)

private
  teI : Fun1
  teI = Comp2 TreeEq I I

  teSelf : Fun2
  teSelf = Fan (Post Fst (Post Snd Pair))
               (Fan (Post Snd (Post Snd Pair)) (Lift (KT poo)) Pair)
               IfLf

  teIRed : (t : Term) -> {hyp : Equation} ->
           Deriv hyp (eqn (ap1 teI t) (ap2 TreeEq t t))
  teIRed t =
    ruleTrans (axComp2 TreeEq I I t)
    (ruleTrans (congL TreeEq (ap1 I t) (axI t)) (congR TreeEq t (axI t)))

  teSelfRed : (ab fa fb : Term) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap2 teSelf ab (ap2 Pair fa fb)) (ap2 IfLf fa (ap2 Pair fb poo)))
  teSelfRed ab fa fb =
    let recs = ap2 Pair fa fb
    in ruleTrans (fanRed (Post Fst (Post Snd Pair))
                  (Fan (Post Snd (Post Snd Pair)) (Lift (KT poo)) Pair) IfLf ab recs)
       (ruleTrans (congL IfLf (ap2 (Fan (Post Snd (Post Snd Pair)) (Lift (KT poo)) Pair) ab recs)
         (ruleTrans (postRed Fst (Post Snd Pair) ab recs)
         (ruleTrans (cong1 Fst (postRed Snd Pair ab recs))
         (ruleTrans (cong1 Fst (axSnd ab recs)) (axFst fa fb)))))
       (congR IfLf fa
         (ruleTrans (fanRed (Post Snd (Post Snd Pair)) (Lift (KT poo)) Pair ab recs)
         (ruleTrans (congL Pair (ap2 (Lift (KT poo)) ab recs)
           (ruleTrans (postRed Snd (Post Snd Pair) ab recs)
           (ruleTrans (cong1 Snd (postRed Snd Pair ab recs))
           (ruleTrans (cong1 Snd (axSnd ab recs)) (axSnd fa fb)))))
         (congR Pair fb (ruleTrans (liftRed (KT poo) ab recs) (axKT poo ab)))))))

  fBase : {hyp : Equation} -> Deriv hyp (eqn (ap1 teI O) O)
  fBase = ruleTrans (teIRed O) axTreeEqLL

  fStep : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 teI (ap2 Pair v0 v1T))
                   (ap2 teSelf (ap2 Pair v0 v1T) (ap2 Pair (ap1 teI v0) (ap1 teI v1T))))
  fStep =
    let ab = ap2 Pair v0 v1T ; fa = ap1 teI v0 ; fb = ap1 teI v1T
    in ruleTrans (ruleTrans (teIRed ab) (axTreeEqNN v0 v1T v0 v1T))
       (ruleSym (ruleTrans (teSelfRed ab fa fb)
                (ruleTrans (congL IfLf (ap2 Pair fb poo) (teIRed v0))
                (congR IfLf (ap2 TreeEq v0 v0) (congL Pair poo (teIRed v1T))))))

  gBase : {hyp : Equation} -> Deriv hyp (eqn (ap1 (KT O) O) O)
  gBase = axKT O O

  gStep : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (KT O) (ap2 Pair v0 v1T))
                   (ap2 teSelf (ap2 Pair v0 v1T) (ap2 Pair (ap1 (KT O) v0) (ap1 (KT O) v1T))))
  gStep =
    let ab = ap2 Pair v0 v1T ; ga = ap1 (KT O) v0 ; gb = ap1 (KT O) v1T
    in ruleTrans (axKT O ab)
       (ruleSym (ruleTrans (teSelfRed ab ga gb)
                (ruleTrans (congL IfLf (ap2 Pair gb poo) (axKT O v0))
                (ruleTrans (axIfLfL gb poo) (axKT O v1T)))))

treeEqSelfAll : {hyp : Equation} -> Deriv hyp (eqn (ap1 teI v0) (ap1 (KT O) v0))
treeEqSelfAll = ruleF teI (KT O) O teSelf fBase fStep gBase gStep

treeEqSelf : (t : Term) -> {hyp : Equation} ->
             Deriv hyp (eqn (ap2 TreeEq t t) O)
treeEqSelf t =
  ruleTrans (ruleSym (teIRed t))
    (ruleTrans (ruleInst zero t treeEqSelfAll) (axKT O t))
