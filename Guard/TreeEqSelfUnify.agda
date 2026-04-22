{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.TreeEqSelfUnify -- port of Guard.TreeEqSelf to DerivF.
--
-- treeEqSelfReify : structural self-equality for reified trees,
-- derived by Agda-level meta-induction.  No ruleInst needed.
--
-- treeEqSelfAll / treeEqSelf use  ruleF  (Schema F) and  ruleInst .
-- In the hyp-less DerivF,  ruleInst  has no side condition, so
-- treeEqSelf's signature is simplified (no  Eq (substEq _ _ _)
-- witness required — there is no hyp).
--
-- Part of the unify-2 migration.

module Guard.TreeEqSelfUnify where

open import Guard.Base
open import Guard.Term
open import Guard.Formula
open import Guard.DerivF
open import Guard.StepReduceUnify

private
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

  teIRed : (t : Term) ->
           Deriv (atomic (eqn (ap1 teI t) (ap2 TreeEq t t)))
  teIRed t =
    ruleTrans (axComp2 TreeEq I I t)
    (ruleTrans (congL TreeEq (ap1 I t) (axI t)) (congR TreeEq t (axI t)))

  teSelfRed : (ab fa fb : Term) ->
    Deriv (atomic (eqn (ap2 teSelf ab (ap2 Pair fa fb)) (ap2 IfLf fa (ap2 Pair fb poo))))
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

  fBase : Deriv (atomic (eqn (ap1 teI O) O))
  fBase = ruleTrans (teIRed O) axTreeEqLL

  fStep : Deriv (atomic (eqn (ap1 teI (ap2 Pair v0 v1T))
                              (ap2 teSelf (ap2 Pair v0 v1T)
                                          (ap2 Pair (ap1 teI v0) (ap1 teI v1T)))))
  fStep =
    let ab = ap2 Pair v0 v1T ; fa = ap1 teI v0 ; fb = ap1 teI v1T
    in ruleTrans (ruleTrans (teIRed ab) (axTreeEqNN v0 v1T v0 v1T))
       (ruleSym (ruleTrans (teSelfRed ab fa fb)
                (ruleTrans (congL IfLf (ap2 Pair fb poo) (teIRed v0))
                (congR IfLf (ap2 TreeEq v0 v0) (congL Pair poo (teIRed v1T))))))

  gBase : Deriv (atomic (eqn (ap1 (KT O) O) O))
  gBase = axKT O O

  gStep : Deriv (atomic (eqn (ap1 (KT O) (ap2 Pair v0 v1T))
                              (ap2 teSelf (ap2 Pair v0 v1T)
                                          (ap2 Pair (ap1 (KT O) v0) (ap1 (KT O) v1T)))))
  gStep =
    let ab = ap2 Pair v0 v1T ; ga = ap1 (KT O) v0 ; gb = ap1 (KT O) v1T
    in ruleTrans (axKT O ab)
       (ruleSym (ruleTrans (teSelfRed ab ga gb)
                (ruleTrans (congL IfLf (ap2 Pair gb poo) (axKT O v0))
                (ruleTrans (axIfLfL gb poo) (axKT O v1T)))))

treeEqSelfAll : Deriv (atomic (eqn (ap1 teI v0) (ap1 (KT O) v0)))
treeEqSelfAll = ruleF teI (KT O) O teSelf fBase fStep gBase gStep

-- In hyp-less DerivF, ruleInst has no side condition.  treeEqSelf
-- at any term t is unconditionally derivable.

treeEqSelf : (t : Term) -> Deriv (atomic (eqn (ap2 TreeEq t t) O))
treeEqSelf t =
  ruleTrans (ruleSym (teIRed t))
    (ruleTrans (ruleInst zero t treeEqSelfAll) (axKT O t))

------------------------------------------------------------------------
-- treeEqSelfReify: structural variant for reified-tree arguments.

treeEqSelfReify : (t : Tree) ->
                  Deriv (atomic (eqn (ap2 TreeEq (reify t) (reify t)) O))
treeEqSelfReify lf       = axTreeEqLL
treeEqSelfReify (nd a b) =
  let ra : Term ; ra = reify a
      rb : Term ; rb = reify b
      ihA : Deriv (atomic (eqn (ap2 TreeEq ra ra) O))
      ihA = treeEqSelfReify a
      ihB : Deriv (atomic (eqn (ap2 TreeEq rb rb) O))
      ihB = treeEqSelfReify b
  in ruleTrans (axTreeEqNN ra rb ra rb)
     (ruleTrans (congL IfLf (ap2 Pair (ap2 TreeEq rb rb) poo) ihA)
     (ruleTrans (axIfLfL (ap2 TreeEq rb rb) poo) ihB))
