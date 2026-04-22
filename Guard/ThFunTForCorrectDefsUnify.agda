{-# OPTIONS --safe --without-K --exact-split #-}

module Guard.ThFunTForCorrectDefsUnify where

open import Guard.Base
open import Guard.Term
open import Guard.Formula
open import Guard.DerivF
open import Guard.StepReduceUnify
open import Guard.ThFun
open import Guard.ThFunTFor
open import Guard.ThFunTForDefs
open import Guard.ThFunTForCases2

------------------------------------------------------------------------
-- natCode equality in Deriv

private
  n13 : Nat
  n13 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))

natCodeSelfEq : (n : Nat) ->
  Deriv (eqF (ap2 TreeEq (reify (natCode n)) (reify (natCode n))) O)
natCodeSelfEq zero = axTreeEqLL
natCodeSelfEq (suc n) =
  ruleTrans (axTreeEqNN O (reify (natCode n)) O (reify (natCode n)))
  (ruleTrans (congL IfLf (ap2 Pair (ap2 TreeEq (reify (natCode n)) (reify (natCode n))) falseT) axTreeEqLL)
  (ruleTrans (axIfLfL (ap2 TreeEq (reify (natCode n)) (reify (natCode n))) falseT)
             (natCodeSelfEq n)))

------------------------------------------------------------------------
-- natCode inequality in Deriv

natCodeNeq : (n m : Nat) -> Eq (natEq n m) false ->
  Deriv (eqF (ap2 TreeEq (reify (natCode n)) (reify (natCode m))) falseT)
natCodeNeq zero zero ()
natCodeNeq zero (suc m) pf = axTreeEqLN O (reify (natCode m))
natCodeNeq (suc n) zero pf = axTreeEqNL O (reify (natCode n))
natCodeNeq (suc n) (suc m) pf =
  ruleTrans (axTreeEqNN O (reify (natCode n)) O (reify (natCode m)))
  (ruleTrans (congL IfLf (ap2 Pair (ap2 TreeEq (reify (natCode n)) (reify (natCode m))) falseT) axTreeEqLL)
  (ruleTrans (axIfLfL (ap2 TreeEq (reify (natCode n)) (reify (natCode m))) falseT)
             (natCodeNeq n m pf)))

------------------------------------------------------------------------
-- Rec unfolding + IH substitution

recUnfoldIH : (a b : Tree) ->
  Deriv (eqF (ap1 thFunTFor (reify a)) (reify (thFun a))) ->
  Deriv (eqF (ap1 thFunTFor (reify b)) (reify (thFun b))) ->
  Deriv (eqF (ap1 thFunTFor (ap2 Pair (reify a) (reify b)))
                 (ap2 thFunStep (ap2 Pair (reify a) (reify b))
                                (ap2 Pair (reify (thFun a)) (reify (thFun b)))))
recUnfoldIH a b iha ihb =
  ruleTrans (recNdRed O thFunStep (reify a) (reify b))
  (congR thFunStep (ap2 Pair (reify a) (reify b))
    (ruleTrans (congL Pair (ap1 thFunTFor (reify b)) iha)
               (congR Pair (reify (thFun a)) ihb)))

------------------------------------------------------------------------
-- tagCheck reduction

tagCheckRed : (n : Nat) (tag data' recs : Term) ->
  Deriv (eqF (ap2 (tagCheck n) (ap2 Pair tag data') recs)
                 (ap2 TreeEq tag (reify (natCode n))))
tagCheckRed n tag data' recs =
  ruleTrans (fanRed (Lift Fst) (kF2 (reify (natCode n))) TreeEq (ap2 Pair tag data') recs)
  (ruleTrans (congL TreeEq (ap2 (kF2 (reify (natCode n))) (ap2 Pair tag data') recs)
               (ruleTrans (liftRed Fst (ap2 Pair tag data') recs) (axFst tag data')))
             (congR TreeEq tag (constF2Red (reify (natCode n)) (ap2 Pair tag data') recs)))

------------------------------------------------------------------------
-- Branch hit/miss

branchHit : (check result rest : Fun2) (orig recs : Term) ->
  Deriv (eqF (ap2 check orig recs) O) ->
  Deriv (eqF (ap2 (branch check result rest) orig recs) (ap2 result orig recs))
branchHit check result rest orig recs checkEqO =
  ruleTrans (fanRed check (Fan result rest Pair) IfLf orig recs)
  (ruleTrans (congL IfLf (ap2 (Fan result rest Pair) orig recs) checkEqO)
  (ruleTrans (congR IfLf O (fanRed result rest Pair orig recs))
             (axIfLfL (ap2 result orig recs) (ap2 rest orig recs))))

branchMiss : (check result rest : Fun2) (orig recs : Term) ->
  Deriv (eqF (ap2 check orig recs) falseT) ->
  Deriv (eqF (ap2 (branch check result rest) orig recs) (ap2 rest orig recs))
branchMiss check result rest orig recs checkEqPoo =
  ruleTrans (fanRed check (Fan result rest Pair) IfLf orig recs)
  (ruleTrans (congL IfLf (ap2 (Fan result rest Pair) orig recs) checkEqPoo)
  (ruleTrans (congR IfLf falseT (fanRed result rest Pair orig recs))
             (axIfLfN O O (ap2 result orig recs) (ap2 rest orig recs))))

------------------------------------------------------------------------
-- Guard dispatch helpers

private
  -- The lfDispatch and dataIsLf combinators from ThFunTFor
  dataIsLfF : Fun2
  dataIsLfF = Fan (Lift Snd) (kF2 O) TreeEq

  tag13CheckF : Fun2
  tag13CheckF = Fan (Lift Fst) (kF2 (reify (natCode n13))) TreeEq

  lfDispatchF : Fun2
  lfDispatchF = branch tag13CheckF case13 (kF2 O)

-- When data = Pair x y (nd case): thFunStep selects ndDispatch
guardNd : (tag x y recs : Term) ->
  Deriv (eqF (ap2 thFunStep (ap2 Pair tag (ap2 Pair x y)) recs)
                 (ap2 ndDispatch (ap2 Pair tag (ap2 Pair x y)) recs))
guardNd tag x y recs =
  branchMiss dataIsLfF lfDispatchF ndDispatch
    (ap2 Pair tag (ap2 Pair x y)) recs
    (ruleTrans (fanRed (Lift Snd) (kF2 O) TreeEq (ap2 Pair tag (ap2 Pair x y)) recs)
    (ruleTrans (congL TreeEq (ap2 (kF2 O) (ap2 Pair tag (ap2 Pair x y)) recs)
                 (ruleTrans (liftRed Snd (ap2 Pair tag (ap2 Pair x y)) recs)
                            (axSnd tag (ap2 Pair x y))))
    (ruleTrans (congR TreeEq (ap2 Pair x y)
                 (constF2Red O (ap2 Pair tag (ap2 Pair x y)) recs))
               (axTreeEqNL x y))))

-- When data = O (lf case): thFunStep selects lfDispatch
guardLf : (tag recs : Term) ->
  Deriv (eqF (ap2 thFunStep (ap2 Pair tag O) recs)
                 (ap2 lfDispatchF (ap2 Pair tag O) recs))
guardLf tag recs =
  branchHit dataIsLfF lfDispatchF ndDispatch
    (ap2 Pair tag O) recs
    (ruleTrans (fanRed (Lift Snd) (kF2 O) TreeEq (ap2 Pair tag O) recs)
    (ruleTrans (congL TreeEq (ap2 (kF2 O) (ap2 Pair tag O) recs)
                 (ruleTrans (liftRed Snd (ap2 Pair tag O) recs) (axSnd tag O)))
    (ruleTrans (congR TreeEq O (constF2Red O (ap2 Pair tag O) recs))
               axTreeEqLL)))

------------------------------------------------------------------------
-- ndDispatch branch selection: skip one branch

ndBranchMiss : (k n : Nat) (caseN tail : Fun2) (data' recs : Term) ->
  Eq (natEq k n) false ->
  Deriv (eqF (ap2 (branch (tagCheck n) caseN tail) (ap2 Pair (reify (natCode k)) data') recs)
                 (ap2 tail (ap2 Pair (reify (natCode k)) data') recs))
ndBranchMiss k n caseN tail data' recs neq =
  branchMiss (tagCheck n) caseN tail
    (ap2 Pair (reify (natCode k)) data') recs
    (ruleTrans (tagCheckRed n (reify (natCode k)) data' recs) (natCodeNeq k n neq))

ndBranchHit : (k : Nat) (caseK tail : Fun2) (data' recs : Term) ->
  Deriv (eqF (ap2 (branch (tagCheck k) caseK tail) (ap2 Pair (reify (natCode k)) data') recs)
                 (ap2 caseK (ap2 Pair (reify (natCode k)) data') recs))
ndBranchHit k caseK tail data' recs =
  branchHit (tagCheck k) caseK tail
    (ap2 Pair (reify (natCode k)) data') recs
    (ruleTrans (tagCheckRed k (reify (natCode k)) data' recs) (natCodeSelfEq k))
