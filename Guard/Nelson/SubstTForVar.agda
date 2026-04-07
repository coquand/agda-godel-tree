{-# OPTIONS --safe --without-K --exact-split #-}

module Guard.Nelson.SubstTForVar where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.SubstTFor
open import Guard.StepReduce
open import Guard.Nelson.SubstTForNd

------------------------------------------------------------------------
-- Variable case:
-- When the tag IS tagVarT, the step function checks if the payload
-- matches the target (var 12), and returns replacement (var 11) or
-- the original node.
--
-- We need to unfold innerBranchF and show the IfLf chain.

------------------------------------------------------------------------
-- Unfold innerBranchF = Fan matchTgtF replOrigF IfLf

innerBranchFUnfold : {hyp : Equation} (orig recs : Term) ->
  Deriv hyp (eqn (ap2 innerBranchF orig recs)
                 (ap2 IfLf (ap2 matchTgtF orig recs)
                           (ap2 replOrigF orig recs)))
innerBranchFUnfold orig recs = fanRed matchTgtF replOrigF IfLf orig recs

------------------------------------------------------------------------
-- Unfold matchTgtF = Fan (Lift Snd) (constF2 (var v12)) TreeEq

private
  v11 : Nat
  v11 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
  v12 : Nat
  v12 = suc v11

matchTgtFUnfold : {hyp : Equation} (orig recs : Term) ->
  Deriv hyp (eqn (ap2 matchTgtF orig recs)
                 (ap2 TreeEq (ap2 (Lift Snd) orig recs)
                             (ap2 (constF2 (var v12)) orig recs)))
matchTgtFUnfold orig recs = fanRed (Lift Snd) (constF2 (var v12)) TreeEq orig recs

-- At (ap2 Pair a b, recs): matchTgtF = TreeEq(b, var 12)
matchTgtFAtPair : {hyp : Equation} (a b recs : Term) ->
  Deriv hyp (eqn (ap2 matchTgtF (ap2 Pair a b) recs)
                 (ap2 TreeEq b (var v12)))
matchTgtFAtPair a b recs =
  ruleTrans (matchTgtFUnfold (ap2 Pair a b) recs)
  (ruleTrans (congL TreeEq (ap2 (constF2 (var v12)) (ap2 Pair a b) recs)
               (ruleTrans (liftRed Snd (ap2 Pair a b) recs) (axSnd a b)))
             (congR TreeEq b (constF2Red (var v12) (ap2 Pair a b) recs)))

------------------------------------------------------------------------
-- Unfold replOrigF = Fan (constF2 (var v11)) Const Pair

replOrigFUnfold : {hyp : Equation} (orig recs : Term) ->
  Deriv hyp (eqn (ap2 replOrigF orig recs)
                 (ap2 Pair (ap2 (constF2 (var v11)) orig recs)
                           (ap2 Const orig recs)))
replOrigFUnfold orig recs = fanRed (constF2 (var v11)) Const Pair orig recs

-- At (orig, recs): replOrigF = Pair(var 11, orig)
replOrigFRed : {hyp : Equation} (orig recs : Term) ->
  Deriv hyp (eqn (ap2 replOrigF orig recs)
                 (ap2 Pair (var v11) orig))
replOrigFRed orig recs =
  ruleTrans (replOrigFUnfold orig recs)
  (ruleTrans (congL Pair (ap2 Const orig recs) (constF2Red (var v11) orig recs))
             (congR Pair (var v11) (axConst orig recs)))

------------------------------------------------------------------------
-- Combined: innerBranchF at (ap2 Pair a b, recs)
-- = IfLf(TreeEq(b, var 12), Pair(var 11, ap2 Pair a b))

innerBranchFAtPair : {hyp : Equation} (a b recs : Term) ->
  Deriv hyp (eqn (ap2 innerBranchF (ap2 Pair a b) recs)
                 (ap2 IfLf (ap2 TreeEq b (var v12))
                           (ap2 Pair (var v11) (ap2 Pair a b))))
innerBranchFAtPair a b recs =
  ruleTrans (innerBranchFUnfold (ap2 Pair a b) recs)
  (ruleTrans (congL IfLf (ap2 replOrigF (ap2 Pair a b) recs)
               (matchTgtFAtPair a b recs))
             (congR IfLf (ap2 TreeEq b (var v12))
               (replOrigFRed (ap2 Pair a b) recs)))

------------------------------------------------------------------------
-- Variable step: when TreeEq(a, tagVarT) = O (true)
--
-- ap1 substTFor (ap2 Pair a b)
-- = ap2 IfLf O (ap2 Pair innerBranch recs)   [after isVar = O]
-- = innerBranch                                [axIfLfL]
-- = IfLf(TreeEq(b, var 12), Pair(var 11, ap2 Pair a b))

substTForVarStep : {hyp : Equation}
  (a b : Term) ->
  Deriv hyp (eqn (ap2 TreeEq a tagVarT) O) ->
  Deriv hyp (eqn (ap1 substTFor (ap2 Pair a b))
                 (ap2 IfLf (ap2 TreeEq b (var v12))
                           (ap2 Pair (var v11) (ap2 Pair a b))))
substTForVarStep a b treeEqTrue =
  ruleTrans (substTForNdUnfold a b)
  (ruleTrans (stepSubstUnfold (ap2 Pair a b) recs)
  (ruleTrans (congL IfLf (ap2 outerPairF (ap2 Pair a b) recs)
               (isVarFAtPair a b recs))
  (ruleTrans (congR IfLf (ap2 TreeEq a tagVarT)
               (ruleTrans (outerPairFUnfold (ap2 Pair a b) recs)
                 (congR Pair (ap2 innerBranchF (ap2 Pair a b) recs)
                   (sndArgRed (ap2 Pair a b) recs))))
  (ruleTrans (congL IfLf (ap2 Pair (ap2 innerBranchF (ap2 Pair a b) recs) recs) treeEqTrue)
  (ruleTrans (axIfLfL (ap2 innerBranchF (ap2 Pair a b) recs) recs)
             (innerBranchFAtPair a b recs))))))
  where recs = ap2 Pair (ap1 substTFor a) (ap1 substTFor b)
