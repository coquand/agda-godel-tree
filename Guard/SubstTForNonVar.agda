{-# OPTIONS --safe --without-K --exact-split #-}

module Guard.SubstTForNonVar where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.SubstTFor
open import Guard.StepReduce
open import Guard.SubstTForNd

------------------------------------------------------------------------
-- Non-variable case:
-- When TreeEq(a, tagVarT) = ap2 Pair x y (i.e., false),
-- substTFor returns the recursive results (i.e., nd(rec_a, rec_b)).
--
-- Full chain for nd(a, b) when a is not tagVarT:
--
-- ap1 substTFor (ap2 Pair a b)
-- = ap2 stepSubst (ap2 Pair a b) recs           [axRecNd]
-- = ap2 IfLf (ap2 isVarF ...) (ap2 outerPairF ...)  [Fan]
-- = ap2 IfLf (ap2 TreeEq a tagVarT) (ap2 Pair inner recs)  [various reductions]
-- = ap2 IfLf (ap2 Pair x y) (ap2 Pair inner recs)  [hypothesis: TreeEq gives false]
-- = recs                                         [axIfLfN]
-- = ap2 Pair (ap1 substTFor a) (ap1 substTFor b)

-- When the non-variable test holds, the step result is the recursive results.
-- This lemma connects the full chain.

substTForNonVarStep : {hyp : Equation}
  (a b : Term) (x y : Term) ->
  Deriv hyp (eqn (ap2 TreeEq a tagVarT) (ap2 Pair x y)) ->
  Deriv hyp (eqn (ap1 substTFor (ap2 Pair a b))
                 (ap2 Pair (ap1 substTFor a) (ap1 substTFor b)))
substTForNonVarStep a b x y treeEqFalse =
  ruleTrans (substTForNdUnfold a b)
  (ruleTrans (stepSubstUnfold (ap2 Pair a b) recs)
  (ruleTrans (congL IfLf (ap2 outerPairF (ap2 Pair a b) recs)
               (isVarFAtPair a b recs))
  (ruleTrans (congR IfLf (ap2 TreeEq a tagVarT)
               (ruleTrans (outerPairFUnfold (ap2 Pair a b) recs)
                 (congR Pair (ap2 innerBranchF (ap2 Pair a b) recs)
                   (sndArgRed (ap2 Pair a b) recs))))
  (ruleTrans (congL IfLf (ap2 Pair (ap2 innerBranchF (ap2 Pair a b) recs) recs) treeEqFalse)
  (axIfLfN x y (ap2 innerBranchF (ap2 Pair a b) recs) recs)))))
  where recs = ap2 Pair (ap1 substTFor a) (ap1 substTFor b)
