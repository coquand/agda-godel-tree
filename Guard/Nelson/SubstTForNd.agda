{-# OPTIONS --safe --without-K --exact-split #-}

module Guard.Nelson.SubstTForNd where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.SubstTFor
open import Guard.StepReduce

------------------------------------------------------------------------
-- substTFor unfolds at nd nodes via axRecNd:
--
-- ap1 substTFor (ap2 Pair a b)
-- = ap2 stepSubst (ap2 Pair a b) (ap2 Pair (ap1 substTFor a) (ap1 substTFor b))
--
-- Then stepSubst = Fan isVarF outerPairF IfLf, so:
-- = ap2 IfLf (ap2 isVarF orig recs) (ap2 outerPairF orig recs)
--   where orig = ap2 Pair a b, recs = ap2 Pair (ap1 substTFor a) (ap1 substTFor b)

substTForNdUnfold : {hyp : Equation} (a b : Term) ->
  Deriv hyp (eqn (ap1 substTFor (ap2 Pair a b))
                 (ap2 stepSubst (ap2 Pair a b)
                                (ap2 Pair (ap1 substTFor a)
                                          (ap1 substTFor b))))
substTForNdUnfold a b = recNdRed O stepSubst a b

------------------------------------------------------------------------
-- Unfold stepSubst = Fan isVarF outerPairF IfLf

stepSubstUnfold : {hyp : Equation} (orig recs : Term) ->
  Deriv hyp (eqn (ap2 stepSubst orig recs)
                 (ap2 IfLf (ap2 isVarF orig recs)
                           (ap2 outerPairF orig recs)))
stepSubstUnfold orig recs = fanRed isVarF outerPairF IfLf orig recs

------------------------------------------------------------------------
-- Unfold isVarF = Fan (Lift Fst) (constF2 tagVarT) TreeEq

isVarFUnfold : {hyp : Equation} (orig recs : Term) ->
  Deriv hyp (eqn (ap2 isVarF orig recs)
                 (ap2 TreeEq (ap2 (Lift Fst) orig recs)
                             (ap2 (constF2 tagVarT) orig recs)))
isVarFUnfold orig recs = fanRed (Lift Fst) (constF2 tagVarT) TreeEq orig recs

-- Lift Fst applied to (orig, recs) = Fst(orig)
liftFstRed : {hyp : Equation} (orig recs : Term) ->
  Deriv hyp (eqn (ap2 (Lift Fst) orig recs) (ap1 Fst orig))
liftFstRed orig recs = liftRed Fst orig recs

-- constF2 tagVarT applied to (orig, recs) = tagVarT
constTagVarRed : {hyp : Equation} (orig recs : Term) ->
  Deriv hyp (eqn (ap2 (constF2 tagVarT) orig recs) tagVarT)
constTagVarRed orig recs = constF2Red tagVarT orig recs

-- Combined: isVarF at (ap2 Pair a b, recs) = TreeEq(a, tagVarT)
isVarFAtPair : {hyp : Equation} (a b recs : Term) ->
  Deriv hyp (eqn (ap2 isVarF (ap2 Pair a b) recs)
                 (ap2 TreeEq a tagVarT))
isVarFAtPair a b recs =
  ruleTrans (isVarFUnfold (ap2 Pair a b) recs)
    (ruleTrans (congL TreeEq (ap2 (constF2 tagVarT) (ap2 Pair a b) recs)
                 (ruleTrans (liftFstRed (ap2 Pair a b) recs) (axFst a b)))
              (congR TreeEq a (constTagVarRed (ap2 Pair a b) recs)))

------------------------------------------------------------------------
-- Unfold outerPairF = Fan innerBranchF sndArg Pair

outerPairFUnfold : {hyp : Equation} (orig recs : Term) ->
  Deriv hyp (eqn (ap2 outerPairF orig recs)
                 (ap2 Pair (ap2 innerBranchF orig recs)
                           (ap2 sndArg orig recs)))
outerPairFUnfold orig recs = fanRed innerBranchF sndArg Pair orig recs

-- sndArg = Post Snd Pair, so sndArg(orig, recs) = Snd(Pair(orig, recs)) = recs
sndArgRed : {hyp : Equation} (orig recs : Term) ->
  Deriv hyp (eqn (ap2 sndArg orig recs) recs)
sndArgRed orig recs =
  ruleTrans (postRed Snd Pair orig recs)
            (axSnd orig recs)
