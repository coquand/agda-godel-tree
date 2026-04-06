{-# OPTIONS --safe --without-K --exact-split #-}

-- SemSoundRefl.agda
-- Semantic soundness of axRefl (tag 17).
--
-- No IH, no side condition.
-- thFunTFor(enc) = Pair(x, x), so evalCode(x) = evalCode(x) trivially.

module Guard.SemSoundRefl where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.ThFunTForDefs
open import Guard.ThFunTFor
open import Guard.EvalCode
open import Guard.NelsonDispatch
open import Guard.NelsonAxRefl using (nelsonAxRefl)
open import Guard.GodelII using (treeEqSelf)

private
  tag17T : Term ; tag17T = reify (natCode n17)
  v0 : Term ; v0 = var zero

------------------------------------------------------------------------
-- Semantic soundness of axRefl: unconditional.

semSoundRefl : {hyp : Equation} ->
  Deriv hyp (eqn (ap1 evalCode (ap1 Fst (ap1 thFunTFor (ap2 Pair tag17T (ap2 Pair v0 O)))))
                  (ap1 evalCode (ap1 Snd (ap1 thFunTFor (ap2 Pair tag17T (ap2 Pair v0 O))))))
semSoundRefl =
  let enc = ap2 Pair tag17T (ap2 Pair v0 O)
      -- nelsonAxRefl: thFunTFor(enc) = Pair(v0, v0)
      nar = nelsonAxRefl
      -- Fst(thFunTFor(enc)) = v0
      fstR = ruleTrans (cong1 Fst nar) (axFst v0 v0)
      -- Snd(thFunTFor(enc)) = v0
      sndR = ruleTrans (cong1 Snd nar) (axSnd v0 v0)
      -- evalCode(Fst(...)) = evalCode(v0) = evalCode(Snd(...))
  in ruleTrans (cong1 evalCode fstR) (ruleSym (cong1 evalCode sndR))

------------------------------------------------------------------------
-- TreeEq corollary

semSoundReflTreeEq : {hyp : Equation} ->
  let enc = ap2 Pair tag17T (ap2 Pair v0 O)
  in Deriv hyp (eqn (ap2 TreeEq (ap1 evalCode (ap1 Fst (ap1 thFunTFor enc)))
                                 (ap1 evalCode (ap1 Snd (ap1 thFunTFor enc))))
                    O)
semSoundReflTreeEq =
  let enc = ap2 Pair tag17T (ap2 Pair v0 O)
  in ruleTrans (congL TreeEq (ap1 evalCode (ap1 Snd (ap1 thFunTFor enc))) semSoundRefl)
               (treeEqSelf (ap1 evalCode (ap1 Snd (ap1 thFunTFor enc))))
