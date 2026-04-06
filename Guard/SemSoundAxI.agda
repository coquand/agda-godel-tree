{-# OPTIONS --safe --without-K --exact-split #-}

-- SemSoundAxI.agda
-- Semantic soundness of axI (tag 0) at ground term code(O).
--
-- This is the non-trivial base case: L != R as trees, but
-- evalCode(L) = evalCode(R) = O.
--
-- thFunTFor(enc_axI(codeO)) = Pair(code(I(O)), code(O))
-- evalCode(code(I(O))) = O  [evalCode strips I]
-- evalCode(code(O)) = O     [direct]
--
-- So the coded equation I(O)=O is semantically true under evalCode.

module Guard.SemSoundAxI where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.ThFunTForDefs
open import Guard.ThFunTFor
open import Guard.EvalCode
open import Guard.EvalCodeCorrect using (evalCodeO ; evalCodeIO)
open import Guard.NelsonDispatch
open import Guard.NelsonAxI
open import Guard.GodelII using (treeEqSelf)

private
  tag0T : Term ; tag0T = reify (natCode n0)
  codeOT : Term ; codeOT = ap2 Pair O O
  codeIT : Term ; codeIT = reify (codeF1 I)
  codeIOT : Term ; codeIOT = ap2 Pair (reify tagAp1) (ap2 Pair codeIT codeOT)

------------------------------------------------------------------------
-- Semantic soundness of axI at code(O).

semSoundAxI : {hyp : Equation} ->
  let enc = ap2 Pair tag0T (ap2 Pair codeOT O)
  in Deriv hyp (eqn (ap1 evalCode (ap1 Fst (ap1 thFunTFor enc)))
                     (ap1 evalCode (ap1 Snd (ap1 thFunTFor enc))))
semSoundAxI =
  let enc = ap2 Pair tag0T (ap2 Pair codeOT O)
      -- nelsonAxI codeOT: thFunTFor(enc) = Pair(codeIOT, codeOT)
      nai = nelsonAxI codeOT

      -- Fst(thFunTFor(enc)) = codeIOT
      fstR = ruleTrans (cong1 Fst nai) (axFst codeIOT codeOT)
      -- Snd(thFunTFor(enc)) = codeOT
      sndR = ruleTrans (cong1 Snd nai) (axSnd codeIOT codeOT)

      -- evalCode(Fst(thFunTFor(enc))) = evalCode(codeIOT) = O
      evalL = ruleTrans (cong1 evalCode fstR) evalCodeIO
      -- evalCode(Snd(thFunTFor(enc))) = evalCode(codeOT) = O
      evalR = ruleTrans (cong1 evalCode sndR) evalCodeO
  in ruleTrans evalL (ruleSym evalR)

------------------------------------------------------------------------
-- TreeEq corollary

semSoundAxITreeEq : {hyp : Equation} ->
  let enc = ap2 Pair tag0T (ap2 Pair codeOT O)
  in Deriv hyp (eqn (ap2 TreeEq (ap1 evalCode (ap1 Fst (ap1 thFunTFor enc)))
                                 (ap1 evalCode (ap1 Snd (ap1 thFunTFor enc))))
                    O)
semSoundAxITreeEq =
  let enc = ap2 Pair tag0T (ap2 Pair codeOT O)
  in ruleTrans (congL TreeEq (ap1 evalCode (ap1 Snd (ap1 thFunTFor enc))) semSoundAxI)
               (treeEqSelf (ap1 evalCode (ap1 Snd (ap1 thFunTFor enc))))
