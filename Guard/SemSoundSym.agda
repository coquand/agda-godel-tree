{-# OPTIONS --safe --without-K --exact-split #-}

-- SemSoundSym.agda
-- Semantic soundness of ruleSym for locally valid encodings.
--
-- Given:
--   IH: evalCode(Fst(thFunTFor(sp))) = evalCode(Snd(thFunTFor(sp)))
--       (sub-proof is semantically true)
--
-- Then:
--   evalCode(Fst(thFunTFor(enc))) = evalCode(Snd(thFunTFor(enc)))
--   where enc is the ruleSym encoding.
--
-- ruleSym has NO side condition — semantic truth is preserved
-- unconditionally (just swap L and R).
--
-- enc = Pair(tag18T, Pair(tagVarT, sp))
-- nelsonRuleSym: thFunTFor(enc) = Pair(Snd(thFunTFor(sp)), Fst(thFunTFor(sp)))
-- So Fst(thFunTFor(enc)) = Snd(thFunTFor(sp))
--    Snd(thFunTFor(enc)) = Fst(thFunTFor(sp))
-- Then evalCode(Snd(thFunTFor(sp))) = evalCode(Fst(thFunTFor(sp))) by ruleSym of IH.

module Guard.SemSoundSym where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.ThFunTForDefs
open import Guard.ThFunTFor
open import Guard.EvalCode
open import Guard.NelsonDispatch
open import Guard.NelsonRuleSym using (nelsonRuleSym)
open import Guard.GodelII using (treeEqSelf)

private
  tag18T : Term ; tag18T = reify (natCode n18)
  tagVarT : Term ; tagVarT = ap2 Pair (ap2 Pair (ap2 Pair O O) O) O

------------------------------------------------------------------------
-- Semantic soundness of ruleSym.
-- No side condition needed — just symmetry of IH.

semSoundSym :
  (s1 s2 : Term) -> {hyp : Equation} ->
  let sp = ap2 Pair s1 s2
      enc = ap2 Pair tag18T (ap2 Pair tagVarT sp)
  in
  -- IH: sub-proof is semantically true
  Deriv hyp (eqn (ap1 evalCode (ap1 Fst (ap1 thFunTFor sp)))
                  (ap1 evalCode (ap1 Snd (ap1 thFunTFor sp)))) ->
  -- Conclusion: symmetric proof is semantically true
  Deriv hyp (eqn (ap1 evalCode (ap1 Fst (ap1 thFunTFor enc)))
                  (ap1 evalCode (ap1 Snd (ap1 thFunTFor enc))))
semSoundSym s1 s2 ih =
  let sp = ap2 Pair s1 s2
      enc = ap2 Pair tag18T (ap2 Pair tagVarT sp)
      sndSp = ap1 Snd (ap1 thFunTFor sp)
      fstSp = ap1 Fst (ap1 thFunTFor sp)

      -- nelsonRuleSym: thFunTFor(enc) = Pair(sndSp, fstSp)
      nrs = nelsonRuleSym s1 s2

      -- Fst(thFunTFor(enc)) = sndSp
      fstEnc = ruleTrans (cong1 Fst nrs) (axFst sndSp fstSp)

      -- Snd(thFunTFor(enc)) = fstSp
      sndEnc = ruleTrans (cong1 Snd nrs) (axSnd sndSp fstSp)

      -- evalCode(Fst(enc)) = evalCode(sndSp)
      evalFst = cong1 evalCode fstEnc

      -- evalCode(Snd(enc)) = evalCode(fstSp)
      evalSnd = cong1 evalCode sndEnc

      -- Chain: evalCode(sndSp) = evalCode(fstSp) by ruleSym of IH
  in ruleTrans evalFst (ruleTrans (ruleSym ih) (ruleSym evalSnd))

------------------------------------------------------------------------
-- TreeEq corollary

semSoundSymTreeEq :
  (s1 s2 : Term) -> {hyp : Equation} ->
  let sp = ap2 Pair s1 s2
      enc = ap2 Pair tag18T (ap2 Pair tagVarT sp)
  in
  Deriv hyp (eqn (ap1 evalCode (ap1 Fst (ap1 thFunTFor sp)))
                  (ap1 evalCode (ap1 Snd (ap1 thFunTFor sp)))) ->
  Deriv hyp (eqn (ap2 TreeEq (ap1 evalCode (ap1 Fst (ap1 thFunTFor enc)))
                              (ap1 evalCode (ap1 Snd (ap1 thFunTFor enc))))
                 O)
semSoundSymTreeEq s1 s2 ih =
  let enc = ap2 Pair tag18T (ap2 Pair tagVarT (ap2 Pair s1 s2))
      eqPf = semSoundSym s1 s2 ih
  in ruleTrans (congL TreeEq (ap1 evalCode (ap1 Snd (ap1 thFunTFor enc))) eqPf)
               (treeEqSelf (ap1 evalCode (ap1 Snd (ap1 thFunTFor enc))))
