{-# OPTIONS --safe --without-K --exact-split #-}

-- SemSoundTrans.agda
-- Semantic soundness of ruleTrans for locally valid encodings.
--
-- Given:
--   IH1: evalCode(Fst(thFunTFor(sp1))) = evalCode(Snd(thFunTFor(sp1)))
--         (sub-proof 1 is semantically true)
--   IH2: evalCode(Fst(thFunTFor(sp2))) = evalCode(Snd(thFunTFor(sp2)))
--         (sub-proof 2 is semantically true)
--   match: Snd(thFunTFor(sp1)) = Fst(thFunTFor(sp2))
--         (middle terms match — the local validity condition)
--
-- Then:
--   evalCode(Fst(thFunTFor(enc))) = evalCode(Snd(thFunTFor(enc)))
--   where enc is the ruleTrans encoding of sp1, sp2.
--
-- This is the sharpest form of the result:
--   Semantic truth composes through ruleTrans
--   WHEN the validity side condition holds.
--
-- The side condition "match" is what distinguishes valid proof trees
-- from arbitrary trees. It cannot be proved for all trees by Schema F,
-- and this is exactly where Nelson meets Godel.

module Guard.Nelson.SemSoundTrans where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.ThFunTForDefs
open import Guard.ThFunTFor
open import Guard.Nelson.EvalCode
open import Guard.Nelson.NelsonDispatch
open import Guard.Nelson.NelsonExtractors
open import Guard.Nelson.NelsonRuleTransFull using (nelsonRuleTransFull)
open import Guard.GodelII using (treeEqSelf)

private
  tag19T : Term ; tag19T = reify (natCode n19)

------------------------------------------------------------------------
-- Semantic soundness of ruleTrans.

semSoundTrans :
  (a1 a2 b1 c1 c2 d1 : Term) -> {hyp : Equation} ->
  let sp1 = ap2 Pair (ap2 Pair a1 a2) b1
      sp2 = ap2 Pair (ap2 Pair c1 c2) d1
      enc = ap2 Pair tag19T (ap2 Pair sp1 sp2)
  in
  -- IH1: sub-proof 1 is semantically true
  Deriv hyp (eqn (ap1 evalCode (ap1 Fst (ap1 thFunTFor sp1)))
                  (ap1 evalCode (ap1 Snd (ap1 thFunTFor sp1)))) ->
  -- IH2: sub-proof 2 is semantically true
  Deriv hyp (eqn (ap1 evalCode (ap1 Fst (ap1 thFunTFor sp2)))
                  (ap1 evalCode (ap1 Snd (ap1 thFunTFor sp2)))) ->
  -- match: middle terms match (local validity condition)
  Deriv hyp (eqn (ap1 Snd (ap1 thFunTFor sp1))
                  (ap1 Fst (ap1 thFunTFor sp2))) ->
  -- Conclusion: combined proof is semantically true
  Deriv hyp (eqn (ap1 evalCode (ap1 Fst (ap1 thFunTFor enc)))
                  (ap1 evalCode (ap1 Snd (ap1 thFunTFor enc))))
semSoundTrans a1 a2 b1 c1 c2 d1 ih1 ih2 match =
  let sp1 = ap2 Pair (ap2 Pair a1 a2) b1
      sp2 = ap2 Pair (ap2 Pair c1 c2) d1
      enc = ap2 Pair tag19T (ap2 Pair sp1 sp2)

      -- nelsonRuleTransFull: thFunTFor(enc) = Pair(Fst(thFunTFor(sp1)), Snd(thFunTFor(sp2)))
      nrt = nelsonRuleTransFull a1 a2 b1 c1 c2 d1
      fstSp1 = ap1 Fst (ap1 thFunTFor sp1)
      sndSp2 = ap1 Snd (ap1 thFunTFor sp2)

      -- Fst(thFunTFor(enc)) = Fst(Pair(fstSp1, sndSp2)) = fstSp1
      fstEnc = ruleTrans (cong1 Fst nrt) (axFst fstSp1 sndSp2)

      -- Snd(thFunTFor(enc)) = Snd(Pair(fstSp1, sndSp2)) = sndSp2
      sndEnc = ruleTrans (cong1 Snd nrt) (axSnd fstSp1 sndSp2)

      -- evalCode(Fst(thFunTFor(enc))) = evalCode(fstSp1)
      evalFstEnc = cong1 evalCode fstEnc

      -- evalCode(Snd(thFunTFor(enc))) = evalCode(sndSp2)
      evalSndEnc = cong1 evalCode sndEnc

      -- Chain:
      -- evalCode(fstSp1) = evalCode(sndSp1)  [ih1]
      -- evalCode(sndSp1) = evalCode(fstSp2)  [cong1 evalCode match]
      -- evalCode(fstSp2) = evalCode(sndSp2)  [ih2]
      bridge = cong1 evalCode match
      chain = ruleTrans ih1 (ruleTrans bridge ih2)

      -- evalCode(Fst(thFunTFor(enc))) = evalCode(fstSp1) = ... = evalCode(sndSp2) = evalCode(Snd(thFunTFor(enc)))
  in ruleTrans evalFstEnc (ruleTrans chain (ruleSym evalSndEnc))

------------------------------------------------------------------------
-- Corollary: TreeEq version
-- Same as above but with TreeEq output instead of equational.

semSoundTransTreeEq :
  (a1 a2 b1 c1 c2 d1 : Term) -> {hyp : Equation} ->
  let sp1 = ap2 Pair (ap2 Pair a1 a2) b1
      sp2 = ap2 Pair (ap2 Pair c1 c2) d1
      enc = ap2 Pair tag19T (ap2 Pair sp1 sp2)
  in
  Deriv hyp (eqn (ap1 evalCode (ap1 Fst (ap1 thFunTFor sp1)))
                  (ap1 evalCode (ap1 Snd (ap1 thFunTFor sp1)))) ->
  Deriv hyp (eqn (ap1 evalCode (ap1 Fst (ap1 thFunTFor sp2)))
                  (ap1 evalCode (ap1 Snd (ap1 thFunTFor sp2)))) ->
  Deriv hyp (eqn (ap1 Snd (ap1 thFunTFor sp1))
                  (ap1 Fst (ap1 thFunTFor sp2))) ->
  Deriv hyp (eqn (ap2 TreeEq (ap1 evalCode (ap1 Fst (ap1 thFunTFor enc)))
                              (ap1 evalCode (ap1 Snd (ap1 thFunTFor enc))))
                 O)
semSoundTransTreeEq a1 a2 b1 c1 c2 d1 ih1 ih2 match =
  let enc = ap2 Pair tag19T (ap2 Pair (ap2 Pair (ap2 Pair a1 a2) b1) (ap2 Pair (ap2 Pair c1 c2) d1))
      eqPf = semSoundTrans a1 a2 b1 c1 c2 d1 ih1 ih2 match
  in ruleTrans (congL TreeEq (ap1 evalCode (ap1 Snd (ap1 thFunTFor enc))) eqPf)
               (treeEqSelf (ap1 evalCode (ap1 Snd (ap1 thFunTFor enc))))
