{-# OPTIONS --safe --without-K --exact-split #-}

-- NelsonCong1.agda
-- Nelson case proof for cong1 (tag 20).
--
-- Encoding: encCong1 f sp = nd(natCode 20, nd(fCode, sp))
--         = Pair(tag20T, Pair(fCode, sp))
--
-- case20 = mkEqF (mkAp1F origA recsBL) (mkAp1F origA recsBR)
--
-- Result: thFunTFor(enc) = Pair(mkAp1(fCode, L), mkAp1(fCode, R))
-- where L = Fst(thFunTFor(sp)), R = Snd(thFunTFor(sp)).
--
-- Requirement: fCode must be Pair-Pair-tagged so that the inner
-- passthrough (ndDispatchPairMiss) applies.

module Guard.Nelson.NelsonCong1 where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.ThFunTForDefs
open import Guard.ThFunTForCases3
open import Guard.ThFunTFor
open import Guard.Nelson.NelsonDispatch
open import Guard.Nelson.NelsonExtractors

private
  tag20T : Term ; tag20T = reify (natCode n20)

------------------------------------------------------------------------
-- nelsonCong1:
-- Given fCode = Pair(Pair(f1,f2), f3) (Pair-Pair-tagged) and
-- sp = Pair(s1, s2):
--
-- thFunTFor(Pair(tag20T, Pair(fCode, sp)))
--   = Pair( Pair(reify tagAp1, Pair(fCode, Fst(thFunTFor(sp))))
--         , Pair(reify tagAp1, Pair(fCode, Snd(thFunTFor(sp)))) )

nelsonCong1 :
  (f1 f2 f3 s1 s2 : Term) -> {hyp : Equation} ->
  let fCode = ap2 Pair (ap2 Pair f1 f2) f3
      sp = ap2 Pair s1 s2
      fstSp = ap1 Fst (ap1 thFunTFor sp)
      sndSp = ap1 Snd (ap1 thFunTFor sp)
  in Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair tag20T (ap2 Pair fCode sp)))
                    (ap2 Pair (ap2 Pair (reify tagAp1) (ap2 Pair fCode fstSp))
                              (ap2 Pair (reify tagAp1) (ap2 Pair fCode sndSp))))
nelsonCong1 f1 f2 f3 s1 s2 =
  let fCode = ap2 Pair (ap2 Pair f1 f2) f3
      sp = ap2 Pair s1 s2
      origT = ap2 Pair tag20T (ap2 Pair fCode sp)
      recsT = ap2 Pair (ap1 thFunTFor tag20T) (ap1 thFunTFor (ap2 Pair fCode sp))
      fstSp = ap1 Fst (ap1 thFunTFor sp)
      sndSp = ap1 Snd (ap1 thFunTFor sp)

      -- Phase 1+2: thFunTFor(origT) = case20(origT, recsT)
      step12 = ruleTrans (phase1Nd tag20T fCode sp)
                         (ndDispatchToCase20 (ap2 Pair fCode sp) recsT)

      -- Phase 3: extract components via passthrough
      -- origA = fCode
      oA = origARed tag20T fCode sp recsT
      -- recsBL = Fst(thFunTFor(sp))
      rbL = recsBLWithPassthrough tag20T f1 f2 f3 s1 s2
      -- recsBR = Snd(thFunTFor(sp))
      rbR = recsBRWithPassthrough tag20T f1 f2 f3 s1 s2

      -- Phase 4: case20 = mkEqF (mkAp1F origA recsBL) (mkAp1F origA recsBR)
      -- Left side: mkAp1F origA recsBL -> Pair(reify tagAp1, Pair(fCode, fstSp))
      leftRed = mkAp1FRed origA recsBL origT recsT fCode fstSp oA rbL
      -- Right side: mkAp1F origA recsBR -> Pair(reify tagAp1, Pair(fCode, sndSp))
      rightRed = mkAp1FRed origA recsBR origT recsT fCode sndSp oA rbR
      -- Combine: mkEqF gives Pair(left, right)
      step4 = mkEqFRed (mkAp1F origA recsBL) (mkAp1F origA recsBR)
                origT recsT
                (ap2 Pair (reify tagAp1) (ap2 Pair fCode fstSp))
                (ap2 Pair (reify tagAp1) (ap2 Pair fCode sndSp))
                leftRed rightRed
  in
  ruleTrans step12 step4
