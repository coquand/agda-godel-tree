{-# OPTIONS --safe --without-K --exact-split #-}

-- NelsonCongR.agda
-- Nelson case proof for congR (tag 22).
--
-- Encoding: Pair(tag22T, Pair(Pair(gCode, xCode), sp))
-- case22 = mkEqF (mkAp2F origAL origAR recsBL) (mkAp2F origAL origAR recsBR)
-- Result: Pair(mkAp2(gCode, xCode, L), mkAp2(gCode, xCode, R))

module Guard.Nelson.NelsonCongR where

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
  tag22T : Term ; tag22T = reify (natCode n22)

nelsonCongR :
  (g1 g2 g3 xCode s1 s2 : Term) -> {hyp : Equation} ->
  let gCode = ap2 Pair (ap2 Pair g1 g2) g3
      sp = ap2 Pair s1 s2
      fstSp = ap1 Fst (ap1 thFunTFor sp)
      sndSp = ap1 Snd (ap1 thFunTFor sp)
  in Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair tag22T (ap2 Pair (ap2 Pair gCode xCode) sp)))
                    (ap2 Pair (ap2 Pair (reify tagAp2) (ap2 Pair gCode (ap2 Pair xCode fstSp)))
                              (ap2 Pair (reify tagAp2) (ap2 Pair gCode (ap2 Pair xCode sndSp)))))
nelsonCongR g1 g2 g3 xCode s1 s2 =
  let gCode = ap2 Pair (ap2 Pair g1 g2) g3
      sp = ap2 Pair s1 s2
      origT = ap2 Pair tag22T (ap2 Pair (ap2 Pair gCode xCode) sp)
      recsT = ap2 Pair (ap1 thFunTFor tag22T) (ap1 thFunTFor (ap2 Pair (ap2 Pair gCode xCode) sp))
      fstSp = ap1 Fst (ap1 thFunTFor sp)
      sndSp = ap1 Snd (ap1 thFunTFor sp)

      step12 = ruleTrans (phase1Nd tag22T (ap2 Pair gCode xCode) sp)
                         (ndDispatchToCase22 (ap2 Pair (ap2 Pair gCode xCode) sp) recsT)

      oaL = origALRed tag22T gCode xCode (ap2 Pair s1 s2) recsT
      oaR = origARRed tag22T gCode xCode (ap2 Pair s1 s2) recsT

      ppA1 = ap2 Pair g1 g2
      ppA2 = g3
      ppB = xCode

      rbL = recsBLWithPassthrough tag22T ppA1 ppA2 ppB s1 s2
      rbR = recsBRWithPassthrough tag22T ppA1 ppA2 ppB s1 s2

      -- case22 = mkEqF (mkAp2F origAL origAR recsBL) (mkAp2F origAL origAR recsBR)
      -- Note: origAR and recsBL/recsBR swap positions vs congL
      leftRed = mkAp2FRed origAL origAR recsBL origT recsT gCode xCode fstSp oaL oaR rbL
      rightRed = mkAp2FRed origAL origAR recsBR origT recsT gCode xCode sndSp oaL oaR rbR
      step4 = mkEqFRed (mkAp2F origAL origAR recsBL) (mkAp2F origAL origAR recsBR)
                origT recsT
                (ap2 Pair (reify tagAp2) (ap2 Pair gCode (ap2 Pair xCode fstSp)))
                (ap2 Pair (reify tagAp2) (ap2 Pair gCode (ap2 Pair xCode sndSp)))
                leftRed rightRed
  in
  ruleTrans step12 step4
