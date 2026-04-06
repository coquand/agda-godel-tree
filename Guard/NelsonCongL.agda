{-# OPTIONS --safe --without-K --exact-split #-}

-- NelsonCongL.agda
-- Nelson case proof for congL (tag 21).
--
-- Encoding: Pair(tag21T, Pair(Pair(gCode, xCode), sp))
-- case21 = mkEqF (mkAp2F origAL recsBL origAR) (mkAp2F origAL recsBR origAR)
-- Result: Pair(mkAp2(gCode, L, xCode), mkAp2(gCode, R, xCode))
--
-- gCode must be Pair-Pair-tagged for inner passthrough.

module Guard.NelsonCongL where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.ThFunTForDefs
open import Guard.ThFunTForCases3
open import Guard.ThFunTFor
open import Guard.NelsonDispatch
open import Guard.NelsonExtractors

private
  tag21T : Term ; tag21T = reify (natCode n21)

nelsonCongL :
  (g1 g2 g3 xCode s1 s2 : Term) -> {hyp : Equation} ->
  let gCode = ap2 Pair (ap2 Pair g1 g2) g3
      sp = ap2 Pair s1 s2
      fstSp = ap1 Fst (ap1 thFunTFor sp)
      sndSp = ap1 Snd (ap1 thFunTFor sp)
  in Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair tag21T (ap2 Pair (ap2 Pair gCode xCode) sp)))
                    (ap2 Pair (ap2 Pair (reify tagAp2) (ap2 Pair gCode (ap2 Pair fstSp xCode)))
                              (ap2 Pair (reify tagAp2) (ap2 Pair gCode (ap2 Pair sndSp xCode)))))
nelsonCongL g1 g2 g3 xCode s1 s2 =
  let gCode = ap2 Pair (ap2 Pair g1 g2) g3
      sp = ap2 Pair s1 s2
      origT = ap2 Pair tag21T (ap2 Pair (ap2 Pair gCode xCode) sp)
      recsT = ap2 Pair (ap1 thFunTFor tag21T) (ap1 thFunTFor (ap2 Pair (ap2 Pair gCode xCode) sp))
      fstSp = ap1 Fst (ap1 thFunTFor sp)
      sndSp = ap1 Snd (ap1 thFunTFor sp)

      -- Phase 1+2
      step12 = ruleTrans (phase1Nd tag21T (ap2 Pair gCode xCode) sp)
                         (ndDispatchToCase21 (ap2 Pair (ap2 Pair gCode xCode) sp) recsT)

      -- origAL(origT, recsT) = Fst(origA) = Fst(Pair(gCode, xCode)) = gCode
      oaL = origALRed tag21T gCode xCode (ap2 Pair s1 s2) recsT
      -- origAR(origT, recsT) = Snd(origA) = Snd(Pair(gCode, xCode)) = xCode
      oaR = origARRed tag21T gCode xCode (ap2 Pair s1 s2) recsT

      -- Passthrough decomposition:
      -- Pair(gCode, xCode) = Pair(Pair(Pair(g1,g2),g3), xCode)
      -- Pair-Pair: a1=Pair(g1,g2), a2=g3, b=xCode
      ppA1 = ap2 Pair g1 g2
      ppA2 = g3
      ppB = xCode

      rbL = recsBLWithPassthrough tag21T ppA1 ppA2 ppB s1 s2
      rbR = recsBRWithPassthrough tag21T ppA1 ppA2 ppB s1 s2

      -- case21 reduction
      leftRed = mkAp2FRed origAL recsBL origAR origT recsT gCode fstSp xCode oaL rbL oaR
      rightRed = mkAp2FRed origAL recsBR origAR origT recsT gCode sndSp xCode oaL rbR oaR
      step4 = mkEqFRed (mkAp2F origAL recsBL origAR) (mkAp2F origAL recsBR origAR)
                origT recsT
                (ap2 Pair (reify tagAp2) (ap2 Pair gCode (ap2 Pair fstSp xCode)))
                (ap2 Pair (reify tagAp2) (ap2 Pair gCode (ap2 Pair sndSp xCode)))
                leftRed rightRed
  in
  ruleTrans step12 step4
