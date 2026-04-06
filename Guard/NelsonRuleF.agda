{-# OPTIONS --safe --without-K --exact-split #-}

-- Nelson Experiment D: the system verifies its own Schema F case.
--
-- case24 (ruleF) constructs Pair(ap1(f, var0Code), ap1(g, var0Code))
-- from the functor codes f and g. This is the equation f(x) = g(x)
-- that Schema F establishes for all x.
--
-- Like axRefl, this case ignores recursive results — it only uses
-- origAL (fCode) and origAR (gCode) from the encoding.

module Guard.NelsonRuleF where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.ThFunTForDefs
open import Guard.ThFunTForCases0
open import Guard.ThFunTForCases1
open import Guard.ThFunTForCases2
open import Guard.ThFunTForCases3
open import Guard.ThFunTFor
open import Guard.ThFunTForCorrectDefs hiding (natCodeNeq)
open import Guard.GodelII using (treeEqSelf)
open import Guard.NelsonAxRefl using (natCodeNeq ; natAdd)

private
  poo : Term ; poo = ap2 Pair O O
  n0  : Nat ; n0  = zero
  n1  : Nat ; n1  = suc n0
  n2  : Nat ; n2  = suc n1
  n3  : Nat ; n3  = suc n2
  n4  : Nat ; n4  = suc n3
  n5  : Nat ; n5  = suc n4
  n6  : Nat ; n6  = suc n5
  n7  : Nat ; n7  = suc n6
  n8  : Nat ; n8  = suc n7
  n9  : Nat ; n9  = suc n8
  n10 : Nat ; n10 = suc n9
  n11 : Nat ; n11 = suc n10
  n12 : Nat ; n12 = suc n11
  n13 : Nat ; n13 = suc n12
  n14 : Nat ; n14 = suc n13
  n15 : Nat ; n15 = suc n14
  n16 : Nat ; n16 = suc n15
  n17 : Nat ; n17 = suc n16
  n18 : Nat ; n18 = suc n17
  n19 : Nat ; n19 = suc n18
  n20 : Nat ; n20 = suc n19
  n21 : Nat ; n21 = suc n20
  n22 : Nat ; n22 = suc n21
  n23 : Nat ; n23 = suc n22
  n24 : Nat ; n24 = suc n23

  tag24T : Term ; tag24T = reify (natCode n24)
  tagAp1T : Term ; tagAp1T = reify tagAp1
  var0CodeT : Term ; var0CodeT = reify (nd (nd (nd (nd lf lf) lf) lf) lf)

------------------------------------------------------------------------
-- Encoding: Pair(tag24, Pair(Pair(fC, gC), data))
-- where fC, gC are functor codes, data is the rest of the encoding.
-- case24 only uses fC and gC.

nelsonRuleF :
  (fC gC dataT : Term) -> {hyp : Equation} ->
  let ax = ap2 Pair fC gC
  in Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair tag24T (ap2 Pair ax dataT)))
                    (ap2 Pair (ap2 Pair tagAp1T (ap2 Pair fC var0CodeT))
                              (ap2 Pair tagAp1T (ap2 Pair gC var0CodeT))))
nelsonRuleF fC gC dataT =
  let ax = ap2 Pair fC gC
      origT = ap2 Pair tag24T (ap2 Pair ax dataT)
      recsT = ap2 Pair (ap1 thFunTFor tag24T) (ap1 thFunTFor (ap2 Pair ax dataT))
  in

  -- Phase 1: RecNd + guardNd
  let step1 = axRecNd O thFunStep tag24T (ap2 Pair ax dataT)
      step2 = guardNd tag24T ax dataT recsT
  in

  -- Phase 2: ndDispatch falls through 24 branches, hits case24
  let tCR : (k : Nat) -> {h : Equation} -> Deriv h (eqn (ap2 (tagCheck k) origT recsT) (ap2 TreeEq tag24T (reify (natCode k))))
      tCR k = tagCheckRed k tag24T (ap2 Pair ax dataT) recsT
      tN : (k : Nat) -> {h : Equation} -> Deriv h (eqn (ap2 TreeEq tag24T (reify (natCode k))) poo) -> Deriv h (eqn (ap2 (tagCheck k) origT recsT) poo)
      tN k cmp = ruleTrans (tCR k) cmp
      bM : (k : Nat) (c t : Fun2) -> {h : Equation} -> Deriv h (eqn (ap2 (tagCheck k) origT recsT) poo) -> Deriv h (eqn (ap2 (branch (tagCheck k) c t) origT recsT) (ap2 t origT recsT))
      bM k c t chk = branchMiss (tagCheck k) c t origT recsT chk
      h24 : {h : Equation} -> Deriv h (eqn (ap2 ndT24 origT recsT) (ap2 case24 origT recsT))
      h24 = branchHit (tagCheck n24) case24 ndT25 origT recsT
              (ruleTrans (tCR n24) (treeEqSelf tag24T))
      step3 : {h : Equation} -> Deriv h (eqn (ap2 ndDispatch origT recsT) (ap2 case24 origT recsT))
      step3 =
       ruleTrans (bM n0  case0  ndT1  (tN n0  (natCodeNeq n23 n0)))
       (ruleTrans (bM n1  case1  ndT2  (tN n1  (natCodeNeq n22 n1)))
       (ruleTrans (bM n2  case2  ndT3  (tN n2  (natCodeNeq n21 n2)))
       (ruleTrans (bM n3  case3  ndT4  (tN n3  (natCodeNeq n20 n3)))
       (ruleTrans (bM n4  case4  ndT5  (tN n4  (natCodeNeq n19 n4)))
       (ruleTrans (bM n5  case5  ndT6  (tN n5  (natCodeNeq n18 n5)))
       (ruleTrans (bM n6  case6  ndT7  (tN n6  (natCodeNeq n17 n6)))
       (ruleTrans (bM n7  case7  ndT8  (tN n7  (natCodeNeq n16 n7)))
       (ruleTrans (bM n8  case8  ndT9  (tN n8  (natCodeNeq n15 n8)))
       (ruleTrans (bM n9  case9  ndT10 (tN n9  (natCodeNeq n14 n9)))
       (ruleTrans (bM n10 case10 ndT11 (tN n10 (natCodeNeq n13 n10)))
       (ruleTrans (bM n11 case11 ndT12 (tN n11 (natCodeNeq n12 n11)))
       (ruleTrans (bM n12 case12 ndT13 (tN n12 (natCodeNeq n11 n12)))
       (ruleTrans (bM n13 case13 ndT14 (tN n13 (natCodeNeq n10 n13)))
       (ruleTrans (bM n14 case14 ndT15 (tN n14 (natCodeNeq n9  n14)))
       (ruleTrans (bM n15 case15 ndT16 (tN n15 (natCodeNeq n8  n15)))
       (ruleTrans (bM n16 case16 ndT17 (tN n16 (natCodeNeq n7  n16)))
       (ruleTrans (bM n17 case17 ndT18 (tN n17 (natCodeNeq n6  n17)))
       (ruleTrans (bM n18 case18 ndT19 (tN n18 (natCodeNeq n5  n18)))
       (ruleTrans (bM n19 case19 ndT20 (tN n19 (natCodeNeq n4  n19)))
       (ruleTrans (bM n20 case20 ndT21 (tN n20 (natCodeNeq n3  n20)))
       (ruleTrans (bM n21 case21 ndT22 (tN n21 (natCodeNeq n2  n21)))
       (ruleTrans (bM n22 case22 ndT23 (tN n22 (natCodeNeq n1  n22)))
       (ruleTrans (bM n23 case23 ndT24 (tN n23 (natCodeNeq n0  n23)))
                  h24)))))))))))))))))))))))
  in

  -- Phase 3: case24 reduction
  -- case24 = mkEqF (mkAp1F origAL (kF2 var0CodeT)) (mkAp1F origAR (kF2 var0CodeT))
  --        = Fan leftF rightF Pair
  -- where leftF = mkAp1F origAL (kF2 var0CodeT)
  --             = Fan (kF2 tagAp1T) (Fan origAL (kF2 var0CodeT) Pair) Pair
  -- Reduces to: Pair(tagAp1T, Pair(origAL(...), var0CodeT))
  --           = Pair(tagAp1T, Pair(fC, var0CodeT))

  let leftF  = mkAp1F origAL (kF2 var0CodeT)
      rightF = mkAp1F origAR (kF2 var0CodeT)

      -- origA(origT, recsT) = Fst(Snd(origT)) = Fst(Pair(ax, dataT)) = ax = Pair(fC, gC)
      origARed : {h : Equation} -> Deriv h (eqn (ap2 origA origT recsT) ax)
      origARed = ruleTrans (axLift (Comp Fst Snd) origT recsT)
                 (ruleTrans (axComp Fst Snd origT)
                 (ruleTrans (cong1 Fst (axSnd tag24T (ap2 Pair ax dataT)))
                            (axFst ax dataT)))

      -- origAL = Fst(origA) = Fst(Pair(fC, gC)) = fC
      origALRed : {h : Equation} -> Deriv h (eqn (ap2 origAL origT recsT) fC)
      origALRed = ruleTrans (axPost Fst origA origT recsT)
                  (ruleTrans (cong1 Fst origARed) (axFst fC gC))

      -- origAR = Snd(origA) = gC
      origARRed : {h : Equation} -> Deriv h (eqn (ap2 origAR origT recsT) gC)
      origARRed = ruleTrans (axPost Snd origA origT recsT)
                  (ruleTrans (cong1 Snd origARed) (axSnd fC gC))

      -- kF2 var0CodeT (origT, recsT) = var0CodeT
      kVRed : {h : Equation} -> Deriv h (eqn (ap2 (kF2 var0CodeT) origT recsT) var0CodeT)
      kVRed = constF2Red var0CodeT origT recsT

      -- kF2 tagAp1T (origT, recsT) = tagAp1T
      kTRed : {h : Equation} -> Deriv h (eqn (ap2 (kF2 tagAp1T) origT recsT) tagAp1T)
      kTRed = constF2Red tagAp1T origT recsT

      -- mkAp1F origAL (kF2 var0CodeT) (origT, recsT)
      -- = Pair(tagAp1T, Pair(fC, var0CodeT))
      leftRed : {h : Equation} -> Deriv h (eqn (ap2 leftF origT recsT)
                                               (ap2 Pair tagAp1T (ap2 Pair fC var0CodeT)))
      leftRed = ruleTrans (axFan (kF2 tagAp1T) (Fan origAL (kF2 var0CodeT) Pair) Pair origT recsT)
                (ruleTrans (congL Pair (ap2 (Fan origAL (kF2 var0CodeT) Pair) origT recsT) kTRed)
                (congR Pair tagAp1T
                  (ruleTrans (axFan origAL (kF2 var0CodeT) Pair origT recsT)
                  (ruleTrans (congL Pair (ap2 (kF2 var0CodeT) origT recsT) origALRed)
                             (congR Pair fC kVRed)))))

      -- mkAp1F origAR (kF2 var0CodeT) similarly
      rightRed : {h : Equation} -> Deriv h (eqn (ap2 rightF origT recsT)
                                                (ap2 Pair tagAp1T (ap2 Pair gC var0CodeT)))
      rightRed = ruleTrans (axFan (kF2 tagAp1T) (Fan origAR (kF2 var0CodeT) Pair) Pair origT recsT)
                 (ruleTrans (congL Pair (ap2 (Fan origAR (kF2 var0CodeT) Pair) origT recsT) kTRed)
                 (congR Pair tagAp1T
                   (ruleTrans (axFan origAR (kF2 var0CodeT) Pair origT recsT)
                   (ruleTrans (congL Pair (ap2 (kF2 var0CodeT) origT recsT) origARRed)
                              (congR Pair gC kVRed)))))

      -- case24 = Fan leftF rightF Pair
      step4 : {h : Equation} -> Deriv h (eqn (ap2 case24 origT recsT)
                (ap2 Pair (ap2 Pair tagAp1T (ap2 Pair fC var0CodeT))
                          (ap2 Pair tagAp1T (ap2 Pair gC var0CodeT))))
      step4 = ruleTrans (axFan leftF rightF Pair origT recsT)
              (ruleTrans (congL Pair (ap2 rightF origT recsT) leftRed)
                         (congR Pair (ap2 Pair tagAp1T (ap2 Pair fC var0CodeT)) rightRed))
  in

  -- Final chain
  ruleTrans step1 (ruleTrans step2 (ruleTrans step3 step4))
