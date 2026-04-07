{-# OPTIONS --safe --without-K --exact-split #-}

module Guard.Nelson.NelsonRuleTransFull where

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
open import Guard.PairPassthroughAll
open import Guard.GodelII using (treeEqSelf)
open import Guard.Nelson.NelsonAxRefl using (natCodeNeq ; natAdd)

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
  tag19T : Term ; tag19T = reify (natCode n19)

nelsonRuleTransFull :
  (a1 a2 b1 c1 c2 d1 : Term) -> {hyp : Equation} ->
  let sp1 = ap2 Pair (ap2 Pair a1 a2) b1
      sp2 = ap2 Pair (ap2 Pair c1 c2) d1
  in Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair tag19T (ap2 Pair sp1 sp2)))
                    (ap2 Pair (ap1 Fst (ap1 thFunTFor sp1))
                              (ap1 Snd (ap1 thFunTFor sp2))))
nelsonRuleTransFull a1 a2 b1 c1 c2 d1 =
  let sp1 = ap2 Pair (ap2 Pair a1 a2) b1
      sp2 = ap2 Pair (ap2 Pair c1 c2) d1
      origT = ap2 Pair tag19T (ap2 Pair sp1 sp2)
      recsSp = ap2 Pair (ap1 thFunTFor sp1) (ap1 thFunTFor sp2)
      innerRec = ap1 thFunTFor (ap2 Pair sp1 sp2)
      recsT = ap2 Pair (ap1 thFunTFor tag19T) innerRec
  in
  -- Phase 1: RecNd + guardNd
  let step1 = axRecNd O thFunStep tag19T (ap2 Pair sp1 sp2)
      step2 = guardNd tag19T sp1 sp2 recsT
  in
  -- Phase 2: ndDispatch falls through to case19
  let tCR : (k : Nat) -> {h : Equation} -> Deriv h (eqn (ap2 (tagCheck k) origT recsT) (ap2 TreeEq tag19T (reify (natCode k))))
      tCR k = tagCheckRed k tag19T (ap2 Pair sp1 sp2) recsT
      tN : (k : Nat) -> {h : Equation} -> Deriv h (eqn (ap2 TreeEq tag19T (reify (natCode k))) poo) -> Deriv h (eqn (ap2 (tagCheck k) origT recsT) poo)
      tN k cmp = ruleTrans (tCR k) cmp
      bM : (k : Nat) (c t : Fun2) -> {h : Equation} -> Deriv h (eqn (ap2 (tagCheck k) origT recsT) poo) -> Deriv h (eqn (ap2 (branch (tagCheck k) c t) origT recsT) (ap2 t origT recsT))
      bM k c t chk = branchMiss (tagCheck k) c t origT recsT chk
      h19 : {h : Equation} -> Deriv h (eqn (ap2 ndT19 origT recsT) (ap2 case19 origT recsT))
      h19 = branchHit (tagCheck n19) case19 ndT20 origT recsT
              (ruleTrans (tCR n19) (treeEqSelf tag19T))
      step3 : {h : Equation} -> Deriv h (eqn (ap2 ndDispatch origT recsT) (ap2 case19 origT recsT))
      step3 =
       ruleTrans (bM n0  case0  ndT1  (tN n0  (natCodeNeq n18 n0)))
       (ruleTrans (bM n1  case1  ndT2  (tN n1  (natCodeNeq n17 n1)))
       (ruleTrans (bM n2  case2  ndT3  (tN n2  (natCodeNeq n16 n2)))
       (ruleTrans (bM n3  case3  ndT4  (tN n3  (natCodeNeq n15 n3)))
       (ruleTrans (bM n4  case4  ndT5  (tN n4  (natCodeNeq n14 n4)))
       (ruleTrans (bM n5  case5  ndT6  (tN n5  (natCodeNeq n13 n5)))
       (ruleTrans (bM n6  case6  ndT7  (tN n6  (natCodeNeq n12 n6)))
       (ruleTrans (bM n7  case7  ndT8  (tN n7  (natCodeNeq n11 n7)))
       (ruleTrans (bM n8  case8  ndT9  (tN n8  (natCodeNeq n10 n8)))
       (ruleTrans (bM n9  case9  ndT10 (tN n9  (natCodeNeq n9  n9)))
       (ruleTrans (bM n10 case10 ndT11 (tN n10 (natCodeNeq n8  n10)))
       (ruleTrans (bM n11 case11 ndT12 (tN n11 (natCodeNeq n7  n11)))
       (ruleTrans (bM n12 case12 ndT13 (tN n12 (natCodeNeq n6  n12)))
       (ruleTrans (bM n13 case13 ndT14 (tN n13 (natCodeNeq n5  n13)))
       (ruleTrans (bM n14 case14 ndT15 (tN n14 (natCodeNeq n4  n14)))
       (ruleTrans (bM n15 case15 ndT16 (tN n15 (natCodeNeq n3  n15)))
       (ruleTrans (bM n16 case16 ndT17 (tN n16 (natCodeNeq n2  n16)))
       (ruleTrans (bM n17 case17 ndT18 (tN n17 (natCodeNeq n1  n17)))
       (ruleTrans (bM n18 case18 ndT19 (tN n18 (natCodeNeq n0  n18)))
                  h19))))))))))))))))))
  in
  -- Phase 3: Inner passthrough
  let passInner = ruleTrans (axRecNd O thFunStep sp1 sp2)
                  (ruleTrans (guardNd sp1 (ap2 Pair c1 c2) d1 recsSp)
                  (ruleTrans (ndDispatchPairMiss a1 a2 b1 sp2 recsSp)
                  (ruleTrans (axPost Snd Pair (ap2 Pair sp1 sp2) recsSp)
                             (axSnd (ap2 Pair sp1 sp2) recsSp))))
      -- passInner : innerRec = recsSp
  in
  -- Phase 4: case19 extractors → final result
  -- Reduce sndArg2/Post chain all the way through Snd(recsT) → innerRec → recsSp → Fst/Snd
  let snd2 = ruleTrans (axPost Snd Pair origT recsT) (axSnd origT recsT)
      -- snd2 : sndArg2(origT, recsT) = recsT
      ps = ruleTrans (axPost Snd sndArg2 origT recsT) (cong1 Snd snd2)
      -- ps : Post Snd sndArg2 (origT, recsT) = Snd(recsT)
      sndR = axSnd (ap1 thFunTFor tag19T) innerRec
      -- sndR : Snd(recsT) = innerRec
      full = ruleTrans ps (ruleTrans sndR passInner)
      -- full : Post Snd sndArg2 (origT, recsT) = recsSp = Pair(thFunTFor(sp1), thFunTFor(sp2))

      -- recsAL → Fst(thFunTFor(sp1))
      raL = ruleTrans (axPost Fst recsA origT recsT)
            (ruleTrans (cong1 Fst (ruleTrans (axPost Fst (Post Snd sndArg2) origT recsT) (cong1 Fst full)))
                       (cong1 Fst (axFst (ap1 thFunTFor sp1) (ap1 thFunTFor sp2))))
      -- recsBR → Snd(thFunTFor(sp2))
      rbR = ruleTrans (axPost Snd recsB origT recsT)
            (ruleTrans (cong1 Snd (ruleTrans (axPost Snd (Post Snd sndArg2) origT recsT) (cong1 Snd full)))
                       (cong1 Snd (axSnd (ap1 thFunTFor sp1) (ap1 thFunTFor sp2))))
      -- case19 → Pair(Fst(thFunTFor(sp1)), Snd(thFunTFor(sp2)))
      step4 = ruleTrans (axFan recsAL recsBR Pair origT recsT)
              (ruleTrans (congL Pair (ap2 recsBR origT recsT) raL)
                         (congR Pair (ap1 Fst (ap1 thFunTFor sp1)) rbR))
  in
  -- Final chain
  ruleTrans step1 (ruleTrans step2 (ruleTrans step3 step4))
