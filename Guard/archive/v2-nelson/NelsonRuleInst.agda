{-# OPTIONS --safe --without-K --exact-split #-}

-- Nelson Experiment C: the system verifies its own ruleInst case.
--
-- case23 applies substTFor to both sides of the sub-proof's equation.
-- This is the case where the self-referential substTFor enters the
-- proof checker — the key case for Nelson's program.

module Guard.Nelson.NelsonRuleInst where

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
open import Guard.SubstTFor using (substTFor)
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
  n20 : Nat ; n20 = suc n19
  n21 : Nat ; n21 = suc n20
  n22 : Nat ; n22 = suc n21
  n23 : Nat ; n23 = suc n22

  tag23T : Term ; tag23T = reify (natCode n23)

------------------------------------------------------------------------
-- For encoding ruleInst(tC, xC, sp):
-- Pair(tag23, Pair(Pair(tC, xC), sp))
--
-- tC = Pair(Pair(t1,t2), t3) — Pair-Pair-tagged (code t is always nd)
-- xC is arbitrary
-- sp = Pair(Pair(s1,s2), s3) — Pair-Pair-tagged (valid encoding)
--
-- Result: Pair(substTFor(Fst(thFunTFor(sp))), substTFor(Snd(thFunTFor(sp))))

nelsonRuleInst :
  (t1 t2 t3 xC s1 s2 s3 : Term) -> {hyp : Equation} ->
  let tC  = ap2 Pair (ap2 Pair t1 t2) t3
      sp  = ap2 Pair (ap2 Pair s1 s2) s3
      ax  = ap2 Pair tC xC
  in Deriv hyp (eqn (ap1 thFunTFor (ap2 Pair tag23T (ap2 Pair ax sp)))
                    (ap2 Pair (ap1 substTFor (ap1 Fst (ap1 thFunTFor sp)))
                              (ap1 substTFor (ap1 Snd (ap1 thFunTFor sp)))))
nelsonRuleInst t1 t2 t3 xC s1 s2 s3 =
  let tC  = ap2 Pair (ap2 Pair t1 t2) t3
      sp  = ap2 Pair (ap2 Pair s1 s2) s3
      ax  = ap2 Pair tC xC
      origT = ap2 Pair tag23T (ap2 Pair ax sp)
      innerRec = ap1 thFunTFor (ap2 Pair ax sp)
      recsSp = ap2 Pair (ap1 thFunTFor ax) (ap1 thFunTFor sp)
      recsT = ap2 Pair (ap1 thFunTFor tag23T) innerRec
  in

  -- Phase 1: RecNd + guardNd
  let step1 = axRecNd O thFunStep tag23T (ap2 Pair ax sp)
      step2 = guardNd tag23T ax sp recsT
  in

  -- Phase 2: ndDispatch falls through 23 branches, hits case23
  let tCR : (k : Nat) -> {h : Equation} -> Deriv h (eqn (ap2 (tagCheck k) origT recsT) (ap2 TreeEq tag23T (reify (natCode k))))
      tCR k = tagCheckRed k tag23T (ap2 Pair ax sp) recsT
      tN : (k : Nat) -> {h : Equation} -> Deriv h (eqn (ap2 TreeEq tag23T (reify (natCode k))) poo) -> Deriv h (eqn (ap2 (tagCheck k) origT recsT) poo)
      tN k cmp = ruleTrans (tCR k) cmp
      bM : (k : Nat) (c t : Fun2) -> {h : Equation} -> Deriv h (eqn (ap2 (tagCheck k) origT recsT) poo) -> Deriv h (eqn (ap2 (branch (tagCheck k) c t) origT recsT) (ap2 t origT recsT))
      bM k c t chk = branchMiss (tagCheck k) c t origT recsT chk
      h23 : {h : Equation} -> Deriv h (eqn (ap2 ndT23 origT recsT) (ap2 case23 origT recsT))
      h23 = branchHit (tagCheck n23) case23 ndT24 origT recsT
              (ruleTrans (tCR n23) (treeEqSelf tag23T))
      step3 : {h : Equation} -> Deriv h (eqn (ap2 ndDispatch origT recsT) (ap2 case23 origT recsT))
      step3 =
       ruleTrans (bM n0  case0  ndT1  (tN n0  (natCodeNeq n22 n0)))
       (ruleTrans (bM n1  case1  ndT2  (tN n1  (natCodeNeq n21 n1)))
       (ruleTrans (bM n2  case2  ndT3  (tN n2  (natCodeNeq n20 n2)))
       (ruleTrans (bM n3  case3  ndT4  (tN n3  (natCodeNeq n19 n3)))
       (ruleTrans (bM n4  case4  ndT5  (tN n4  (natCodeNeq n18 n4)))
       (ruleTrans (bM n5  case5  ndT6  (tN n5  (natCodeNeq n17 n5)))
       (ruleTrans (bM n6  case6  ndT7  (tN n6  (natCodeNeq n16 n6)))
       (ruleTrans (bM n7  case7  ndT8  (tN n7  (natCodeNeq n15 n7)))
       (ruleTrans (bM n8  case8  ndT9  (tN n8  (natCodeNeq n14 n8)))
       (ruleTrans (bM n9  case9  ndT10 (tN n9  (natCodeNeq n13 n9)))
       (ruleTrans (bM n10 case10 ndT11 (tN n10 (natCodeNeq n12 n10)))
       (ruleTrans (bM n11 case11 ndT12 (tN n11 (natCodeNeq n11 n11)))
       (ruleTrans (bM n12 case12 ndT13 (tN n12 (natCodeNeq n10 n12)))
       (ruleTrans (bM n13 case13 ndT14 (tN n13 (natCodeNeq n9  n13)))
       (ruleTrans (bM n14 case14 ndT15 (tN n14 (natCodeNeq n8  n14)))
       (ruleTrans (bM n15 case15 ndT16 (tN n15 (natCodeNeq n7  n15)))
       (ruleTrans (bM n16 case16 ndT17 (tN n16 (natCodeNeq n6  n16)))
       (ruleTrans (bM n17 case17 ndT18 (tN n17 (natCodeNeq n5  n17)))
       (ruleTrans (bM n18 case18 ndT19 (tN n18 (natCodeNeq n4  n18)))
       (ruleTrans (bM n19 case19 ndT20 (tN n19 (natCodeNeq n3  n19)))
       (ruleTrans (bM n20 case20 ndT21 (tN n20 (natCodeNeq n2  n20)))
       (ruleTrans (bM n21 case21 ndT22 (tN n21 (natCodeNeq n1  n21)))
       (ruleTrans (bM n22 case22 ndT23 (tN n22 (natCodeNeq n0  n22)))
                  h23))))))))))))))))))))))
  in

  -- Phase 3: Inner passthrough
  -- thFunTFor(Pair(ax, sp)) where ax = Pair(Pair(t1,t2),t3)·xC... wait.
  -- ax = Pair(tC, xC) where tC = Pair(Pair(t1,t2), t3).
  -- So Pair(ax, sp) = Pair(Pair(tC, xC), sp).
  -- Left child = ax = Pair(tC, xC). Fst(ax) = tC = Pair(Pair(t1,t2), t3).
  -- For ndDispatchPairMiss on Pair(ax, sp): need ax = Pair(Pair(a1,a2), b).
  -- ax = Pair(tC, xC) = Pair(Pair(Pair(t1,t2), t3), xC).
  -- So a1 = Pair(t1,t2), a2 = t3, b = xC. ✓ (Pair-Pair-tagged)
  let passInner = ruleTrans (axRecNd O thFunStep ax sp)
                  (ruleTrans (guardNd ax (ap2 Pair s1 s2) s3 recsSp)
                  (ruleTrans (ndDispatchPairMiss (ap2 Pair t1 t2) t3 xC sp recsSp)
                  (ruleTrans (axPost Snd Pair (ap2 Pair ax sp) recsSp)
                             (axSnd (ap2 Pair ax sp) recsSp))))
      -- passInner : innerRec = recsSp = Pair(thFunTFor(ax), thFunTFor(sp))
  in

  -- Phase 4: case23 extractors → final result
  -- case23 = mkEqF (Post substTFor recsBL) (Post substTFor recsBR)
  --        = Fan (Post substTFor recsBL) (Post substTFor recsBR) Pair
  --
  -- We need:
  -- Post substTFor recsBL (origT, recsT) = substTFor(recsBL(origT, recsT))
  --   = substTFor(Fst(Snd(Snd(recsT))))
  --   → substTFor(Fst(thFunTFor(sp)))  [via passthrough]

  let snd2 = ruleTrans (axPost Snd Pair origT recsT) (axSnd origT recsT)
      ps = ruleTrans (axPost Snd sndArg2 origT recsT) (cong1 Snd snd2)
      sndR = axSnd (ap1 thFunTFor tag23T) innerRec
      full = ruleTrans ps (ruleTrans sndR passInner)
      -- full : Post Snd sndArg2 (origT, recsT) = recsSp

      -- recsBL → Fst(thFunTFor(sp))
      rbL = ruleTrans (axPost Fst recsB origT recsT)
            (ruleTrans (cong1 Fst (ruleTrans (axPost Snd (Post Snd sndArg2) origT recsT) (cong1 Snd full)))
                       (cong1 Fst (axSnd (ap1 thFunTFor ax) (ap1 thFunTFor sp))))
      -- rbL : recsBL(origT, recsT) = Fst(thFunTFor(sp))

      -- recsBR → Snd(thFunTFor(sp))
      rbR = ruleTrans (axPost Snd recsB origT recsT)
            (ruleTrans (cong1 Snd (ruleTrans (axPost Snd (Post Snd sndArg2) origT recsT) (cong1 Snd full)))
                       (cong1 Snd (axSnd (ap1 thFunTFor ax) (ap1 thFunTFor sp))))
      -- rbR : recsBR(origT, recsT) = Snd(thFunTFor(sp))

      -- Post substTFor recsBL → substTFor(Fst(thFunTFor(sp)))
      stfL = ruleTrans (axPost substTFor recsBL origT recsT) (cong1 substTFor rbL)

      -- Post substTFor recsBR → substTFor(Snd(thFunTFor(sp)))
      stfR = ruleTrans (axPost substTFor recsBR origT recsT) (cong1 substTFor rbR)

      -- case23 = Pair(substTFor(Fst(thFunTFor(sp))), substTFor(Snd(thFunTFor(sp))))
      step4 = ruleTrans (axFan (Post substTFor recsBL) (Post substTFor recsBR) Pair origT recsT)
              (ruleTrans (congL Pair (ap2 (Post substTFor recsBR) origT recsT) stfL)
                         (congR Pair (ap1 substTFor (ap1 Fst (ap1 thFunTFor sp))) stfR))
  in

  -- Final chain
  ruleTrans step1 (ruleTrans step2 (ruleTrans step3 step4))
