{-# OPTIONS --safe --without-K --exact-split #-}

module Guard.PairPassthroughAll where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.ThFunTFor
open import Guard.ThFunTForDefs
open import Guard.ThFunTForCases0
open import Guard.ThFunTForCases1
open import Guard.ThFunTForCases2
open import Guard.ThFunTForCases3
open import Guard.ThFunTForCorrectDefs
open import Guard.PairPassthrough

private
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
  n25 : Nat ; n25 = suc n24

  pm : (a1 a2 b x : Term) (n : Nat) (c t : Fun2) (r : Term) -> {hyp : Equation} -> Deriv hyp (eqn (ap2 (branch (tagCheck n) c t) (ap2 Pair (ap2 Pair (ap2 Pair a1 a2) b) x) r) (ap2 t (ap2 Pair (ap2 Pair (ap2 Pair a1 a2) b) x) r))
  pm = pairBranchMiss

  om : (c1 c2 d x : Term) (n : Nat) (c t : Fun2) (r : Term) -> {hyp : Equation} -> Deriv hyp (eqn (ap2 (branch (tagCheck n) c t) (ap2 Pair (ap2 Pair O (ap2 Pair (ap2 Pair c1 c2) d)) x) r) (ap2 t (ap2 Pair (ap2 Pair O (ap2 Pair (ap2 Pair c1 c2) d)) x) r))
  om = oPairBranchMiss

------------------------------------------------------------------------
-- When tag = Pair(Pair(a1,a2),b), ndDispatch falls through to sndArg2.

ndDispatchPairMiss : (a1 a2 b x recs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (ap2 Pair (ap2 Pair a1 a2) b) x) recs)
                 (ap2 sndArg2 (ap2 Pair (ap2 Pair (ap2 Pair a1 a2) b) x) recs))
ndDispatchPairMiss a1 a2 b x recs =
  let p = pm a1 a2 b x in
  ruleTrans (p n0 case0 ndT1 recs)
  (ruleTrans (p n1 case1 ndT2 recs) (ruleTrans (p n2 case2 ndT3 recs)
  (ruleTrans (p n3 case3 ndT4 recs) (ruleTrans (p n4 case4 ndT5 recs)
  (ruleTrans (p n5 case5 ndT6 recs) (ruleTrans (p n6 case6 ndT7 recs)
  (ruleTrans (p n7 case7 ndT8 recs) (ruleTrans (p n8 case8 ndT9 recs)
  (ruleTrans (p n9 case9 ndT10 recs) (ruleTrans (p n10 case10 ndT11 recs)
  (ruleTrans (p n11 case11 ndT12 recs) (ruleTrans (p n12 case12 ndT13 recs)
  (ruleTrans (p n13 case13 ndT14 recs) (ruleTrans (p n14 case14 ndT15 recs)
  (ruleTrans (p n15 case15 ndT16 recs) (ruleTrans (p n16 case16 ndT17 recs)
  (ruleTrans (p n17 case17 ndT18 recs) (ruleTrans (p n18 case18 ndT19 recs)
  (ruleTrans (p n19 case19 ndT20 recs) (ruleTrans (p n20 case20 ndT21 recs)
  (ruleTrans (p n21 case21 ndT22 recs) (ruleTrans (p n22 case22 ndT23 recs)
  (ruleTrans (p n23 case23 ndT24 recs) (ruleTrans (p n24 case24 ndT25 recs)
  (p n25 case25 ndT26 recs)))))))))))))))))))))))))

------------------------------------------------------------------------
-- When tag = Pair(O, Pair(Pair(c1,c2), d)): covers encAxI sub-proofs.

ndDispatchOPairMiss : (c1 c2 d x recs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (ap2 Pair O (ap2 Pair (ap2 Pair c1 c2) d)) x) recs)
                 (ap2 sndArg2 (ap2 Pair (ap2 Pair O (ap2 Pair (ap2 Pair c1 c2) d)) x) recs))
ndDispatchOPairMiss c1 c2 d x recs =
  let o = om c1 c2 d x in
  ruleTrans (o n0 case0 ndT1 recs)
  (ruleTrans (o n1 case1 ndT2 recs) (ruleTrans (o n2 case2 ndT3 recs)
  (ruleTrans (o n3 case3 ndT4 recs) (ruleTrans (o n4 case4 ndT5 recs)
  (ruleTrans (o n5 case5 ndT6 recs) (ruleTrans (o n6 case6 ndT7 recs)
  (ruleTrans (o n7 case7 ndT8 recs) (ruleTrans (o n8 case8 ndT9 recs)
  (ruleTrans (o n9 case9 ndT10 recs) (ruleTrans (o n10 case10 ndT11 recs)
  (ruleTrans (o n11 case11 ndT12 recs) (ruleTrans (o n12 case12 ndT13 recs)
  (ruleTrans (o n13 case13 ndT14 recs) (ruleTrans (o n14 case14 ndT15 recs)
  (ruleTrans (o n15 case15 ndT16 recs) (ruleTrans (o n16 case16 ndT17 recs)
  (ruleTrans (o n17 case17 ndT18 recs) (ruleTrans (o n18 case18 ndT19 recs)
  (ruleTrans (o n19 case19 ndT20 recs) (ruleTrans (o n20 case20 ndT21 recs)
  (ruleTrans (o n21 case21 ndT22 recs) (ruleTrans (o n22 case22 ndT23 recs)
  (ruleTrans (o n23 case23 ndT24 recs) (ruleTrans (o n24 case24 ndT25 recs)
  (o n25 case25 ndT26 recs)))))))))))))))))))))))))
