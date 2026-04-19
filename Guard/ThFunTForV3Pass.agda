{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.ThFunTForV3Pass — V3 ndDispatch passthrough chains.
--
-- When an encoded proof's tag is NOT a natCode (specifically, when it
-- is a Pair — i.e., we are looking at a nested sub-encoding at one
-- level up), ndDispatchV3 hCode falls through every branch down to
-- sndArg2.  This file provides the 27-step miss chains (one more miss
-- than V2, for the new n26 branch).
--
-- These generalise Guard.PairPassthroughAll.ndDispatchPairMiss /
-- ndDispatchOPairMiss to the V3 chain.

module Guard.ThFunTForV3Pass where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.ThFunTForDefs
open import Guard.ThFunTForCases0
open import Guard.ThFunTForCases1
open import Guard.ThFunTForCases2
open import Guard.ThFunTForCases3
open import Guard.ThFunTForV3
open import Guard.PairPassthrough

-- codeF1, codeF2, code, reify all re-exported via Guard.Term above.

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
  n26 : Nat ; n26 = suc n25
  n27 : Nat ; n27 = suc n26
  n28 : Nat ; n28 = suc n27

------------------------------------------------------------------------
-- 27-branch miss chain for tags of shape Pair(Pair(a1,a2), b).
--
-- The V3 ndDispatchV3 hCode chain is
--   branch n0 case0  ⊸ branch n1 case1 ⊸ ... ⊸ branch n25 case25
--     ⊸ branch n26 (case26 hCode) ⊸ sndArg2.
-- With the given tag shape, every tagCheck against natCode n misses,
-- so we fall through all 27 branches down to sndArg2.

ndDispatchV3PairMiss : (hCode a1 a2 b x recs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (ndDispatchV3 hCode) (ap2 Pair (ap2 Pair (ap2 Pair a1 a2) b) x) recs)
                 (ap2 sndArg2 (ap2 Pair (ap2 Pair (ap2 Pair a1 a2) b) x) recs))
ndDispatchV3PairMiss hCode a1 a2 b x recs =
  let p = pairBranchMiss a1 a2 b x in
  ruleTrans (p n0 case0 (ndT1V3 hCode) recs)
  (ruleTrans (p n1 case1 (ndT2V3 hCode) recs)
  (ruleTrans (p n2 case2 (ndT3V3 hCode) recs)
  (ruleTrans (p n3 case3 (ndT4V3 hCode) recs)
  (ruleTrans (p n4 case4 (ndT5V3 hCode) recs)
  (ruleTrans (p n5 case5 (ndT6V3 hCode) recs)
  (ruleTrans (p n6 case6 (ndT7V3 hCode) recs)
  (ruleTrans (p n7 case7 (ndT8V3 hCode) recs)
  (ruleTrans (p n8 case8 (ndT9V3 hCode) recs)
  (ruleTrans (p n9 case9 (ndT10V3 hCode) recs)
  (ruleTrans (p n10 case10 (ndT11V3 hCode) recs)
  (ruleTrans (p n11 case11 (ndT12V3 hCode) recs)
  (ruleTrans (p n12 case12 (ndT13V3 hCode) recs)
  (ruleTrans (p n13 case13 (ndT14V3 hCode) recs)
  (ruleTrans (p n14 case14 (ndT15V3 hCode) recs)
  (ruleTrans (p n15 case15 (ndT16V3 hCode) recs)
  (ruleTrans (p n16 case16 (ndT17V3 hCode) recs)
  (ruleTrans (p n17 case17 (ndT18V3 hCode) recs)
  (ruleTrans (p n18 case18 (ndT19V3 hCode) recs)
  (ruleTrans (p n19 case19V3 (ndT20V3 hCode) recs)
  (ruleTrans (p n20 case20 (ndT21V3 hCode) recs)
  (ruleTrans (p n21 case21 (ndT22V3 hCode) recs)
  (ruleTrans (p n22 case22 (ndT23V3 hCode) recs)
  (ruleTrans (p n23 case23V3 (ndT24V3 hCode) recs)
  (ruleTrans (p n24 case24 (ndT25V3 hCode) recs)
  (ruleTrans (p n25 case25 (ndT26V3 hCode) recs)
  (ruleTrans (p n26 (case26 hCode) ndT27V3 recs)
  (ruleTrans (p n27 case27 ndT28V3 recs)
             (p n28 case28 ndT29V3 recs))))))))))))))))))))))))))))

------------------------------------------------------------------------
-- 27-branch miss chain for tags of shape Pair(O, Pair(Pair(c1,c2), d))
-- (covers encAxI / encRefl sub-proofs where the tag's first element
-- is literally O = reify (natCode 0)).

ndDispatchV3OPairMiss : (hCode c1 c2 d x recs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (ndDispatchV3 hCode) (ap2 Pair (ap2 Pair O (ap2 Pair (ap2 Pair c1 c2) d)) x) recs)
                 (ap2 sndArg2 (ap2 Pair (ap2 Pair O (ap2 Pair (ap2 Pair c1 c2) d)) x) recs))
ndDispatchV3OPairMiss hCode c1 c2 d x recs =
  let o = oPairBranchMiss c1 c2 d x in
  ruleTrans (o n0 case0 (ndT1V3 hCode) recs)
  (ruleTrans (o n1 case1 (ndT2V3 hCode) recs)
  (ruleTrans (o n2 case2 (ndT3V3 hCode) recs)
  (ruleTrans (o n3 case3 (ndT4V3 hCode) recs)
  (ruleTrans (o n4 case4 (ndT5V3 hCode) recs)
  (ruleTrans (o n5 case5 (ndT6V3 hCode) recs)
  (ruleTrans (o n6 case6 (ndT7V3 hCode) recs)
  (ruleTrans (o n7 case7 (ndT8V3 hCode) recs)
  (ruleTrans (o n8 case8 (ndT9V3 hCode) recs)
  (ruleTrans (o n9 case9 (ndT10V3 hCode) recs)
  (ruleTrans (o n10 case10 (ndT11V3 hCode) recs)
  (ruleTrans (o n11 case11 (ndT12V3 hCode) recs)
  (ruleTrans (o n12 case12 (ndT13V3 hCode) recs)
  (ruleTrans (o n13 case13 (ndT14V3 hCode) recs)
  (ruleTrans (o n14 case14 (ndT15V3 hCode) recs)
  (ruleTrans (o n15 case15 (ndT16V3 hCode) recs)
  (ruleTrans (o n16 case16 (ndT17V3 hCode) recs)
  (ruleTrans (o n17 case17 (ndT18V3 hCode) recs)
  (ruleTrans (o n18 case18 (ndT19V3 hCode) recs)
  (ruleTrans (o n19 case19V3 (ndT20V3 hCode) recs)
  (ruleTrans (o n20 case20 (ndT21V3 hCode) recs)
  (ruleTrans (o n21 case21 (ndT22V3 hCode) recs)
  (ruleTrans (o n22 case22 (ndT23V3 hCode) recs)
  (ruleTrans (o n23 case23V3 (ndT24V3 hCode) recs)
  (ruleTrans (o n24 case24 (ndT25V3 hCode) recs)
  (ruleTrans (o n25 case25 (ndT26V3 hCode) recs)
  (ruleTrans (o n26 (case26 hCode) ndT27V3 recs)
  (ruleTrans (o n27 case27 ndT28V3 recs)
             (o n28 case28 ndT29V3 recs))))))))))))))))))))))))))))

------------------------------------------------------------------------
-- passthroughSucV3: convenience wrapper around ndDispatchV3PairMiss
-- specialised to tags of shape  Pair O (reify (natCode n))  — the
-- reification of  natCode (suc n) .  Used by every base case except
-- axI (whose tag is natCode 0 = lf).

passthroughSucV3 : (hCode : Term) (n : Nat) (dat : Tree) (x rcs : Term) ->
                   {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (ndDispatchV3 hCode)
                  (ap2 Pair (ap2 Pair (ap2 Pair O (reify (natCode n))) (reify dat)) x) rcs)
                 (ap2 sndArg2
                  (ap2 Pair (ap2 Pair (ap2 Pair O (reify (natCode n))) (reify dat)) x) rcs))
passthroughSucV3 hCode n dat x rcs =
  ndDispatchV3PairMiss hCode O (reify (natCode n)) (reify dat) x rcs

------------------------------------------------------------------------
-- axIPassthroughV3: passthrough for  encAxI (code t)  = nd lf (nd (code t) lf).
--
-- The encoding's tag is  natCode n0 = lf ; reify = O.  Since the tag is
-- a leaf (not a suc), we need the OPair form with the first Pair being
-- (O, reify(code t)).  reify(code t) is always a Pair (Pair c1 c2) for
-- some c1, c2 extractable by case analysis on the Term t.

axIPassthroughV3 : (hCode : Term) (t : Term) (x rcs : Term) ->
                   {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (ndDispatchV3 hCode)
                  (ap2 Pair (ap2 Pair O (ap2 Pair (reify (code t)) O)) x) rcs)
                 (ap2 sndArg2
                  (ap2 Pair (ap2 Pair O (ap2 Pair (reify (code t)) O)) x) rcs))
axIPassthroughV3 hCode O x rcs =
  ndDispatchV3OPairMiss hCode O O O x rcs
axIPassthroughV3 hCode (var n) x rcs =
  ndDispatchV3OPairMiss hCode
    (ap2 Pair (ap2 Pair (ap2 Pair O O) O) O) (reify (natCode n)) O x rcs
axIPassthroughV3 hCode (ap1 f t) x rcs =
  ndDispatchV3OPairMiss hCode
    (ap2 Pair O (ap2 Pair O O))
    (ap2 Pair (reify (codeF1 f)) (reify (code t))) O x rcs
axIPassthroughV3 hCode (ap2 g a b) x rcs =
  ndDispatchV3OPairMiss hCode
    (ap2 Pair O (ap2 Pair O (ap2 Pair O O)))
    (ap2 Pair (reify (codeF2 g)) (ap2 Pair (reify (code a)) (reify (code b))))
    O x rcs
