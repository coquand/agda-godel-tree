{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.ThFunTForV3PassUnify — V3 ndDispatch passthrough chains.
--
-- When an encoded proof's tag is NOT a natCode (specifically, when it
-- is a Pair — i.e., we are looking at a nested sub-encoding at one
-- level up), ndDispatchV3 falls through every branch down to sndArg2.
--
-- Per UNIFIED-DESIGN-REV2.md: tag 26 is no longer a live branch
-- (case26 / ruleHyp removed).  ndT26V3 is defined as an alias for
-- ndT27V3 in Guard.ThFunTForHF, so the passthrough chains skip
-- the n26 step entirely.

module Guard.ThFunTForV3PassUnify where

open import Guard.Base
open import Guard.Term
open import Guard.Formula
open import Guard.DerivF
open import Guard.ThFunTForDefs
open import Guard.ThFunTForCases0
open import Guard.ThFunTForCases1
open import Guard.ThFunTForCases2
open import Guard.ThFunTForCases3
open import Guard.ThFunTForHF
open import Guard.PairPassthroughUnify

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
  n29 : Nat ; n29 = suc n28
  n30 : Nat ; n30 = suc n29
  n31 : Nat ; n31 = suc n30
  n32 : Nat ; n32 = suc n31
  n33 : Nat ; n33 = suc n32

------------------------------------------------------------------------
-- Miss chain for tags of shape Pair(Pair(a1,a2), b).
--
-- The HF ndDispatchV3 chain is
--   branch n0 case0 ⊸ branch n1 case1 ⊸ ... ⊸ branch n25 case25
--     ⊸ ndT26V3 = ndT27V3 ⊸ branch n27 case27 ⊸ ... ⊸ branch n33 case33 ⊸ sndArg2.
-- There is no branch-n26 step: ndT26V3 is a definitional alias for
-- ndT27V3.  So the miss chain skips directly from n25 to n27.

ndDispatchV3PairMiss : (a1 a2 b x recs : Term) ->
  Deriv (eqF (ap2 ndDispatchV3 (ap2 Pair (ap2 Pair (ap2 Pair a1 a2) b) x) recs)
                 (ap2 sndArg2 (ap2 Pair (ap2 Pair (ap2 Pair a1 a2) b) x) recs))
ndDispatchV3PairMiss a1 a2 b x recs =
  let p = pairBranchMiss a1 a2 b x in
  ruleTrans (p n0 case0 ndT1V3 recs)
  (ruleTrans (p n1 case1 ndT2V3 recs)
  (ruleTrans (p n2 case2 ndT3V3 recs)
  (ruleTrans (p n3 case3 ndT4V3 recs)
  (ruleTrans (p n4 case4 ndT5V3 recs)
  (ruleTrans (p n5 case5 ndT6V3 recs)
  (ruleTrans (p n6 case6 ndT7V3 recs)
  (ruleTrans (p n7 case7 ndT8V3 recs)
  (ruleTrans (p n8 case8 ndT9V3 recs)
  (ruleTrans (p n9 case9 ndT10V3 recs)
  (ruleTrans (p n10 case10 ndT11V3 recs)
  (ruleTrans (p n11 case11 ndT12V3 recs)
  (ruleTrans (p n12 case12 ndT13V3 recs)
  (ruleTrans (p n13 case13 ndT14V3 recs)
  (ruleTrans (p n14 case14 ndT15V3 recs)
  (ruleTrans (p n15 case15 ndT16V3 recs)
  (ruleTrans (p n16 case16 ndT17V3 recs)
  (ruleTrans (p n17 case17 ndT18V3 recs)
  (ruleTrans (p n18 case18 ndT19V3 recs)
  (ruleTrans (p n19 case19V3 ndT20V3 recs)
  (ruleTrans (p n20 case20 ndT21V3 recs)
  (ruleTrans (p n21 case21 ndT22V3 recs)
  (ruleTrans (p n22 case22 ndT23V3 recs)
  (ruleTrans (p n23 case23V3 ndT24V3 recs)
  (ruleTrans (p n24 case24 ndT25V3 recs)
  (ruleTrans (p n25 case25 ndT26V3 recs)   -- ndT26V3 = ndT27V3 definitionally
  (ruleTrans (p n27 case27 ndT28V3 recs)
  (ruleTrans (p n28 case28 ndT29V3 recs)
  (ruleTrans (p n29 case29 ndT30V3 recs)
  (ruleTrans (p n30 case30 ndT31V3 recs)
  (ruleTrans (p n31 case31 ndT32V3 recs)
  (ruleTrans (p n32 case32 ndT33V3 recs)
             (p n33 case33 ndT34V3 recs))))))))))))))))))))))))))))))))

------------------------------------------------------------------------
-- Miss chain for tags of shape Pair(O, Pair(Pair(c1,c2), d)).

ndDispatchV3OPairMiss : (c1 c2 d x recs : Term) ->
  Deriv (eqF (ap2 ndDispatchV3 (ap2 Pair (ap2 Pair O (ap2 Pair (ap2 Pair c1 c2) d)) x) recs)
                 (ap2 sndArg2 (ap2 Pair (ap2 Pair O (ap2 Pair (ap2 Pair c1 c2) d)) x) recs))
ndDispatchV3OPairMiss c1 c2 d x recs =
  let o = oPairBranchMiss c1 c2 d x in
  ruleTrans (o n0 case0 ndT1V3 recs)
  (ruleTrans (o n1 case1 ndT2V3 recs)
  (ruleTrans (o n2 case2 ndT3V3 recs)
  (ruleTrans (o n3 case3 ndT4V3 recs)
  (ruleTrans (o n4 case4 ndT5V3 recs)
  (ruleTrans (o n5 case5 ndT6V3 recs)
  (ruleTrans (o n6 case6 ndT7V3 recs)
  (ruleTrans (o n7 case7 ndT8V3 recs)
  (ruleTrans (o n8 case8 ndT9V3 recs)
  (ruleTrans (o n9 case9 ndT10V3 recs)
  (ruleTrans (o n10 case10 ndT11V3 recs)
  (ruleTrans (o n11 case11 ndT12V3 recs)
  (ruleTrans (o n12 case12 ndT13V3 recs)
  (ruleTrans (o n13 case13 ndT14V3 recs)
  (ruleTrans (o n14 case14 ndT15V3 recs)
  (ruleTrans (o n15 case15 ndT16V3 recs)
  (ruleTrans (o n16 case16 ndT17V3 recs)
  (ruleTrans (o n17 case17 ndT18V3 recs)
  (ruleTrans (o n18 case18 ndT19V3 recs)
  (ruleTrans (o n19 case19V3 ndT20V3 recs)
  (ruleTrans (o n20 case20 ndT21V3 recs)
  (ruleTrans (o n21 case21 ndT22V3 recs)
  (ruleTrans (o n22 case22 ndT23V3 recs)
  (ruleTrans (o n23 case23V3 ndT24V3 recs)
  (ruleTrans (o n24 case24 ndT25V3 recs)
  (ruleTrans (o n25 case25 ndT26V3 recs)   -- ndT26V3 = ndT27V3 definitionally
  (ruleTrans (o n27 case27 ndT28V3 recs)
  (ruleTrans (o n28 case28 ndT29V3 recs)
  (ruleTrans (o n29 case29 ndT30V3 recs)
  (ruleTrans (o n30 case30 ndT31V3 recs)
  (ruleTrans (o n31 case31 ndT32V3 recs)
  (ruleTrans (o n32 case32 ndT33V3 recs)
             (o n33 case33 ndT34V3 recs))))))))))))))))))))))))))))))))

------------------------------------------------------------------------
-- passthroughSucV3: convenience wrapper around ndDispatchV3PairMiss
-- specialised to tags of shape  Pair O (reify (natCode n))  — the
-- reification of  natCode (suc n) .  Used by every base case except
-- axI (whose tag is natCode 0 = lf).

passthroughSucV3 : (n : Nat) (dat : Tree) (x rcs : Term) ->
  Deriv (eqF (ap2 ndDispatchV3
                  (ap2 Pair (ap2 Pair (ap2 Pair O (reify (natCode n))) (reify dat)) x) rcs)
                 (ap2 sndArg2
                  (ap2 Pair (ap2 Pair (ap2 Pair O (reify (natCode n))) (reify dat)) x) rcs))
passthroughSucV3 n dat x rcs =
  ndDispatchV3PairMiss O (reify (natCode n)) (reify dat) x rcs

------------------------------------------------------------------------
-- axIPassthroughV3: passthrough for  encAxI (code t)  = nd lf (nd (code t) lf).

axIPassthroughV3 : (t : Term) (x rcs : Term) ->
  Deriv (eqF (ap2 ndDispatchV3
                  (ap2 Pair (ap2 Pair O (ap2 Pair (reify (code t)) O)) x) rcs)
                 (ap2 sndArg2
                  (ap2 Pair (ap2 Pair O (ap2 Pair (reify (code t)) O)) x) rcs))
axIPassthroughV3 O x rcs =
  ndDispatchV3OPairMiss O O O x rcs
axIPassthroughV3 (var n) x rcs =
  ndDispatchV3OPairMiss
    (ap2 Pair (ap2 Pair (ap2 Pair O O) O) O) (reify (natCode n)) O x rcs
axIPassthroughV3 (ap1 f t) x rcs =
  ndDispatchV3OPairMiss
    (ap2 Pair O (ap2 Pair O O))
    (ap2 Pair (reify (codeF1 f)) (reify (code t))) O x rcs
axIPassthroughV3 (ap2 g a b) x rcs =
  ndDispatchV3OPairMiss
    (ap2 Pair O (ap2 Pair O (ap2 Pair O O)))
    (ap2 Pair (reify (codeF2 g)) (ap2 Pair (reify (code a)) (reify (code b))))
    O x rcs
