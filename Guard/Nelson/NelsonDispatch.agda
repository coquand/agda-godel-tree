{-# OPTIONS --safe --without-K --exact-split #-}

-- NelsonDispatch.agda
-- Generic dispatch chain proofs for thFunTFor case selection.
-- Uses ndBranchMiss/ndBranchHit from ThFunTForCorrectDefs.
--
-- For each tag k, ndDispatchToCase_k proves:
--   ndDispatch(Pair(reify(natCode k), data'), recs) = case_k(...)
--
-- Also provides phase1Nd combining RecNd + guardNd.

module Guard.Nelson.NelsonDispatch where

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
open import Guard.ThFunTForCorrectDefs

------------------------------------------------------------------------
-- Nat abbreviations (exported for use by Nelson case proofs)

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

------------------------------------------------------------------------
-- Phase 1: RecNd + guardNd
-- Unfolds thFunTFor on Pair(tagT, Pair(x, y)) to ndDispatch.

phase1Nd : (tagT x y : Term) -> {hyp : Equation} ->
  let origT = ap2 Pair tagT (ap2 Pair x y)
      recsT = ap2 Pair (ap1 thFunTFor tagT) (ap1 thFunTFor (ap2 Pair x y))
  in Deriv hyp (eqn (ap1 thFunTFor origT)
                    (ap2 ndDispatch origT recsT))
phase1Nd tagT x y =
  ruleTrans (axRecNd O thFunStep tagT (ap2 Pair x y))
            (guardNd tagT x y
              (ap2 Pair (ap1 thFunTFor tagT)
                        (ap1 thFunTFor (ap2 Pair x y))))

------------------------------------------------------------------------
-- Dispatch chain proofs: ndDispatch -> caseK
--
-- Each uses ndBranchMiss (tag != branch) and ndBranchHit (tag = branch).
-- The inequality proof Eq (natEq k n) false is always refl for
-- distinct concrete nats.

-- abbreviation
private
  bm : (k n : Nat) (c t : Fun2) (d r : Term) -> {hyp : Equation} ->
       Eq (natEq k n) false ->
       Deriv hyp (eqn (ap2 (branch (tagCheck n) c t) (ap2 Pair (reify (natCode k)) d) r)
                      (ap2 t (ap2 Pair (reify (natCode k)) d) r))
  bm = ndBranchMiss

  bh : (k : Nat) (c t : Fun2) (d r : Term) -> {hyp : Equation} ->
       Deriv hyp (eqn (ap2 (branch (tagCheck k) c t) (ap2 Pair (reify (natCode k)) d) r)
                      (ap2 c (ap2 Pair (reify (natCode k)) d) r))
  bh = ndBranchHit

-- Tag 0: axI (direct hit, no misses)
ndDispatchToCase0 : (data' recs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (natCode n0)) data') recs)
                 (ap2 case0 (ap2 Pair (reify (natCode n0)) data') recs))
ndDispatchToCase0 d r = bh n0 case0 ndT1 d r

-- Tag 1: axFst (1 miss + hit)
ndDispatchToCase1 : (data' recs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (natCode n1)) data') recs)
                 (ap2 case1 (ap2 Pair (reify (natCode n1)) data') recs))
ndDispatchToCase1 d r =
  ruleTrans (bm n1 n0 case0 ndT1 d r refl)
            (bh n1 case1 ndT2 d r)

-- Tag 2: axSnd
ndDispatchToCase2 : (data' recs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (natCode n2)) data') recs)
                 (ap2 case2 (ap2 Pair (reify (natCode n2)) data') recs))
ndDispatchToCase2 d r =
  ruleTrans (bm n2 n0 case0 ndT1 d r refl)
  (ruleTrans (bm n2 n1 case1 ndT2 d r refl)
             (bh n2 case2 ndT3 d r))

-- Tag 3: axConst
ndDispatchToCase3 : (data' recs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (natCode n3)) data') recs)
                 (ap2 case3 (ap2 Pair (reify (natCode n3)) data') recs))
ndDispatchToCase3 d r =
  ruleTrans (bm n3 n0 case0 ndT1 d r refl)
  (ruleTrans (bm n3 n1 case1 ndT2 d r refl)
  (ruleTrans (bm n3 n2 case2 ndT3 d r refl)
             (bh n3 case3 ndT4 d r)))

-- Tag 4
ndDispatchToCase4 : (data' recs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (natCode n4)) data') recs)
                 (ap2 case4 (ap2 Pair (reify (natCode n4)) data') recs))
ndDispatchToCase4 d r =
  ruleTrans (bm n4 n0 case0 ndT1 d r refl)
  (ruleTrans (bm n4 n1 case1 ndT2 d r refl)
  (ruleTrans (bm n4 n2 case2 ndT3 d r refl)
  (ruleTrans (bm n4 n3 case3 ndT4 d r refl)
             (bh n4 case4 ndT5 d r))))

-- Tag 5
ndDispatchToCase5 : (data' recs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (natCode n5)) data') recs)
                 (ap2 case5 (ap2 Pair (reify (natCode n5)) data') recs))
ndDispatchToCase5 d r =
  ruleTrans (bm n5 n0 case0 ndT1 d r refl)
  (ruleTrans (bm n5 n1 case1 ndT2 d r refl)
  (ruleTrans (bm n5 n2 case2 ndT3 d r refl)
  (ruleTrans (bm n5 n3 case3 ndT4 d r refl)
  (ruleTrans (bm n5 n4 case4 ndT5 d r refl)
             (bh n5 case5 ndT6 d r)))))

-- Tag 6
ndDispatchToCase6 : (data' recs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (natCode n6)) data') recs)
                 (ap2 case6 (ap2 Pair (reify (natCode n6)) data') recs))
ndDispatchToCase6 d r =
  ruleTrans (bm n6 n0 case0 ndT1 d r refl)
  (ruleTrans (bm n6 n1 case1 ndT2 d r refl)
  (ruleTrans (bm n6 n2 case2 ndT3 d r refl)
  (ruleTrans (bm n6 n3 case3 ndT4 d r refl)
  (ruleTrans (bm n6 n4 case4 ndT5 d r refl)
  (ruleTrans (bm n6 n5 case5 ndT6 d r refl)
             (bh n6 case6 ndT7 d r))))))

-- Tag 7
ndDispatchToCase7 : (data' recs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (natCode n7)) data') recs)
                 (ap2 case7 (ap2 Pair (reify (natCode n7)) data') recs))
ndDispatchToCase7 d r =
  ruleTrans (bm n7 n0 case0 ndT1 d r refl)
  (ruleTrans (bm n7 n1 case1 ndT2 d r refl)
  (ruleTrans (bm n7 n2 case2 ndT3 d r refl)
  (ruleTrans (bm n7 n3 case3 ndT4 d r refl)
  (ruleTrans (bm n7 n4 case4 ndT5 d r refl)
  (ruleTrans (bm n7 n5 case5 ndT6 d r refl)
  (ruleTrans (bm n7 n6 case6 ndT7 d r refl)
             (bh n7 case7 ndT8 d r)))))))

-- Tag 8
ndDispatchToCase8 : (data' recs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (natCode n8)) data') recs)
                 (ap2 case8 (ap2 Pair (reify (natCode n8)) data') recs))
ndDispatchToCase8 d r =
  ruleTrans (bm n8 n0 case0 ndT1 d r refl)
  (ruleTrans (bm n8 n1 case1 ndT2 d r refl)
  (ruleTrans (bm n8 n2 case2 ndT3 d r refl)
  (ruleTrans (bm n8 n3 case3 ndT4 d r refl)
  (ruleTrans (bm n8 n4 case4 ndT5 d r refl)
  (ruleTrans (bm n8 n5 case5 ndT6 d r refl)
  (ruleTrans (bm n8 n6 case6 ndT7 d r refl)
  (ruleTrans (bm n8 n7 case7 ndT8 d r refl)
             (bh n8 case8 ndT9 d r))))))))

-- Tag 9
ndDispatchToCase9 : (data' recs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (natCode n9)) data') recs)
                 (ap2 case9 (ap2 Pair (reify (natCode n9)) data') recs))
ndDispatchToCase9 d r =
  ruleTrans (bm n9 n0 case0 ndT1 d r refl)
  (ruleTrans (bm n9 n1 case1 ndT2 d r refl)
  (ruleTrans (bm n9 n2 case2 ndT3 d r refl)
  (ruleTrans (bm n9 n3 case3 ndT4 d r refl)
  (ruleTrans (bm n9 n4 case4 ndT5 d r refl)
  (ruleTrans (bm n9 n5 case5 ndT6 d r refl)
  (ruleTrans (bm n9 n6 case6 ndT7 d r refl)
  (ruleTrans (bm n9 n7 case7 ndT8 d r refl)
  (ruleTrans (bm n9 n8 case8 ndT9 d r refl)
             (bh n9 case9 ndT10 d r)))))))))

-- Tag 10
ndDispatchToCase10 : (data' recs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (natCode n10)) data') recs)
                 (ap2 case10 (ap2 Pair (reify (natCode n10)) data') recs))
ndDispatchToCase10 d r =
  ruleTrans (bm n10 n0 case0 ndT1  d r refl)
  (ruleTrans (bm n10 n1 case1 ndT2  d r refl)
  (ruleTrans (bm n10 n2 case2 ndT3  d r refl)
  (ruleTrans (bm n10 n3 case3 ndT4  d r refl)
  (ruleTrans (bm n10 n4 case4 ndT5  d r refl)
  (ruleTrans (bm n10 n5 case5 ndT6  d r refl)
  (ruleTrans (bm n10 n6 case6 ndT7  d r refl)
  (ruleTrans (bm n10 n7 case7 ndT8  d r refl)
  (ruleTrans (bm n10 n8 case8 ndT9  d r refl)
  (ruleTrans (bm n10 n9 case9 ndT10 d r refl)
             (bh n10 case10 ndT11 d r))))))))))

-- Tag 11
ndDispatchToCase11 : (data' recs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (natCode n11)) data') recs)
                 (ap2 case11 (ap2 Pair (reify (natCode n11)) data') recs))
ndDispatchToCase11 d r =
  ruleTrans (bm n11 n0  case0  ndT1  d r refl)
  (ruleTrans (bm n11 n1  case1  ndT2  d r refl)
  (ruleTrans (bm n11 n2  case2  ndT3  d r refl)
  (ruleTrans (bm n11 n3  case3  ndT4  d r refl)
  (ruleTrans (bm n11 n4  case4  ndT5  d r refl)
  (ruleTrans (bm n11 n5  case5  ndT6  d r refl)
  (ruleTrans (bm n11 n6  case6  ndT7  d r refl)
  (ruleTrans (bm n11 n7  case7  ndT8  d r refl)
  (ruleTrans (bm n11 n8  case8  ndT9  d r refl)
  (ruleTrans (bm n11 n9  case9  ndT10 d r refl)
  (ruleTrans (bm n11 n10 case10 ndT11 d r refl)
             (bh n11 case11 ndT12 d r)))))))))))

-- Tag 12
ndDispatchToCase12 : (data' recs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (natCode n12)) data') recs)
                 (ap2 case12 (ap2 Pair (reify (natCode n12)) data') recs))
ndDispatchToCase12 d r =
  ruleTrans (bm n12 n0  case0  ndT1  d r refl)
  (ruleTrans (bm n12 n1  case1  ndT2  d r refl)
  (ruleTrans (bm n12 n2  case2  ndT3  d r refl)
  (ruleTrans (bm n12 n3  case3  ndT4  d r refl)
  (ruleTrans (bm n12 n4  case4  ndT5  d r refl)
  (ruleTrans (bm n12 n5  case5  ndT6  d r refl)
  (ruleTrans (bm n12 n6  case6  ndT7  d r refl)
  (ruleTrans (bm n12 n7  case7  ndT8  d r refl)
  (ruleTrans (bm n12 n8  case8  ndT9  d r refl)
  (ruleTrans (bm n12 n9  case9  ndT10 d r refl)
  (ruleTrans (bm n12 n10 case10 ndT11 d r refl)
  (ruleTrans (bm n12 n11 case11 ndT12 d r refl)
             (bh n12 case12 ndT13 d r))))))))))))

-- Tag 13
ndDispatchToCase13 : (data' recs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (natCode n13)) data') recs)
                 (ap2 case13 (ap2 Pair (reify (natCode n13)) data') recs))
ndDispatchToCase13 d r =
  ruleTrans (bm n13 n0  case0  ndT1  d r refl)
  (ruleTrans (bm n13 n1  case1  ndT2  d r refl)
  (ruleTrans (bm n13 n2  case2  ndT3  d r refl)
  (ruleTrans (bm n13 n3  case3  ndT4  d r refl)
  (ruleTrans (bm n13 n4  case4  ndT5  d r refl)
  (ruleTrans (bm n13 n5  case5  ndT6  d r refl)
  (ruleTrans (bm n13 n6  case6  ndT7  d r refl)
  (ruleTrans (bm n13 n7  case7  ndT8  d r refl)
  (ruleTrans (bm n13 n8  case8  ndT9  d r refl)
  (ruleTrans (bm n13 n9  case9  ndT10 d r refl)
  (ruleTrans (bm n13 n10 case10 ndT11 d r refl)
  (ruleTrans (bm n13 n11 case11 ndT12 d r refl)
  (ruleTrans (bm n13 n12 case12 ndT13 d r refl)
             (bh n13 case13 ndT14 d r)))))))))))))

-- Tag 14
ndDispatchToCase14 : (data' recs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (natCode n14)) data') recs)
                 (ap2 case14 (ap2 Pair (reify (natCode n14)) data') recs))
ndDispatchToCase14 d r =
  ruleTrans (bm n14 n0  case0  ndT1  d r refl)
  (ruleTrans (bm n14 n1  case1  ndT2  d r refl)
  (ruleTrans (bm n14 n2  case2  ndT3  d r refl)
  (ruleTrans (bm n14 n3  case3  ndT4  d r refl)
  (ruleTrans (bm n14 n4  case4  ndT5  d r refl)
  (ruleTrans (bm n14 n5  case5  ndT6  d r refl)
  (ruleTrans (bm n14 n6  case6  ndT7  d r refl)
  (ruleTrans (bm n14 n7  case7  ndT8  d r refl)
  (ruleTrans (bm n14 n8  case8  ndT9  d r refl)
  (ruleTrans (bm n14 n9  case9  ndT10 d r refl)
  (ruleTrans (bm n14 n10 case10 ndT11 d r refl)
  (ruleTrans (bm n14 n11 case11 ndT12 d r refl)
  (ruleTrans (bm n14 n12 case12 ndT13 d r refl)
  (ruleTrans (bm n14 n13 case13 ndT14 d r refl)
             (bh n14 case14 ndT15 d r))))))))))))))

-- Tag 15
ndDispatchToCase15 : (data' recs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (natCode n15)) data') recs)
                 (ap2 case15 (ap2 Pair (reify (natCode n15)) data') recs))
ndDispatchToCase15 d r =
  ruleTrans (bm n15 n0  case0  ndT1  d r refl)
  (ruleTrans (bm n15 n1  case1  ndT2  d r refl)
  (ruleTrans (bm n15 n2  case2  ndT3  d r refl)
  (ruleTrans (bm n15 n3  case3  ndT4  d r refl)
  (ruleTrans (bm n15 n4  case4  ndT5  d r refl)
  (ruleTrans (bm n15 n5  case5  ndT6  d r refl)
  (ruleTrans (bm n15 n6  case6  ndT7  d r refl)
  (ruleTrans (bm n15 n7  case7  ndT8  d r refl)
  (ruleTrans (bm n15 n8  case8  ndT9  d r refl)
  (ruleTrans (bm n15 n9  case9  ndT10 d r refl)
  (ruleTrans (bm n15 n10 case10 ndT11 d r refl)
  (ruleTrans (bm n15 n11 case11 ndT12 d r refl)
  (ruleTrans (bm n15 n12 case12 ndT13 d r refl)
  (ruleTrans (bm n15 n13 case13 ndT14 d r refl)
  (ruleTrans (bm n15 n14 case14 ndT15 d r refl)
             (bh n15 case15 ndT16 d r)))))))))))))))

-- Tag 16
ndDispatchToCase16 : (data' recs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (natCode n16)) data') recs)
                 (ap2 case16 (ap2 Pair (reify (natCode n16)) data') recs))
ndDispatchToCase16 d r =
  ruleTrans (bm n16 n0  case0  ndT1  d r refl)
  (ruleTrans (bm n16 n1  case1  ndT2  d r refl)
  (ruleTrans (bm n16 n2  case2  ndT3  d r refl)
  (ruleTrans (bm n16 n3  case3  ndT4  d r refl)
  (ruleTrans (bm n16 n4  case4  ndT5  d r refl)
  (ruleTrans (bm n16 n5  case5  ndT6  d r refl)
  (ruleTrans (bm n16 n6  case6  ndT7  d r refl)
  (ruleTrans (bm n16 n7  case7  ndT8  d r refl)
  (ruleTrans (bm n16 n8  case8  ndT9  d r refl)
  (ruleTrans (bm n16 n9  case9  ndT10 d r refl)
  (ruleTrans (bm n16 n10 case10 ndT11 d r refl)
  (ruleTrans (bm n16 n11 case11 ndT12 d r refl)
  (ruleTrans (bm n16 n12 case12 ndT13 d r refl)
  (ruleTrans (bm n16 n13 case13 ndT14 d r refl)
  (ruleTrans (bm n16 n14 case14 ndT15 d r refl)
  (ruleTrans (bm n16 n15 case15 ndT16 d r refl)
             (bh n16 case16 ndT17 d r))))))))))))))))

-- Tag 17: axRefl
ndDispatchToCase17 : (data' recs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (natCode n17)) data') recs)
                 (ap2 case17 (ap2 Pair (reify (natCode n17)) data') recs))
ndDispatchToCase17 d r =
  ruleTrans (bm n17 n0  case0  ndT1  d r refl)
  (ruleTrans (bm n17 n1  case1  ndT2  d r refl)
  (ruleTrans (bm n17 n2  case2  ndT3  d r refl)
  (ruleTrans (bm n17 n3  case3  ndT4  d r refl)
  (ruleTrans (bm n17 n4  case4  ndT5  d r refl)
  (ruleTrans (bm n17 n5  case5  ndT6  d r refl)
  (ruleTrans (bm n17 n6  case6  ndT7  d r refl)
  (ruleTrans (bm n17 n7  case7  ndT8  d r refl)
  (ruleTrans (bm n17 n8  case8  ndT9  d r refl)
  (ruleTrans (bm n17 n9  case9  ndT10 d r refl)
  (ruleTrans (bm n17 n10 case10 ndT11 d r refl)
  (ruleTrans (bm n17 n11 case11 ndT12 d r refl)
  (ruleTrans (bm n17 n12 case12 ndT13 d r refl)
  (ruleTrans (bm n17 n13 case13 ndT14 d r refl)
  (ruleTrans (bm n17 n14 case14 ndT15 d r refl)
  (ruleTrans (bm n17 n15 case15 ndT16 d r refl)
  (ruleTrans (bm n17 n16 case16 ndT17 d r refl)
             (bh n17 case17 ndT18 d r)))))))))))))))))

-- Tag 18: ruleSym
ndDispatchToCase18 : (data' recs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (natCode n18)) data') recs)
                 (ap2 case18 (ap2 Pair (reify (natCode n18)) data') recs))
ndDispatchToCase18 d r =
  ruleTrans (bm n18 n0  case0  ndT1  d r refl)
  (ruleTrans (bm n18 n1  case1  ndT2  d r refl)
  (ruleTrans (bm n18 n2  case2  ndT3  d r refl)
  (ruleTrans (bm n18 n3  case3  ndT4  d r refl)
  (ruleTrans (bm n18 n4  case4  ndT5  d r refl)
  (ruleTrans (bm n18 n5  case5  ndT6  d r refl)
  (ruleTrans (bm n18 n6  case6  ndT7  d r refl)
  (ruleTrans (bm n18 n7  case7  ndT8  d r refl)
  (ruleTrans (bm n18 n8  case8  ndT9  d r refl)
  (ruleTrans (bm n18 n9  case9  ndT10 d r refl)
  (ruleTrans (bm n18 n10 case10 ndT11 d r refl)
  (ruleTrans (bm n18 n11 case11 ndT12 d r refl)
  (ruleTrans (bm n18 n12 case12 ndT13 d r refl)
  (ruleTrans (bm n18 n13 case13 ndT14 d r refl)
  (ruleTrans (bm n18 n14 case14 ndT15 d r refl)
  (ruleTrans (bm n18 n15 case15 ndT16 d r refl)
  (ruleTrans (bm n18 n16 case16 ndT17 d r refl)
  (ruleTrans (bm n18 n17 case17 ndT18 d r refl)
             (bh n18 case18 ndT19 d r))))))))))))))))))

-- Tag 19: ruleTrans
ndDispatchToCase19 : (data' recs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (natCode n19)) data') recs)
                 (ap2 case19 (ap2 Pair (reify (natCode n19)) data') recs))
ndDispatchToCase19 d r =
  ruleTrans (bm n19 n0  case0  ndT1  d r refl)
  (ruleTrans (bm n19 n1  case1  ndT2  d r refl)
  (ruleTrans (bm n19 n2  case2  ndT3  d r refl)
  (ruleTrans (bm n19 n3  case3  ndT4  d r refl)
  (ruleTrans (bm n19 n4  case4  ndT5  d r refl)
  (ruleTrans (bm n19 n5  case5  ndT6  d r refl)
  (ruleTrans (bm n19 n6  case6  ndT7  d r refl)
  (ruleTrans (bm n19 n7  case7  ndT8  d r refl)
  (ruleTrans (bm n19 n8  case8  ndT9  d r refl)
  (ruleTrans (bm n19 n9  case9  ndT10 d r refl)
  (ruleTrans (bm n19 n10 case10 ndT11 d r refl)
  (ruleTrans (bm n19 n11 case11 ndT12 d r refl)
  (ruleTrans (bm n19 n12 case12 ndT13 d r refl)
  (ruleTrans (bm n19 n13 case13 ndT14 d r refl)
  (ruleTrans (bm n19 n14 case14 ndT15 d r refl)
  (ruleTrans (bm n19 n15 case15 ndT16 d r refl)
  (ruleTrans (bm n19 n16 case16 ndT17 d r refl)
  (ruleTrans (bm n19 n17 case17 ndT18 d r refl)
  (ruleTrans (bm n19 n18 case18 ndT19 d r refl)
             (bh n19 case19 ndT20 d r)))))))))))))))))))

-- Tag 20: cong1
ndDispatchToCase20 : (data' recs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (natCode n20)) data') recs)
                 (ap2 case20 (ap2 Pair (reify (natCode n20)) data') recs))
ndDispatchToCase20 d r =
  ruleTrans (bm n20 n0  case0  ndT1  d r refl)
  (ruleTrans (bm n20 n1  case1  ndT2  d r refl)
  (ruleTrans (bm n20 n2  case2  ndT3  d r refl)
  (ruleTrans (bm n20 n3  case3  ndT4  d r refl)
  (ruleTrans (bm n20 n4  case4  ndT5  d r refl)
  (ruleTrans (bm n20 n5  case5  ndT6  d r refl)
  (ruleTrans (bm n20 n6  case6  ndT7  d r refl)
  (ruleTrans (bm n20 n7  case7  ndT8  d r refl)
  (ruleTrans (bm n20 n8  case8  ndT9  d r refl)
  (ruleTrans (bm n20 n9  case9  ndT10 d r refl)
  (ruleTrans (bm n20 n10 case10 ndT11 d r refl)
  (ruleTrans (bm n20 n11 case11 ndT12 d r refl)
  (ruleTrans (bm n20 n12 case12 ndT13 d r refl)
  (ruleTrans (bm n20 n13 case13 ndT14 d r refl)
  (ruleTrans (bm n20 n14 case14 ndT15 d r refl)
  (ruleTrans (bm n20 n15 case15 ndT16 d r refl)
  (ruleTrans (bm n20 n16 case16 ndT17 d r refl)
  (ruleTrans (bm n20 n17 case17 ndT18 d r refl)
  (ruleTrans (bm n20 n18 case18 ndT19 d r refl)
  (ruleTrans (bm n20 n19 case19 ndT20 d r refl)
             (bh n20 case20 ndT21 d r))))))))))))))))))))

-- Tag 21: congL
ndDispatchToCase21 : (data' recs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (natCode n21)) data') recs)
                 (ap2 case21 (ap2 Pair (reify (natCode n21)) data') recs))
ndDispatchToCase21 d r =
  ruleTrans (bm n21 n0  case0  ndT1  d r refl)
  (ruleTrans (bm n21 n1  case1  ndT2  d r refl)
  (ruleTrans (bm n21 n2  case2  ndT3  d r refl)
  (ruleTrans (bm n21 n3  case3  ndT4  d r refl)
  (ruleTrans (bm n21 n4  case4  ndT5  d r refl)
  (ruleTrans (bm n21 n5  case5  ndT6  d r refl)
  (ruleTrans (bm n21 n6  case6  ndT7  d r refl)
  (ruleTrans (bm n21 n7  case7  ndT8  d r refl)
  (ruleTrans (bm n21 n8  case8  ndT9  d r refl)
  (ruleTrans (bm n21 n9  case9  ndT10 d r refl)
  (ruleTrans (bm n21 n10 case10 ndT11 d r refl)
  (ruleTrans (bm n21 n11 case11 ndT12 d r refl)
  (ruleTrans (bm n21 n12 case12 ndT13 d r refl)
  (ruleTrans (bm n21 n13 case13 ndT14 d r refl)
  (ruleTrans (bm n21 n14 case14 ndT15 d r refl)
  (ruleTrans (bm n21 n15 case15 ndT16 d r refl)
  (ruleTrans (bm n21 n16 case16 ndT17 d r refl)
  (ruleTrans (bm n21 n17 case17 ndT18 d r refl)
  (ruleTrans (bm n21 n18 case18 ndT19 d r refl)
  (ruleTrans (bm n21 n19 case19 ndT20 d r refl)
  (ruleTrans (bm n21 n20 case20 ndT21 d r refl)
             (bh n21 case21 ndT22 d r)))))))))))))))))))))

-- Tag 22: congR
ndDispatchToCase22 : (data' recs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (natCode n22)) data') recs)
                 (ap2 case22 (ap2 Pair (reify (natCode n22)) data') recs))
ndDispatchToCase22 d r =
  ruleTrans (bm n22 n0  case0  ndT1  d r refl)
  (ruleTrans (bm n22 n1  case1  ndT2  d r refl)
  (ruleTrans (bm n22 n2  case2  ndT3  d r refl)
  (ruleTrans (bm n22 n3  case3  ndT4  d r refl)
  (ruleTrans (bm n22 n4  case4  ndT5  d r refl)
  (ruleTrans (bm n22 n5  case5  ndT6  d r refl)
  (ruleTrans (bm n22 n6  case6  ndT7  d r refl)
  (ruleTrans (bm n22 n7  case7  ndT8  d r refl)
  (ruleTrans (bm n22 n8  case8  ndT9  d r refl)
  (ruleTrans (bm n22 n9  case9  ndT10 d r refl)
  (ruleTrans (bm n22 n10 case10 ndT11 d r refl)
  (ruleTrans (bm n22 n11 case11 ndT12 d r refl)
  (ruleTrans (bm n22 n12 case12 ndT13 d r refl)
  (ruleTrans (bm n22 n13 case13 ndT14 d r refl)
  (ruleTrans (bm n22 n14 case14 ndT15 d r refl)
  (ruleTrans (bm n22 n15 case15 ndT16 d r refl)
  (ruleTrans (bm n22 n16 case16 ndT17 d r refl)
  (ruleTrans (bm n22 n17 case17 ndT18 d r refl)
  (ruleTrans (bm n22 n18 case18 ndT19 d r refl)
  (ruleTrans (bm n22 n19 case19 ndT20 d r refl)
  (ruleTrans (bm n22 n20 case20 ndT21 d r refl)
  (ruleTrans (bm n22 n21 case21 ndT22 d r refl)
             (bh n22 case22 ndT23 d r))))))))))))))))))))))

-- Tag 23: ruleInst
ndDispatchToCase23 : (data' recs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (natCode n23)) data') recs)
                 (ap2 case23 (ap2 Pair (reify (natCode n23)) data') recs))
ndDispatchToCase23 d r =
  ruleTrans (bm n23 n0  case0  ndT1  d r refl)
  (ruleTrans (bm n23 n1  case1  ndT2  d r refl)
  (ruleTrans (bm n23 n2  case2  ndT3  d r refl)
  (ruleTrans (bm n23 n3  case3  ndT4  d r refl)
  (ruleTrans (bm n23 n4  case4  ndT5  d r refl)
  (ruleTrans (bm n23 n5  case5  ndT6  d r refl)
  (ruleTrans (bm n23 n6  case6  ndT7  d r refl)
  (ruleTrans (bm n23 n7  case7  ndT8  d r refl)
  (ruleTrans (bm n23 n8  case8  ndT9  d r refl)
  (ruleTrans (bm n23 n9  case9  ndT10 d r refl)
  (ruleTrans (bm n23 n10 case10 ndT11 d r refl)
  (ruleTrans (bm n23 n11 case11 ndT12 d r refl)
  (ruleTrans (bm n23 n12 case12 ndT13 d r refl)
  (ruleTrans (bm n23 n13 case13 ndT14 d r refl)
  (ruleTrans (bm n23 n14 case14 ndT15 d r refl)
  (ruleTrans (bm n23 n15 case15 ndT16 d r refl)
  (ruleTrans (bm n23 n16 case16 ndT17 d r refl)
  (ruleTrans (bm n23 n17 case17 ndT18 d r refl)
  (ruleTrans (bm n23 n18 case18 ndT19 d r refl)
  (ruleTrans (bm n23 n19 case19 ndT20 d r refl)
  (ruleTrans (bm n23 n20 case20 ndT21 d r refl)
  (ruleTrans (bm n23 n21 case21 ndT22 d r refl)
  (ruleTrans (bm n23 n22 case22 ndT23 d r refl)
             (bh n23 case23 ndT24 d r)))))))))))))))))))))))

-- Tag 24: ruleF
ndDispatchToCase24 : (data' recs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (natCode n24)) data') recs)
                 (ap2 case24 (ap2 Pair (reify (natCode n24)) data') recs))
ndDispatchToCase24 d r =
  ruleTrans (bm n24 n0  case0  ndT1  d r refl)
  (ruleTrans (bm n24 n1  case1  ndT2  d r refl)
  (ruleTrans (bm n24 n2  case2  ndT3  d r refl)
  (ruleTrans (bm n24 n3  case3  ndT4  d r refl)
  (ruleTrans (bm n24 n4  case4  ndT5  d r refl)
  (ruleTrans (bm n24 n5  case5  ndT6  d r refl)
  (ruleTrans (bm n24 n6  case6  ndT7  d r refl)
  (ruleTrans (bm n24 n7  case7  ndT8  d r refl)
  (ruleTrans (bm n24 n8  case8  ndT9  d r refl)
  (ruleTrans (bm n24 n9  case9  ndT10 d r refl)
  (ruleTrans (bm n24 n10 case10 ndT11 d r refl)
  (ruleTrans (bm n24 n11 case11 ndT12 d r refl)
  (ruleTrans (bm n24 n12 case12 ndT13 d r refl)
  (ruleTrans (bm n24 n13 case13 ndT14 d r refl)
  (ruleTrans (bm n24 n14 case14 ndT15 d r refl)
  (ruleTrans (bm n24 n15 case15 ndT16 d r refl)
  (ruleTrans (bm n24 n16 case16 ndT17 d r refl)
  (ruleTrans (bm n24 n17 case17 ndT18 d r refl)
  (ruleTrans (bm n24 n18 case18 ndT19 d r refl)
  (ruleTrans (bm n24 n19 case19 ndT20 d r refl)
  (ruleTrans (bm n24 n20 case20 ndT21 d r refl)
  (ruleTrans (bm n24 n21 case21 ndT22 d r refl)
  (ruleTrans (bm n24 n22 case22 ndT23 d r refl)
  (ruleTrans (bm n24 n23 case23 ndT24 d r refl)
             (bh n24 case24 ndT25 d r))))))))))))))))))))))))

-- Tag 25: axKT
ndDispatchToCase25 : (data' recs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (natCode n25)) data') recs)
                 (ap2 case25 (ap2 Pair (reify (natCode n25)) data') recs))
ndDispatchToCase25 d r =
  ruleTrans (bm n25 n0  case0  ndT1  d r refl)
  (ruleTrans (bm n25 n1  case1  ndT2  d r refl)
  (ruleTrans (bm n25 n2  case2  ndT3  d r refl)
  (ruleTrans (bm n25 n3  case3  ndT4  d r refl)
  (ruleTrans (bm n25 n4  case4  ndT5  d r refl)
  (ruleTrans (bm n25 n5  case5  ndT6  d r refl)
  (ruleTrans (bm n25 n6  case6  ndT7  d r refl)
  (ruleTrans (bm n25 n7  case7  ndT8  d r refl)
  (ruleTrans (bm n25 n8  case8  ndT9  d r refl)
  (ruleTrans (bm n25 n9  case9  ndT10 d r refl)
  (ruleTrans (bm n25 n10 case10 ndT11 d r refl)
  (ruleTrans (bm n25 n11 case11 ndT12 d r refl)
  (ruleTrans (bm n25 n12 case12 ndT13 d r refl)
  (ruleTrans (bm n25 n13 case13 ndT14 d r refl)
  (ruleTrans (bm n25 n14 case14 ndT15 d r refl)
  (ruleTrans (bm n25 n15 case15 ndT16 d r refl)
  (ruleTrans (bm n25 n16 case16 ndT17 d r refl)
  (ruleTrans (bm n25 n17 case17 ndT18 d r refl)
  (ruleTrans (bm n25 n18 case18 ndT19 d r refl)
  (ruleTrans (bm n25 n19 case19 ndT20 d r refl)
  (ruleTrans (bm n25 n20 case20 ndT21 d r refl)
  (ruleTrans (bm n25 n21 case21 ndT22 d r refl)
  (ruleTrans (bm n25 n22 case22 ndT23 d r refl)
  (ruleTrans (bm n25 n23 case23 ndT24 d r refl)
  (ruleTrans (bm n25 n24 case24 ndT25 d r refl)
             (bh n25 case25 ndT26 d r)))))))))))))))))))))))))
