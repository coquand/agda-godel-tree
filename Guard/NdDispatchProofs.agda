{-# OPTIONS --safe --without-K --exact-split #-}

module Guard.NdDispatchProofs where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.ThFunTFor
open import Guard.ThFunTForDefs
open import Guard.ThFunTForCases0
open import Guard.ThFunTForCases1
open import Guard.ThFunTForCases2
open import Guard.ThFunTForCases3
open import Guard.ThFunTForCorrectDefs

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

private
  miss : (k n : Nat) (caseN tail : Fun2) (d r : Term) -> {hyp : Equation} ->
    Eq (natEq k n) false ->
    Deriv hyp (eqn (ap2 (branch (tagCheck n) caseN tail) (ap2 Pair (reify (natCode k)) d) r)
                   (ap2 tail (ap2 Pair (reify (natCode k)) d) r))
  miss = ndBranchMiss

  hit : (k : Nat) (caseK tail : Fun2) (d r : Term) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap2 (branch (tagCheck k) caseK tail) (ap2 Pair (reify (natCode k)) d) r)
                   (ap2 caseK (ap2 Pair (reify (natCode k)) d) r))
  hit = ndBranchHit

ndDisp0 : (d r : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (natCode n0)) d) r)
                 (ap2 case0 (ap2 Pair (reify (natCode n0)) d) r))
ndDisp0 d r = hit n0 case0 ndT1 d r

ndDisp1 : (d r : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (natCode n1)) d) r)
                 (ap2 case1 (ap2 Pair (reify (natCode n1)) d) r))
ndDisp1 d r =
  ruleTrans (miss n1 n0 case0 ndT1 d r refl)
  (hit n1 case1 ndT2 d r)

ndDisp2 : (d r : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (natCode n2)) d) r)
                 (ap2 case2 (ap2 Pair (reify (natCode n2)) d) r))
ndDisp2 d r =
  ruleTrans (miss n2 n0 case0 ndT1 d r refl)
  (ruleTrans (miss n2 n1 case1 ndT2 d r refl) (hit n2 case2 ndT3 d r))

ndDisp3 : (d r : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (natCode n3)) d) r)
                 (ap2 case3 (ap2 Pair (reify (natCode n3)) d) r))
ndDisp3 d r =
  ruleTrans (miss n3 n0 case0 ndT1 d r refl)
  (ruleTrans (miss n3 n1 case1 ndT2 d r refl) (ruleTrans (miss n3 n2 case2 ndT3 d r refl) (hit n3 case3 ndT4 d r)))

ndDisp4 : (d r : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (natCode n4)) d) r)
                 (ap2 case4 (ap2 Pair (reify (natCode n4)) d) r))
ndDisp4 d r =
  ruleTrans (miss n4 n0 case0 ndT1 d r refl)
  (ruleTrans (miss n4 n1 case1 ndT2 d r refl) (ruleTrans (miss n4 n2 case2 ndT3 d r refl) (ruleTrans (miss n4 n3 case3 ndT4 d r refl) (hit n4 case4 ndT5 d r))))

ndDisp5 : (d r : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (natCode n5)) d) r)
                 (ap2 case5 (ap2 Pair (reify (natCode n5)) d) r))
ndDisp5 d r =
  ruleTrans (miss n5 n0 case0 ndT1 d r refl)
  (ruleTrans (miss n5 n1 case1 ndT2 d r refl) (ruleTrans (miss n5 n2 case2 ndT3 d r refl) (ruleTrans (miss n5 n3 case3 ndT4 d r refl) (ruleTrans (miss n5 n4 case4 ndT5 d r refl) (hit n5 case5 ndT6 d r)))))

ndDisp6 : (d r : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (natCode n6)) d) r)
                 (ap2 case6 (ap2 Pair (reify (natCode n6)) d) r))
ndDisp6 d r =
  ruleTrans (miss n6 n0 case0 ndT1 d r refl)
  (ruleTrans (miss n6 n1 case1 ndT2 d r refl) (ruleTrans (miss n6 n2 case2 ndT3 d r refl) (ruleTrans (miss n6 n3 case3 ndT4 d r refl) (ruleTrans (miss n6 n4 case4 ndT5 d r refl) (ruleTrans (miss n6 n5 case5 ndT6 d r refl) (hit n6 case6 ndT7 d r))))))

ndDisp7 : (d r : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (natCode n7)) d) r)
                 (ap2 case7 (ap2 Pair (reify (natCode n7)) d) r))
ndDisp7 d r =
  ruleTrans (miss n7 n0 case0 ndT1 d r refl)
  (ruleTrans (miss n7 n1 case1 ndT2 d r refl) (ruleTrans (miss n7 n2 case2 ndT3 d r refl) (ruleTrans (miss n7 n3 case3 ndT4 d r refl) (ruleTrans (miss n7 n4 case4 ndT5 d r refl) (ruleTrans (miss n7 n5 case5 ndT6 d r refl) (ruleTrans (miss n7 n6 case6 ndT7 d r refl) (hit n7 case7 ndT8 d r)))))))

ndDisp8 : (d r : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (natCode n8)) d) r)
                 (ap2 case8 (ap2 Pair (reify (natCode n8)) d) r))
ndDisp8 d r =
  ruleTrans (miss n8 n0 case0 ndT1 d r refl)
  (ruleTrans (miss n8 n1 case1 ndT2 d r refl) (ruleTrans (miss n8 n2 case2 ndT3 d r refl) (ruleTrans (miss n8 n3 case3 ndT4 d r refl) (ruleTrans (miss n8 n4 case4 ndT5 d r refl) (ruleTrans (miss n8 n5 case5 ndT6 d r refl) (ruleTrans (miss n8 n6 case6 ndT7 d r refl) (ruleTrans (miss n8 n7 case7 ndT8 d r refl) (hit n8 case8 ndT9 d r))))))))

ndDisp9 : (d r : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (natCode n9)) d) r)
                 (ap2 case9 (ap2 Pair (reify (natCode n9)) d) r))
ndDisp9 d r =
  ruleTrans (miss n9 n0 case0 ndT1 d r refl)
  (ruleTrans (miss n9 n1 case1 ndT2 d r refl) (ruleTrans (miss n9 n2 case2 ndT3 d r refl) (ruleTrans (miss n9 n3 case3 ndT4 d r refl) (ruleTrans (miss n9 n4 case4 ndT5 d r refl) (ruleTrans (miss n9 n5 case5 ndT6 d r refl) (ruleTrans (miss n9 n6 case6 ndT7 d r refl) (ruleTrans (miss n9 n7 case7 ndT8 d r refl) (ruleTrans (miss n9 n8 case8 ndT9 d r refl) (hit n9 case9 ndT10 d r)))))))))

ndDisp10 : (d r : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (natCode n10)) d) r)
                 (ap2 case10 (ap2 Pair (reify (natCode n10)) d) r))
ndDisp10 d r =
  ruleTrans (miss n10 n0 case0 ndT1 d r refl)
  (ruleTrans (miss n10 n1 case1 ndT2 d r refl) (ruleTrans (miss n10 n2 case2 ndT3 d r refl) (ruleTrans (miss n10 n3 case3 ndT4 d r refl) (ruleTrans (miss n10 n4 case4 ndT5 d r refl) (ruleTrans (miss n10 n5 case5 ndT6 d r refl) (ruleTrans (miss n10 n6 case6 ndT7 d r refl) (ruleTrans (miss n10 n7 case7 ndT8 d r refl) (ruleTrans (miss n10 n8 case8 ndT9 d r refl) (ruleTrans (miss n10 n9 case9 ndT10 d r refl) (hit n10 case10 ndT11 d r))))))))))

ndDisp11 : (d r : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (natCode n11)) d) r)
                 (ap2 case11 (ap2 Pair (reify (natCode n11)) d) r))
ndDisp11 d r =
  ruleTrans (miss n11 n0 case0 ndT1 d r refl)
  (ruleTrans (miss n11 n1 case1 ndT2 d r refl) (ruleTrans (miss n11 n2 case2 ndT3 d r refl) (ruleTrans (miss n11 n3 case3 ndT4 d r refl) (ruleTrans (miss n11 n4 case4 ndT5 d r refl) (ruleTrans (miss n11 n5 case5 ndT6 d r refl) (ruleTrans (miss n11 n6 case6 ndT7 d r refl) (ruleTrans (miss n11 n7 case7 ndT8 d r refl) (ruleTrans (miss n11 n8 case8 ndT9 d r refl) (ruleTrans (miss n11 n9 case9 ndT10 d r refl) (ruleTrans (miss n11 n10 case10 ndT11 d r refl) (hit n11 case11 ndT12 d r)))))))))))

ndDisp12 : (d r : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (natCode n12)) d) r)
                 (ap2 case12 (ap2 Pair (reify (natCode n12)) d) r))
ndDisp12 d r =
  ruleTrans (miss n12 n0 case0 ndT1 d r refl)
  (ruleTrans (miss n12 n1 case1 ndT2 d r refl) (ruleTrans (miss n12 n2 case2 ndT3 d r refl) (ruleTrans (miss n12 n3 case3 ndT4 d r refl) (ruleTrans (miss n12 n4 case4 ndT5 d r refl) (ruleTrans (miss n12 n5 case5 ndT6 d r refl) (ruleTrans (miss n12 n6 case6 ndT7 d r refl) (ruleTrans (miss n12 n7 case7 ndT8 d r refl) (ruleTrans (miss n12 n8 case8 ndT9 d r refl) (ruleTrans (miss n12 n9 case9 ndT10 d r refl) (ruleTrans (miss n12 n10 case10 ndT11 d r refl) (ruleTrans (miss n12 n11 case11 ndT12 d r refl) (hit n12 case12 ndT13 d r))))))))))))

ndDisp13 : (d r : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (natCode n13)) d) r)
                 (ap2 case13 (ap2 Pair (reify (natCode n13)) d) r))
ndDisp13 d r =
  ruleTrans (miss n13 n0 case0 ndT1 d r refl)
  (ruleTrans (miss n13 n1 case1 ndT2 d r refl) (ruleTrans (miss n13 n2 case2 ndT3 d r refl) (ruleTrans (miss n13 n3 case3 ndT4 d r refl) (ruleTrans (miss n13 n4 case4 ndT5 d r refl) (ruleTrans (miss n13 n5 case5 ndT6 d r refl) (ruleTrans (miss n13 n6 case6 ndT7 d r refl) (ruleTrans (miss n13 n7 case7 ndT8 d r refl) (ruleTrans (miss n13 n8 case8 ndT9 d r refl) (ruleTrans (miss n13 n9 case9 ndT10 d r refl) (ruleTrans (miss n13 n10 case10 ndT11 d r refl) (ruleTrans (miss n13 n11 case11 ndT12 d r refl) (ruleTrans (miss n13 n12 case12 ndT13 d r refl) (hit n13 case13 ndT14 d r)))))))))))))

ndDisp14 : (d r : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (natCode n14)) d) r)
                 (ap2 case14 (ap2 Pair (reify (natCode n14)) d) r))
ndDisp14 d r =
  ruleTrans (miss n14 n0 case0 ndT1 d r refl)
  (ruleTrans (miss n14 n1 case1 ndT2 d r refl) (ruleTrans (miss n14 n2 case2 ndT3 d r refl) (ruleTrans (miss n14 n3 case3 ndT4 d r refl) (ruleTrans (miss n14 n4 case4 ndT5 d r refl) (ruleTrans (miss n14 n5 case5 ndT6 d r refl) (ruleTrans (miss n14 n6 case6 ndT7 d r refl) (ruleTrans (miss n14 n7 case7 ndT8 d r refl) (ruleTrans (miss n14 n8 case8 ndT9 d r refl) (ruleTrans (miss n14 n9 case9 ndT10 d r refl) (ruleTrans (miss n14 n10 case10 ndT11 d r refl) (ruleTrans (miss n14 n11 case11 ndT12 d r refl) (ruleTrans (miss n14 n12 case12 ndT13 d r refl) (ruleTrans (miss n14 n13 case13 ndT14 d r refl) (hit n14 case14 ndT15 d r))))))))))))))

ndDisp15 : (d r : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (natCode n15)) d) r)
                 (ap2 case15 (ap2 Pair (reify (natCode n15)) d) r))
ndDisp15 d r =
  ruleTrans (miss n15 n0 case0 ndT1 d r refl)
  (ruleTrans (miss n15 n1 case1 ndT2 d r refl) (ruleTrans (miss n15 n2 case2 ndT3 d r refl) (ruleTrans (miss n15 n3 case3 ndT4 d r refl) (ruleTrans (miss n15 n4 case4 ndT5 d r refl) (ruleTrans (miss n15 n5 case5 ndT6 d r refl) (ruleTrans (miss n15 n6 case6 ndT7 d r refl) (ruleTrans (miss n15 n7 case7 ndT8 d r refl) (ruleTrans (miss n15 n8 case8 ndT9 d r refl) (ruleTrans (miss n15 n9 case9 ndT10 d r refl) (ruleTrans (miss n15 n10 case10 ndT11 d r refl) (ruleTrans (miss n15 n11 case11 ndT12 d r refl) (ruleTrans (miss n15 n12 case12 ndT13 d r refl) (ruleTrans (miss n15 n13 case13 ndT14 d r refl) (ruleTrans (miss n15 n14 case14 ndT15 d r refl) (hit n15 case15 ndT16 d r)))))))))))))))

ndDisp16 : (d r : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (natCode n16)) d) r)
                 (ap2 case16 (ap2 Pair (reify (natCode n16)) d) r))
ndDisp16 d r =
  ruleTrans (miss n16 n0 case0 ndT1 d r refl)
  (ruleTrans (miss n16 n1 case1 ndT2 d r refl) (ruleTrans (miss n16 n2 case2 ndT3 d r refl) (ruleTrans (miss n16 n3 case3 ndT4 d r refl) (ruleTrans (miss n16 n4 case4 ndT5 d r refl) (ruleTrans (miss n16 n5 case5 ndT6 d r refl) (ruleTrans (miss n16 n6 case6 ndT7 d r refl) (ruleTrans (miss n16 n7 case7 ndT8 d r refl) (ruleTrans (miss n16 n8 case8 ndT9 d r refl) (ruleTrans (miss n16 n9 case9 ndT10 d r refl) (ruleTrans (miss n16 n10 case10 ndT11 d r refl) (ruleTrans (miss n16 n11 case11 ndT12 d r refl) (ruleTrans (miss n16 n12 case12 ndT13 d r refl) (ruleTrans (miss n16 n13 case13 ndT14 d r refl) (ruleTrans (miss n16 n14 case14 ndT15 d r refl) (ruleTrans (miss n16 n15 case15 ndT16 d r refl) (hit n16 case16 ndT17 d r))))))))))))))))

ndDisp17 : (d r : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (natCode n17)) d) r)
                 (ap2 case17 (ap2 Pair (reify (natCode n17)) d) r))
ndDisp17 d r =
  ruleTrans (miss n17 n0 case0 ndT1 d r refl)
  (ruleTrans (miss n17 n1 case1 ndT2 d r refl) (ruleTrans (miss n17 n2 case2 ndT3 d r refl) (ruleTrans (miss n17 n3 case3 ndT4 d r refl) (ruleTrans (miss n17 n4 case4 ndT5 d r refl) (ruleTrans (miss n17 n5 case5 ndT6 d r refl) (ruleTrans (miss n17 n6 case6 ndT7 d r refl) (ruleTrans (miss n17 n7 case7 ndT8 d r refl) (ruleTrans (miss n17 n8 case8 ndT9 d r refl) (ruleTrans (miss n17 n9 case9 ndT10 d r refl) (ruleTrans (miss n17 n10 case10 ndT11 d r refl) (ruleTrans (miss n17 n11 case11 ndT12 d r refl) (ruleTrans (miss n17 n12 case12 ndT13 d r refl) (ruleTrans (miss n17 n13 case13 ndT14 d r refl) (ruleTrans (miss n17 n14 case14 ndT15 d r refl) (ruleTrans (miss n17 n15 case15 ndT16 d r refl) (ruleTrans (miss n17 n16 case16 ndT17 d r refl) (hit n17 case17 ndT18 d r)))))))))))))))))

ndDisp18 : (d r : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (natCode n18)) d) r)
                 (ap2 case18 (ap2 Pair (reify (natCode n18)) d) r))
ndDisp18 d r =
  ruleTrans (miss n18 n0 case0 ndT1 d r refl)
  (ruleTrans (miss n18 n1 case1 ndT2 d r refl) (ruleTrans (miss n18 n2 case2 ndT3 d r refl) (ruleTrans (miss n18 n3 case3 ndT4 d r refl) (ruleTrans (miss n18 n4 case4 ndT5 d r refl) (ruleTrans (miss n18 n5 case5 ndT6 d r refl) (ruleTrans (miss n18 n6 case6 ndT7 d r refl) (ruleTrans (miss n18 n7 case7 ndT8 d r refl) (ruleTrans (miss n18 n8 case8 ndT9 d r refl) (ruleTrans (miss n18 n9 case9 ndT10 d r refl) (ruleTrans (miss n18 n10 case10 ndT11 d r refl) (ruleTrans (miss n18 n11 case11 ndT12 d r refl) (ruleTrans (miss n18 n12 case12 ndT13 d r refl) (ruleTrans (miss n18 n13 case13 ndT14 d r refl) (ruleTrans (miss n18 n14 case14 ndT15 d r refl) (ruleTrans (miss n18 n15 case15 ndT16 d r refl) (ruleTrans (miss n18 n16 case16 ndT17 d r refl) (ruleTrans (miss n18 n17 case17 ndT18 d r refl) (hit n18 case18 ndT19 d r))))))))))))))))))

ndDisp19 : (d r : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (natCode n19)) d) r)
                 (ap2 case19 (ap2 Pair (reify (natCode n19)) d) r))
ndDisp19 d r =
  ruleTrans (miss n19 n0 case0 ndT1 d r refl)
  (ruleTrans (miss n19 n1 case1 ndT2 d r refl) (ruleTrans (miss n19 n2 case2 ndT3 d r refl) (ruleTrans (miss n19 n3 case3 ndT4 d r refl) (ruleTrans (miss n19 n4 case4 ndT5 d r refl) (ruleTrans (miss n19 n5 case5 ndT6 d r refl) (ruleTrans (miss n19 n6 case6 ndT7 d r refl) (ruleTrans (miss n19 n7 case7 ndT8 d r refl) (ruleTrans (miss n19 n8 case8 ndT9 d r refl) (ruleTrans (miss n19 n9 case9 ndT10 d r refl) (ruleTrans (miss n19 n10 case10 ndT11 d r refl) (ruleTrans (miss n19 n11 case11 ndT12 d r refl) (ruleTrans (miss n19 n12 case12 ndT13 d r refl) (ruleTrans (miss n19 n13 case13 ndT14 d r refl) (ruleTrans (miss n19 n14 case14 ndT15 d r refl) (ruleTrans (miss n19 n15 case15 ndT16 d r refl) (ruleTrans (miss n19 n16 case16 ndT17 d r refl) (ruleTrans (miss n19 n17 case17 ndT18 d r refl) (ruleTrans (miss n19 n18 case18 ndT19 d r refl) (hit n19 case19 ndT20 d r)))))))))))))))))))

ndDisp20 : (d r : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (natCode n20)) d) r)
                 (ap2 case20 (ap2 Pair (reify (natCode n20)) d) r))
ndDisp20 d r =
  ruleTrans (miss n20 n0 case0 ndT1 d r refl)
  (ruleTrans (miss n20 n1 case1 ndT2 d r refl) (ruleTrans (miss n20 n2 case2 ndT3 d r refl) (ruleTrans (miss n20 n3 case3 ndT4 d r refl) (ruleTrans (miss n20 n4 case4 ndT5 d r refl) (ruleTrans (miss n20 n5 case5 ndT6 d r refl) (ruleTrans (miss n20 n6 case6 ndT7 d r refl) (ruleTrans (miss n20 n7 case7 ndT8 d r refl) (ruleTrans (miss n20 n8 case8 ndT9 d r refl) (ruleTrans (miss n20 n9 case9 ndT10 d r refl) (ruleTrans (miss n20 n10 case10 ndT11 d r refl) (ruleTrans (miss n20 n11 case11 ndT12 d r refl) (ruleTrans (miss n20 n12 case12 ndT13 d r refl) (ruleTrans (miss n20 n13 case13 ndT14 d r refl) (ruleTrans (miss n20 n14 case14 ndT15 d r refl) (ruleTrans (miss n20 n15 case15 ndT16 d r refl) (ruleTrans (miss n20 n16 case16 ndT17 d r refl) (ruleTrans (miss n20 n17 case17 ndT18 d r refl) (ruleTrans (miss n20 n18 case18 ndT19 d r refl) (ruleTrans (miss n20 n19 case19 ndT20 d r refl) (hit n20 case20 ndT21 d r))))))))))))))))))))

ndDisp21 : (d r : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (natCode n21)) d) r)
                 (ap2 case21 (ap2 Pair (reify (natCode n21)) d) r))
ndDisp21 d r =
  ruleTrans (miss n21 n0 case0 ndT1 d r refl)
  (ruleTrans (miss n21 n1 case1 ndT2 d r refl) (ruleTrans (miss n21 n2 case2 ndT3 d r refl) (ruleTrans (miss n21 n3 case3 ndT4 d r refl) (ruleTrans (miss n21 n4 case4 ndT5 d r refl) (ruleTrans (miss n21 n5 case5 ndT6 d r refl) (ruleTrans (miss n21 n6 case6 ndT7 d r refl) (ruleTrans (miss n21 n7 case7 ndT8 d r refl) (ruleTrans (miss n21 n8 case8 ndT9 d r refl) (ruleTrans (miss n21 n9 case9 ndT10 d r refl) (ruleTrans (miss n21 n10 case10 ndT11 d r refl) (ruleTrans (miss n21 n11 case11 ndT12 d r refl) (ruleTrans (miss n21 n12 case12 ndT13 d r refl) (ruleTrans (miss n21 n13 case13 ndT14 d r refl) (ruleTrans (miss n21 n14 case14 ndT15 d r refl) (ruleTrans (miss n21 n15 case15 ndT16 d r refl) (ruleTrans (miss n21 n16 case16 ndT17 d r refl) (ruleTrans (miss n21 n17 case17 ndT18 d r refl) (ruleTrans (miss n21 n18 case18 ndT19 d r refl) (ruleTrans (miss n21 n19 case19 ndT20 d r refl) (ruleTrans (miss n21 n20 case20 ndT21 d r refl) (hit n21 case21 ndT22 d r)))))))))))))))))))))

ndDisp22 : (d r : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (natCode n22)) d) r)
                 (ap2 case22 (ap2 Pair (reify (natCode n22)) d) r))
ndDisp22 d r =
  ruleTrans (miss n22 n0 case0 ndT1 d r refl)
  (ruleTrans (miss n22 n1 case1 ndT2 d r refl) (ruleTrans (miss n22 n2 case2 ndT3 d r refl) (ruleTrans (miss n22 n3 case3 ndT4 d r refl) (ruleTrans (miss n22 n4 case4 ndT5 d r refl) (ruleTrans (miss n22 n5 case5 ndT6 d r refl) (ruleTrans (miss n22 n6 case6 ndT7 d r refl) (ruleTrans (miss n22 n7 case7 ndT8 d r refl) (ruleTrans (miss n22 n8 case8 ndT9 d r refl) (ruleTrans (miss n22 n9 case9 ndT10 d r refl) (ruleTrans (miss n22 n10 case10 ndT11 d r refl) (ruleTrans (miss n22 n11 case11 ndT12 d r refl) (ruleTrans (miss n22 n12 case12 ndT13 d r refl) (ruleTrans (miss n22 n13 case13 ndT14 d r refl) (ruleTrans (miss n22 n14 case14 ndT15 d r refl) (ruleTrans (miss n22 n15 case15 ndT16 d r refl) (ruleTrans (miss n22 n16 case16 ndT17 d r refl) (ruleTrans (miss n22 n17 case17 ndT18 d r refl) (ruleTrans (miss n22 n18 case18 ndT19 d r refl) (ruleTrans (miss n22 n19 case19 ndT20 d r refl) (ruleTrans (miss n22 n20 case20 ndT21 d r refl) (ruleTrans (miss n22 n21 case21 ndT22 d r refl) (hit n22 case22 ndT23 d r))))))))))))))))))))))

ndDisp23 : (d r : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (natCode n23)) d) r)
                 (ap2 case23 (ap2 Pair (reify (natCode n23)) d) r))
ndDisp23 d r =
  ruleTrans (miss n23 n0 case0 ndT1 d r refl)
  (ruleTrans (miss n23 n1 case1 ndT2 d r refl) (ruleTrans (miss n23 n2 case2 ndT3 d r refl) (ruleTrans (miss n23 n3 case3 ndT4 d r refl) (ruleTrans (miss n23 n4 case4 ndT5 d r refl) (ruleTrans (miss n23 n5 case5 ndT6 d r refl) (ruleTrans (miss n23 n6 case6 ndT7 d r refl) (ruleTrans (miss n23 n7 case7 ndT8 d r refl) (ruleTrans (miss n23 n8 case8 ndT9 d r refl) (ruleTrans (miss n23 n9 case9 ndT10 d r refl) (ruleTrans (miss n23 n10 case10 ndT11 d r refl) (ruleTrans (miss n23 n11 case11 ndT12 d r refl) (ruleTrans (miss n23 n12 case12 ndT13 d r refl) (ruleTrans (miss n23 n13 case13 ndT14 d r refl) (ruleTrans (miss n23 n14 case14 ndT15 d r refl) (ruleTrans (miss n23 n15 case15 ndT16 d r refl) (ruleTrans (miss n23 n16 case16 ndT17 d r refl) (ruleTrans (miss n23 n17 case17 ndT18 d r refl) (ruleTrans (miss n23 n18 case18 ndT19 d r refl) (ruleTrans (miss n23 n19 case19 ndT20 d r refl) (ruleTrans (miss n23 n20 case20 ndT21 d r refl) (ruleTrans (miss n23 n21 case21 ndT22 d r refl) (ruleTrans (miss n23 n22 case22 ndT23 d r refl) (hit n23 case23 ndT24 d r)))))))))))))))))))))))

ndDisp24 : (d r : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (natCode n24)) d) r)
                 (ap2 case24 (ap2 Pair (reify (natCode n24)) d) r))
ndDisp24 d r =
  ruleTrans (miss n24 n0 case0 ndT1 d r refl)
  (ruleTrans (miss n24 n1 case1 ndT2 d r refl) (ruleTrans (miss n24 n2 case2 ndT3 d r refl) (ruleTrans (miss n24 n3 case3 ndT4 d r refl) (ruleTrans (miss n24 n4 case4 ndT5 d r refl) (ruleTrans (miss n24 n5 case5 ndT6 d r refl) (ruleTrans (miss n24 n6 case6 ndT7 d r refl) (ruleTrans (miss n24 n7 case7 ndT8 d r refl) (ruleTrans (miss n24 n8 case8 ndT9 d r refl) (ruleTrans (miss n24 n9 case9 ndT10 d r refl) (ruleTrans (miss n24 n10 case10 ndT11 d r refl) (ruleTrans (miss n24 n11 case11 ndT12 d r refl) (ruleTrans (miss n24 n12 case12 ndT13 d r refl) (ruleTrans (miss n24 n13 case13 ndT14 d r refl) (ruleTrans (miss n24 n14 case14 ndT15 d r refl) (ruleTrans (miss n24 n15 case15 ndT16 d r refl) (ruleTrans (miss n24 n16 case16 ndT17 d r refl) (ruleTrans (miss n24 n17 case17 ndT18 d r refl) (ruleTrans (miss n24 n18 case18 ndT19 d r refl) (ruleTrans (miss n24 n19 case19 ndT20 d r refl) (ruleTrans (miss n24 n20 case20 ndT21 d r refl) (ruleTrans (miss n24 n21 case21 ndT22 d r refl) (ruleTrans (miss n24 n22 case22 ndT23 d r refl) (ruleTrans (miss n24 n23 case23 ndT24 d r refl) (hit n24 case24 ndT25 d r))))))))))))))))))))))))

ndDisp25 : (d r : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 ndDispatch (ap2 Pair (reify (natCode n25)) d) r)
                 (ap2 case25 (ap2 Pair (reify (natCode n25)) d) r))
ndDisp25 d r =
  ruleTrans (miss n25 n0 case0 ndT1 d r refl)
  (ruleTrans (miss n25 n1 case1 ndT2 d r refl) (ruleTrans (miss n25 n2 case2 ndT3 d r refl) (ruleTrans (miss n25 n3 case3 ndT4 d r refl) (ruleTrans (miss n25 n4 case4 ndT5 d r refl) (ruleTrans (miss n25 n5 case5 ndT6 d r refl) (ruleTrans (miss n25 n6 case6 ndT7 d r refl) (ruleTrans (miss n25 n7 case7 ndT8 d r refl) (ruleTrans (miss n25 n8 case8 ndT9 d r refl) (ruleTrans (miss n25 n9 case9 ndT10 d r refl) (ruleTrans (miss n25 n10 case10 ndT11 d r refl) (ruleTrans (miss n25 n11 case11 ndT12 d r refl) (ruleTrans (miss n25 n12 case12 ndT13 d r refl) (ruleTrans (miss n25 n13 case13 ndT14 d r refl) (ruleTrans (miss n25 n14 case14 ndT15 d r refl) (ruleTrans (miss n25 n15 case15 ndT16 d r refl) (ruleTrans (miss n25 n16 case16 ndT17 d r refl) (ruleTrans (miss n25 n17 case17 ndT18 d r refl) (ruleTrans (miss n25 n18 case18 ndT19 d r refl) (ruleTrans (miss n25 n19 case19 ndT20 d r refl) (ruleTrans (miss n25 n20 case20 ndT21 d r refl) (ruleTrans (miss n25 n21 case21 ndT22 d r refl) (ruleTrans (miss n25 n22 case22 ndT23 d r refl) (ruleTrans (miss n25 n23 case23 ndT24 d r refl) (ruleTrans (miss n25 n24 case24 ndT25 d r refl) (hit n25 case25 ndT26 d r)))))))))))))))))))))))))

