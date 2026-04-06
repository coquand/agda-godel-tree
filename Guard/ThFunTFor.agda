{-# OPTIONS --safe --without-K --exact-split #-}

module Guard.ThFunTFor where

open import Guard.Base
open import Guard.Term
open import Guard.ThFunTForDefs
open import Guard.ThFunTForCases0
open import Guard.ThFunTForCases1
open import Guard.ThFunTForCases2
open import Guard.ThFunTForCases3

------------------------------------------------------------------------
-- Nat abbreviations (private)

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

  tc : Nat -> Fun2
  tc = tagCheck

------------------------------------------------------------------------
-- ndDispatch tails: ndT k is the dispatch chain starting at branch k.
-- Exported for use in correctness proofs.

ndT26 : Fun2
ndT26 = sndArg2

ndT25 : Fun2
ndT25 = branch (tc n25) case25 ndT26

ndT24 : Fun2
ndT24 = branch (tc n24) case24 ndT25

ndT23 : Fun2
ndT23 = branch (tc n23) case23 ndT24

ndT22 : Fun2
ndT22 = branch (tc n22) case22 ndT23

ndT21 : Fun2
ndT21 = branch (tc n21) case21 ndT22

ndT20 : Fun2
ndT20 = branch (tc n20) case20 ndT21

ndT19 : Fun2
ndT19 = branch (tc n19) case19 ndT20

ndT18 : Fun2
ndT18 = branch (tc n18) case18 ndT19

ndT17 : Fun2
ndT17 = branch (tc n17) case17 ndT18

ndT16 : Fun2
ndT16 = branch (tc n16) case16 ndT17

ndT15 : Fun2
ndT15 = branch (tc n15) case15 ndT16

ndT14 : Fun2
ndT14 = branch (tc n14) case14 ndT15

ndT13 : Fun2
ndT13 = branch (tc n13) case13 ndT14

ndT12 : Fun2
ndT12 = branch (tc n12) case12 ndT13

ndT11 : Fun2
ndT11 = branch (tc n11) case11 ndT12

ndT10 : Fun2
ndT10 = branch (tc n10) case10 ndT11

ndT9 : Fun2
ndT9 = branch (tc n9) case9 ndT10

ndT8 : Fun2
ndT8 = branch (tc n8) case8 ndT9

ndT7 : Fun2
ndT7 = branch (tc n7) case7 ndT8

ndT6 : Fun2
ndT6 = branch (tc n6) case6 ndT7

ndT5 : Fun2
ndT5 = branch (tc n5) case5 ndT6

ndT4 : Fun2
ndT4 = branch (tc n4) case4 ndT5

ndT3 : Fun2
ndT3 = branch (tc n3) case3 ndT4

ndT2 : Fun2
ndT2 = branch (tc n2) case2 ndT3

ndT1 : Fun2
ndT1 = branch (tc n1) case1 ndT2

ndDispatch : Fun2
ndDispatch = branch (tc n0) case0 ndT1

------------------------------------------------------------------------
-- lf-data dispatch

private
  dataIsLf : Fun2
  dataIsLf = Fan (Lift Snd) (kF2 O) TreeEq

  tag13Check : Fun2
  tag13Check = Fan (Lift Fst) (kF2 (reify (natCode n13))) TreeEq

  lfDispatch : Fun2
  lfDispatch = branch tag13Check case13 (kF2 O)

------------------------------------------------------------------------
-- thFunStep : Fun2

thFunStep : Fun2
thFunStep = Fan dataIsLf (Fan lfDispatch ndDispatch Pair) IfLf

------------------------------------------------------------------------
-- thFunTFor : Fun1

thFunTFor : Fun1
thFunTFor = Rec O thFunStep
