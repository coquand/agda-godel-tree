{-# OPTIONS --safe --without-K --exact-split #-}

module Guard.ThFunTForCases0 where

open import Guard.Base
open import Guard.Term
open import Guard.ThFunTForDefs

------------------------------------------------------------------------
-- Cases 0-3: axI, axFst, axSnd, axConst
-- These take (orig, recs) where orig = Pair(tag, Pair(a, b))
-- and return the coded equation.

-- Case 0: axI. data: a=tCode, b=lf.
-- thFun result: nd(mkAp1(codeF1 I, a), a) = Pair(Pair(reify tagAp1, Pair(codeIF, a)), a)
private
  codeIF : Term
  codeIF = reify (codeF1 I)

  pairCF : Term
  pairCF = reify (codeF2 Pair)

  constCF : Term
  constCF = reify (codeF2 Const)

case0 : Fun2
case0 = mkEqF (mkAp1F (kF2 codeIF) origA) origA

-- Case 1: axFst. data: a=aCode, b=bCode.
-- thFun: nd(mkAp1(codeFst, mkAp2(codePair, a, b)), a)
private
  codeFstF : Term
  codeFstF = reify (codeF1 Fst)

case1 : Fun2
case1 = mkEqF (mkAp1F (kF2 codeFstF) (mkAp2F (kF2 pairCF) origA origB)) origA

-- Case 2: axSnd. data: a=aCode, b=bCode.
-- thFun: nd(mkAp1(codeSnd, mkAp2(codePair, a, b)), b)
private
  codeSndF : Term
  codeSndF = reify (codeF1 Snd)

case2 : Fun2
case2 = mkEqF (mkAp1F (kF2 codeSndF) (mkAp2F (kF2 pairCF) origA origB)) origB

-- Case 3: axConst. data: a=aCode, b=bCode.
-- thFun: nd(mkAp2(codeConst, a, b), a)
case3 : Fun2
case3 = mkEqF (mkAp2F (kF2 constCF) origA origB) origA
