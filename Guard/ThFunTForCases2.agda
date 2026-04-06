{-# OPTIONS --safe --without-K --exact-split #-}

module Guard.ThFunTForCases2 where

open import Guard.Base
open import Guard.Term
open import Guard.ThFunTForDefs

------------------------------------------------------------------------
-- Cases 9-16: axRecLf, axRecNd, axIfLfL, axIfLfN, axTreeEq*

private
  n26 : Nat ; n26 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))))
  n27 : Nat ; n27 = suc n26
  n28 : Nat ; n28 = suc n27
  n29 : Nat ; n29 = suc n28
  n30 : Nat ; n30 = suc n29
  n31 : Nat ; n31 = suc n30
  oC : Term ; oC = ap2 Pair O O
  pairCF : Term ; pairCF = reify (codeF2 Pair)
  iflfCF : Term ; iflfCF = reify (codeF2 IfLf)
  treeeqCF : Term ; treeeqCF = reify (codeF2 TreeEq)
  reifyTagAp2 : Term ; reifyTagAp2 = ap2 Pair O (ap2 Pair O (ap2 Pair O O))
  oneC : Term ; oneC = ap2 Pair reifyTagAp2 (ap2 Pair pairCF (ap2 Pair (ap2 Pair O O) (ap2 Pair O O)))

  codeRecF : Fun2 -> Fun2 -> Fun2
  codeRecF zF sF = Fan (kF2 (reify (natCode n31))) (Fan zF sF Pair) Pair

-- Case 9: axRecLf. a=zCode, b=sCode.
-- thFun: nd(mkAp1(Rec(z,s), O), z)
case9 : Fun2
case9 = mkEqF (mkAp1F (codeRecF origA origB) (kF2 oC)) origA

-- Case 10: axRecNd. a=zCode, b=nd(sCode, nd(aCode, bCode)).
-- thFun: nd(mkAp1(Rec(z,s), Pair(a,b)),
--           mkAp2(s, Pair(a,b), Pair(mkAp1(Rec(z,s),a), mkAp1(Rec(z,s),b))))
case10 : Fun2
case10 =
  let recF = codeRecF origA origB1
      pairAB = mkAp2F (kF2 pairCF) origB2a origB2b
  in mkEqF (mkAp1F recF pairAB)
           (mkAp2F origB1 pairAB
                   (mkAp2F (kF2 pairCF) (mkAp1F recF origB2a) (mkAp1F recF origB2b)))

-- Case 11: axIfLfL. a=aCode, b=bCode.
-- thFun: nd(mkAp2(IfLf, O, Pair(a,b)), a)
case11 : Fun2
case11 = mkEqF (mkAp2F (kF2 iflfCF) (kF2 oC) (mkAp2F (kF2 pairCF) origA origB)) origA

-- Case 12: axIfLfN. a=xCode, b=nd(yCode, nd(aCode, bCode)).
-- thFun: nd(mkAp2(IfLf, Pair(x,y), Pair(a,b)), b)
case12 : Fun2
case12 = mkEqF (mkAp2F (kF2 iflfCF) (mkAp2F (kF2 pairCF) origA origB1)
                       (mkAp2F (kF2 pairCF) origB2a origB2b))
               origB2b

-- Case 13: axTreeEqLL (handled in thFun for lf payload, skip in nd dispatch)
-- We include a dummy; the lf case is handled separately.
case13 : Fun2
case13 = mkEqF (mkAp2F (kF2 treeeqCF) (kF2 oC) (kF2 oC)) (kF2 oC)

-- Case 14: axTreeEqLN. a=aCode, b=bCode.
-- thFun: nd(mkAp2(TreeEq, O, Pair(a,b)), Pair(O,O))
case14 : Fun2
case14 = mkEqF (mkAp2F (kF2 treeeqCF) (kF2 oC) (mkAp2F (kF2 pairCF) origA origB)) (kF2 oneC)

-- Case 15: axTreeEqNL. a=aCode, b=bCode.
-- thFun: nd(mkAp2(TreeEq, Pair(a,b), O), Pair(O,O))
case15 : Fun2
case15 = mkEqF (mkAp2F (kF2 treeeqCF) (mkAp2F (kF2 pairCF) origA origB) (kF2 oC)) (kF2 oneC)

-- Case 16: axTreeEqNN. a=a1Code, b=nd(a2Code, nd(b1Code, b2Code)).
-- thFun: nd(TreeEq(Pair(a1,a2), Pair(b1,b2)),
--           IfLf(TreeEq(a1,b1), Pair(TreeEq(a2,b2), Pair(O,O))))
case16 : Fun2
case16 = mkEqF
  (mkAp2F (kF2 treeeqCF) (mkAp2F (kF2 pairCF) origA origB1)
                          (mkAp2F (kF2 pairCF) origB2a origB2b))
  (mkAp2F (kF2 iflfCF) (mkAp2F (kF2 treeeqCF) origA origB2a)
                        (mkAp2F (kF2 pairCF) (mkAp2F (kF2 treeeqCF) origB1 origB2b) (kF2 oneC)))
