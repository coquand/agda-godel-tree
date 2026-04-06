{-# OPTIONS --safe --without-K --exact-split #-}

module Guard.ThFunTForCases1 where

open import Guard.Base
open import Guard.Term
open import Guard.ThFunTForDefs

------------------------------------------------------------------------
-- Cases 4-8: axComp, axComp2, axLift, axPost, axFan
-- Payload: a=first functor code, b=nd(rest...)

private
  n26 : Nat
  n26 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))))
  n27 : Nat ; n27 = suc n26
  n28 : Nat ; n28 = suc n27
  n29 : Nat ; n29 = suc n28
  n30 : Nat ; n30 = suc n29

  codeCompTag : Term
  codeCompTag = reify (natCode n29)

  codeComp2Tag : Term
  codeComp2Tag = reify (natCode n30)

  codeLiftTag : Term
  codeLiftTag = reify (natCode n28)

  codePostTag : Term
  codePostTag = reify (natCode n29)

  codeFanTag : Term
  codeFanTag = reify (natCode n30)

-- Case 4: axComp. a=fCode, b=nd(gCode, tCode).
-- thFun: nd(mkAp1(Comp(f,g), t), mkAp1(f, mkAp1(g, t)))
-- Comp code = nd(natCode 3, nd(f, g))
case4 : Fun2
case4 = mkEqF
  (mkAp1F (Fan (kF2 codeCompTag) (Fan origA origB1 Pair) Pair) origB2)
  (mkAp1F origA (mkAp1F origB1 origB2))

-- Case 5: axComp2. a=hCode, b=nd(fCode, nd(gCode, tCode)).
-- thFun: nd(mkAp1(Comp2(h,f,g), t), mkAp2(h, mkAp1(f,t), mkAp1(g,t)))
case5 : Fun2
case5 = mkEqF
  (mkAp1F (Fan (kF2 codeComp2Tag) (Fan origA (Fan origB1 origB2a Pair) Pair) Pair) origB2b)
  (mkAp2F origA (mkAp1F origB1 origB2b) (mkAp1F origB2a origB2b))

-- Case 6: axLift. a=fCode, b=nd(aCode, bCode).
-- thFun: nd(mkAp2(Lift(f), a, b), mkAp1(f, a))
case6 : Fun2
case6 = mkEqF
  (mkAp2F (Fan (kF2 codeLiftTag) origA Pair) origB1 origB2)
  (mkAp1F origA origB1)

-- Case 7: axPost. a=fCode, b=nd(hCode, nd(aCode, bCode)).
-- thFun: nd(mkAp2(Post(f,h), a, b), mkAp1(f, mkAp2(h, a, b)))
case7 : Fun2
case7 = mkEqF
  (mkAp2F (Fan (kF2 codePostTag) (Fan origA origB1 Pair) Pair) origB2a origB2b)
  (mkAp1F origA (mkAp2F origB1 origB2a origB2b))

-- Case 8: axFan. a=h1Code, b=nd(h2Code, nd(hCode, nd(aCode, bCode))).
-- thFun: nd(mkAp2(Fan(h1,h2,h), a, b), mkAp2(h, mkAp2(h1,a,b), mkAp2(h2,a,b)))
private
  origB2b1 : Fun2
  origB2b1 = Post Fst origB2b

  origB2b2 : Fun2
  origB2b2 = Post Snd origB2b

case8 : Fun2
case8 = mkEqF
  (mkAp2F (Fan (kF2 codeFanTag) (Fan origA (Fan origB1 origB2a Pair) Pair) Pair)
           origB2b1 origB2b2)
  (mkAp2F origB2a (mkAp2F origA origB2b1 origB2b2) (mkAp2F origB1 origB2b1 origB2b2))
