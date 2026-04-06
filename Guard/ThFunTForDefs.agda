{-# OPTIONS --safe --without-K --exact-split #-}

module Guard.ThFunTForDefs where

open import Guard.Base
open import Guard.Term

------------------------------------------------------------------------
-- Extractors: Fun2 helpers for accessing parts of (orig, recs)

-- sndArg(orig, recs) = recs
sndArg2 : Fun2
sndArg2 = Post Snd Pair

-- origA(orig, recs) = Fst(Snd(orig)) = data_a
origA : Fun2
origA = Lift (Comp Fst Snd)

-- origB(orig, recs) = Snd(Snd(orig)) = data_b
origB : Fun2
origB = Lift (Comp Snd Snd)

-- recsA(orig, recs) = Fst(Snd(recs)) = Rec(data_a)
-- sndArg2 gives recs, then Snd, then Fst
recsA : Fun2
recsA = Post Fst (Post Snd sndArg2)

-- recsB(orig, recs) = Snd(Snd(recs)) = Rec(data_b)
recsB : Fun2
recsB = Post Snd (Post Snd sndArg2)

-- Fst/Snd of recursive result: extract L,R from thFunTFor(subproof)
-- recsAL = Fst(recsA) = left side of equation from subproof a
recsAL : Fun2
recsAL = Post Fst recsA

-- recsAR = Snd(recsA) = right side of equation from subproof a
recsAR : Fun2
recsAR = Post Snd recsA

-- recsBL = Fst(recsB)
recsBL : Fun2
recsBL = Post Fst recsB

-- recsBR = Snd(recsB)
recsBR : Fun2
recsBR = Post Snd recsB

------------------------------------------------------------------------
-- Sub-extractors for deeply nested payload data
-- For payload = nd(a, nd(b, nd(c, d))):
-- origA = a, origB = nd(b, nd(c, d))
-- origB1 = Fst(origB) = b
-- origB2 = Snd(origB) = nd(c, d)
-- origB2a = Fst(origB2) = c
-- origB2b = Snd(origB2) = d

origB1 : Fun2
origB1 = Post Fst origB

origB2 : Fun2
origB2 = Post Snd origB

origB2a : Fun2
origB2a = Post Fst origB2

origB2b : Fun2
origB2b = Post Snd origB2

------------------------------------------------------------------------
-- Sub-extractors for data packed inside origA = nd(x, y)
origAL : Fun2
origAL = Post Fst origA

origAR : Fun2
origAR = Post Snd origA

------------------------------------------------------------------------
-- Tag check: compare Fst(orig) with reify(natCode n)

tagCheck : Nat -> Fun2
tagCheck n = Fan (Lift Fst) (Lift (KT (reify (natCode n)))) TreeEq

------------------------------------------------------------------------
-- Branch combinator: if check then result else rest

branch : Fun2 -> Fun2 -> Fun2 -> Fun2
branch check result rest = Fan check (Fan result rest Pair) IfLf

------------------------------------------------------------------------
-- Constant Fun2: always returns a specific Term

kF2 : Term -> Fun2
kF2 t = Lift (KT t)

------------------------------------------------------------------------
-- mkAp1F: construct coded ap1 application from Fun2 components
-- mkAp1F fC tC = Pair(reify tagAp1, Pair(fC, tC))

mkAp1F : Fun2 -> Fun2 -> Fun2
mkAp1F fCodeF tCodeF = Fan (kF2 (reify tagAp1)) (Fan fCodeF tCodeF Pair) Pair

-- mkAp2F: construct coded ap2 application
-- mkAp2F gC aC bC = Pair(reify tagAp2, Pair(gC, Pair(aC, bC)))

mkAp2F : Fun2 -> Fun2 -> Fun2 -> Fun2
mkAp2F gCodeF aCodeF bCodeF =
  Fan (kF2 (reify tagAp2)) (Fan gCodeF (Fan aCodeF bCodeF Pair) Pair) Pair

------------------------------------------------------------------------
-- mkEqF: construct coded equation (pair of left and right)

mkEqF : Fun2 -> Fun2 -> Fun2
mkEqF leftF rightF = Fan leftF rightF Pair
