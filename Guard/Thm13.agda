{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.Thm13 -- encoder functors D1/D2 and correctness lemmas.
--
-- Per UNIFIED-DESIGN-REV2-5C.md §(1).  For each primitive functor
-- constructor  f , we build a closed Fun1/Fun2 expression  D1 f  /
--  D2 g  such that, when applied to code arguments, it produces the
-- encoded proof of the corresponding defining equation.  The
-- correctness lemma  thm13Fun1 f / thm13Fun2 g  then states that
--  thmT  on this encoded proof yields the Gödel code of the
-- equation.
--
-- Base cases land first ([unify-5c-thm13-fun1-I], -Fst, -Snd, -KT).
-- Inductive / mutual cases follow in later commits.
--
-- Signature choice.  We take Guard's Thm 13 in its strict form: the
-- target equation is  f(x) = x  for I,  Fst(Pair a b) = a  for Fst,
-- etc. -- i.e.  y  is fixed by the constructor.  This matches every
-- existing  encAx*Corr  lemma without needing a hypothetical  Deriv
-- recursor to bridge  y  to  f(x) .

module Guard.Thm13 where

open import Guard.Base
open import Guard.Term
open import Guard.Formula
open import Guard.DerivF
open import Guard.ThFun using (codeEqn)
open import Guard.ThFunTForHF using (thmT)
open import Guard.ProofEncUnify using (encAxI ; encAxICorr)

------------------------------------------------------------------------
-- Base case:  I .
--
--  D1I  applied to  xC  reduces to  encAxI xC = Pair O (Pair xC O) :
--
--   ap1 D1I xC
--     = ap2 Pair (ap1 (KT O) xC) (ap1 (Comp2 Pair I (KT O)) xC)   [axComp2]
--     = ap2 Pair O                (ap2 Pair (ap1 I xC) (ap1 (KT O) xC))
--                                                                  [axKT, axComp2]
--     = ap2 Pair O (ap2 Pair xC O)                                 [axI, axKT]
--
-- Then  encAxICorr xC  delivers the thmT correctness.

D1I : Fun1
D1I = Comp2 Pair (KT O) (Comp2 Pair I (KT O))

d1IRed : (xC : Term) -> Deriv (atomic (eqn (ap1 D1I xC) (encAxI xC)))
d1IRed xC =
  let inner : Deriv (atomic (eqn (ap1 (Comp2 Pair I (KT O)) xC)
                                  (ap2 Pair xC O)))
      inner = ruleTrans (axComp2 Pair I (KT O) xC)
                        (ruleTrans (congL Pair (ap1 (KT O) xC) (axI xC))
                                   (congR Pair xC (axKT O xC)))
  in ruleTrans (axComp2 Pair (KT O) (Comp2 Pair I (KT O)) xC)
               (ruleTrans (congL Pair (ap1 (Comp2 Pair I (KT O)) xC)
                                  (axKT O xC))
                          (congR Pair O inner))

-- Guard's Thm 13 at  f = I :
--
--   thmT (D1I xC) = reify (codeFormula (atomic (eqn (ap1 I x) x)))
--
-- with  xC = reify (code x) .

thm13Fun1I : (x : Term) ->
  Deriv (atomic (eqn (ap1 thmT (ap1 D1I (reify (code x))))
                     (reify (codeFormula (atomic (eqn (ap1 I x) x))))))
thm13Fun1I x =
  let xC : Term ; xC = reify (code x)
  in ruleTrans (cong1 thmT (d1IRed xC)) (encAxICorr xC)
