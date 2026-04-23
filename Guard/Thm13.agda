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
open import Guard.ProofEncUnify using
  ( encAxI   ; encAxICorr
  ; encAxFst ; encAxFstCorr
  )

private
  n1 : Nat ; n1 = suc zero

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

------------------------------------------------------------------------
-- Base case:  Fst .
--
--  xC = reify (code (ap2 Pair a b))
--     = ap2 Pair (reify tagAp2)
--                (ap2 Pair (reify (codeF2 Pair))
--                          (ap2 Pair (reify (code a)) (reify (code b)))) .
--
--  D1Fst  extracts the innermost pair  (ap2 Pair aC bC)  via  Snd . Snd
-- and prepends the tag  reify (natCode n1) :
--
--   ap1 D1Fst xC
--     = ap2 Pair (ap1 (KT (reify (natCode n1))) xC) (ap1 (Comp Snd Snd) xC)
--                                                                  [axComp2]
--     = ap2 Pair (reify (natCode n1))              (ap1 Snd (ap1 Snd xC))
--                                                                  [axKT, axComp]
--     = ap2 Pair (reify (natCode n1)) (ap2 Pair aC bC)             [axSnd x 2]
--     = encAxFst aC bC .
--
-- Then  encAxFstCorr aC bC  delivers the thmT correctness.

D1Fst : Fun1
D1Fst = Comp2 Pair (KT (reify (natCode n1))) (Comp Snd Snd)

d1FstRed : (a b : Term) ->
  Deriv (atomic (eqn (ap1 D1Fst (reify (code (ap2 Pair a b))))
                     (encAxFst (reify (code a)) (reify (code b)))))
d1FstRed a b =
  let aC : Term ; aC = reify (code a)
      bC : Term ; bC = reify (code b)
      xC : Term ; xC = reify (code (ap2 Pair a b))
      tagR : Term ; tagR = reify (natCode n1)
      inner : Term ; inner = ap2 Pair (reify (codeF2 Pair)) (ap2 Pair aC bC)
      -- ap1 D1Fst xC = Pair (KT(tagR) xC) (Comp Snd Snd xC)
      s1 : Deriv (atomic (eqn (ap1 D1Fst xC)
                              (ap2 Pair (ap1 (KT tagR) xC)
                                        (ap1 (Comp Snd Snd) xC))))
      s1 = axComp2 Pair (KT tagR) (Comp Snd Snd) xC
      -- Left: KT tagR xC = tagR.
      s2 : Deriv (atomic (eqn (ap1 (KT tagR) xC) tagR))
      s2 = axKT tagR xC
      -- Right: Comp Snd Snd xC = Snd (Snd xC).
      s3 : Deriv (atomic (eqn (ap1 (Comp Snd Snd) xC) (ap1 Snd (ap1 Snd xC))))
      s3 = axComp Snd Snd xC
      -- Snd xC = inner.
      s4 : Deriv (atomic (eqn (ap1 Snd xC) inner))
      s4 = axSnd (reify tagAp2) inner
      -- Snd inner = Pair aC bC.
      s5 : Deriv (atomic (eqn (ap1 Snd inner) (ap2 Pair aC bC)))
      s5 = axSnd (reify (codeF2 Pair)) (ap2 Pair aC bC)
  in ruleTrans s1
       (ruleTrans (congL Pair (ap1 (Comp Snd Snd) xC) s2)
                  (congR Pair tagR
                    (ruleTrans s3
                      (ruleTrans (cong1 Snd s4) s5))))

thm13Fun1Fst : (a b : Term) ->
  Deriv (atomic (eqn (ap1 thmT (ap1 D1Fst (reify (code (ap2 Pair a b)))))
                     (reify (codeFormula
                       (atomic (eqn (ap1 Fst (ap2 Pair a b)) a))))))
thm13Fun1Fst a b =
  let aC : Term ; aC = reify (code a)
      bC : Term ; bC = reify (code b)
  in ruleTrans (cong1 thmT (d1FstRed a b)) (encAxFstCorr aC bC)
