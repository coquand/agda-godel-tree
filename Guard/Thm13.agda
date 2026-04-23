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
  ( encAxI        ; encAxICorr
  ; encAxFst      ; encAxFstCorr
  ; encAxSnd      ; encAxSndCorr
  ; encAxKT       ; encAxKTCorr
  ; encAxComp     ; encAxCompCorr
  ; encAxComp2    ; encAxComp2Corr
  ; encAxConst    ; encAxConstCorr
  ; encAxLift     ; encAxLiftCorr
  ; encAxPost     ; encAxPostCorr
  ; encAxFan      ; encAxFanCorr
  ; encAxIfLfL    ; encAxIfLfLCorr
  ; encAxIfLfN    ; encAxIfLfNCorr
  ; encAxTreeEqLL ; encAxTreeEqLLCorr
  ; encAxTreeEqLN ; encAxTreeEqLNCorr
  ; encAxTreeEqNL ; encAxTreeEqNLCorr
  ; encAxTreeEqNN ; encAxTreeEqNNCorr
  ; encAxRecLf    ; encAxRecLfCorr
  ; encAxRecNd    ; encAxRecNdCorr
  )

private
  n1  : Nat ; n1  = suc zero
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
  n25 : Nat
  n25 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
      (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
      (suc (suc (suc (suc (suc zero))))))))))))))))))))))))

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

------------------------------------------------------------------------
-- Base case:  Snd .  Mirrors  Fst  -- only the tag differs  (n2  vs  n1) .

D1Snd : Fun1
D1Snd = Comp2 Pair (KT (reify (natCode n2))) (Comp Snd Snd)

d1SndRed : (a b : Term) ->
  Deriv (atomic (eqn (ap1 D1Snd (reify (code (ap2 Pair a b))))
                     (encAxSnd (reify (code a)) (reify (code b)))))
d1SndRed a b =
  let aC : Term ; aC = reify (code a)
      bC : Term ; bC = reify (code b)
      xC : Term ; xC = reify (code (ap2 Pair a b))
      tagR : Term ; tagR = reify (natCode n2)
      inner : Term ; inner = ap2 Pair (reify (codeF2 Pair)) (ap2 Pair aC bC)
      s1 : Deriv (atomic (eqn (ap1 D1Snd xC)
                              (ap2 Pair (ap1 (KT tagR) xC)
                                        (ap1 (Comp Snd Snd) xC))))
      s1 = axComp2 Pair (KT tagR) (Comp Snd Snd) xC
      s2 : Deriv (atomic (eqn (ap1 (KT tagR) xC) tagR))
      s2 = axKT tagR xC
      s3 : Deriv (atomic (eqn (ap1 (Comp Snd Snd) xC) (ap1 Snd (ap1 Snd xC))))
      s3 = axComp Snd Snd xC
      s4 : Deriv (atomic (eqn (ap1 Snd xC) inner))
      s4 = axSnd (reify tagAp2) inner
      s5 : Deriv (atomic (eqn (ap1 Snd inner) (ap2 Pair aC bC)))
      s5 = axSnd (reify (codeF2 Pair)) (ap2 Pair aC bC)
  in ruleTrans s1
       (ruleTrans (congL Pair (ap1 (Comp Snd Snd) xC) s2)
                  (congR Pair tagR
                    (ruleTrans s3
                      (ruleTrans (cong1 Snd s4) s5))))

thm13Fun1Snd : (a b : Term) ->
  Deriv (atomic (eqn (ap1 thmT (ap1 D1Snd (reify (code (ap2 Pair a b)))))
                     (reify (codeFormula
                       (atomic (eqn (ap1 Snd (ap2 Pair a b)) b))))))
thm13Fun1Snd a b =
  let aC : Term ; aC = reify (code a)
      bC : Term ; bC = reify (code b)
  in ruleTrans (cong1 thmT (d1SndRed a b)) (encAxSndCorr aC bC)

------------------------------------------------------------------------
-- Base case:  KT .
--
--  KT  is parameterized by a closed term  t .  For each  t  we build
--   D1KT t : Fun1  such that, applied to  xC = reify (code x) , it
-- reduces to  encAxKT (reify (code t)) xC .
--
--   ap1 (D1KT t) xC
--     = ap2 Pair (ap1 (KT (reify (natCode n25))) xC)
--                (ap1 (Comp2 Pair (KT (reify (code t))) I) xC)     [axComp2]
--     = ap2 Pair (reify (natCode n25))
--                (ap2 Pair (ap1 (KT (reify (code t))) xC) (ap1 I xC))
--                                                                  [axKT, axComp2]
--     = ap2 Pair (reify (natCode n25)) (ap2 Pair (reify (code t)) xC)
--                                                                  [axKT, axI]
--     = encAxKT (reify (code t)) xC .

D1KT : Term -> Fun1
D1KT t = Comp2 Pair (KT (reify (natCode n25)))
                    (Comp2 Pair (KT (reify (code t))) I)

d1KTRed : (t x : Term) ->
  Deriv (atomic (eqn (ap1 (D1KT t) (reify (code x)))
                     (encAxKT (reify (code t)) (reify (code x)))))
d1KTRed t x =
  let xC : Term ; xC = reify (code x)
      tC : Term ; tC = reify (code t)
      tagR : Term ; tagR = reify (natCode n25)
      inner : Fun1 ; inner = Comp2 Pair (KT tC) I
      s1 : Deriv (atomic (eqn (ap1 (D1KT t) xC)
                              (ap2 Pair (ap1 (KT tagR) xC)
                                        (ap1 inner xC))))
      s1 = axComp2 Pair (KT tagR) inner xC
      s2 : Deriv (atomic (eqn (ap1 (KT tagR) xC) tagR))
      s2 = axKT tagR xC
      s3 : Deriv (atomic (eqn (ap1 inner xC)
                              (ap2 Pair (ap1 (KT tC) xC) (ap1 I xC))))
      s3 = axComp2 Pair (KT tC) I xC
      s4 : Deriv (atomic (eqn (ap1 (KT tC) xC) tC))
      s4 = axKT tC xC
      s5 : Deriv (atomic (eqn (ap1 I xC) xC))
      s5 = axI xC
  in ruleTrans s1
       (ruleTrans (congL Pair (ap1 inner xC) s2)
                  (congR Pair tagR
                    (ruleTrans s3
                      (ruleTrans (congL Pair (ap1 I xC) s4)
                                 (congR Pair tC s5)))))

thm13Fun1KT : (t x : Term) ->
  Deriv (atomic (eqn (ap1 thmT (ap1 (D1KT t) (reify (code x))))
                     (reify (codeFormula
                       (atomic (eqn (ap1 (KT t) x) t))))))
thm13Fun1KT t x =
  let tC : Term ; tC = reify (code t)
      xC : Term ; xC = reify (code x)
  in ruleTrans (cong1 thmT (d1KTRed t x)) (encAxKTCorr tC xC)

------------------------------------------------------------------------
-- Fun1 case:  Comp f g .
--
-- Strict form: at meta-level  y = ap1 (Comp f g) x = ap1 f (ap1 g x) ,
-- so the target encoding is  encAxComp (codeF1 f) (codeF1 g) xC
-- and  encAxCompCorr  closes directly.
--
--   ap1 (D1Comp f g) xC
--     = Pair (natCode n4) (Pair (codeF1 f)R (Pair (codeF1 g)R xC))
--     = encAxComp (codeF1 f)R (codeF1 g)R xC

D1Comp : Fun1 -> Fun1 -> Fun1
D1Comp f g = Comp2 Pair (KT (reify (natCode n4)))
               (Comp2 Pair (KT (reify (codeF1 f)))
                 (Comp2 Pair (KT (reify (codeF1 g))) I))

d1CompRed : (f g : Fun1) (x : Term) ->
  Deriv (atomic (eqn (ap1 (D1Comp f g) (reify (code x)))
                     (encAxComp (reify (codeF1 f)) (reify (codeF1 g))
                                (reify (code x)))))
d1CompRed f g x =
  let xC : Term ; xC = reify (code x)
      fCR : Term ; fCR = reify (codeF1 f)
      gCR : Term ; gCR = reify (codeF1 g)
      tagR : Term ; tagR = reify (natCode n4)
      level3 : Fun1 ; level3 = Comp2 Pair (KT gCR) I
      level2 : Fun1 ; level2 = Comp2 Pair (KT fCR) level3
      inner3 : Deriv (atomic (eqn (ap1 level3 xC)
                                   (ap2 Pair gCR xC)))
      inner3 = ruleTrans (axComp2 Pair (KT gCR) I xC)
                 (ruleTrans (congL Pair (ap1 I xC) (axKT gCR xC))
                            (congR Pair gCR (axI xC)))
      inner2 : Deriv (atomic (eqn (ap1 level2 xC)
                                   (ap2 Pair fCR (ap2 Pair gCR xC))))
      inner2 = ruleTrans (axComp2 Pair (KT fCR) level3 xC)
                 (ruleTrans (congL Pair (ap1 level3 xC) (axKT fCR xC))
                            (congR Pair fCR inner3))
  in ruleTrans (axComp2 Pair (KT tagR) level2 xC)
       (ruleTrans (congL Pair (ap1 level2 xC) (axKT tagR xC))
                  (congR Pair tagR inner2))

thm13Fun1Comp : (f g : Fun1) (x : Term) ->
  Deriv (atomic (eqn (ap1 thmT (ap1 (D1Comp f g) (reify (code x))))
                     (reify (codeFormula
                       (atomic (eqn (ap1 (Comp f g) x) (ap1 f (ap1 g x))))))))
thm13Fun1Comp f g x =
  let xC : Term ; xC = reify (code x)
      fCR : Term ; fCR = reify (codeF1 f)
      gCR : Term ; gCR = reify (codeF1 g)
  in ruleTrans (cong1 thmT (d1CompRed f g x)) (encAxCompCorr fCR gCR xC)

------------------------------------------------------------------------
-- Fun1 case:  Comp2 h f g .
--
-- Strict form: y = ap1 (Comp2 h f g) x = ap2 h (ap1 f x) (ap1 g x).
-- Target encoding: encAxComp2 hhC fC gC xC.

D1Comp2 : Fun2 -> Fun1 -> Fun1 -> Fun1
D1Comp2 h f g = Comp2 Pair (KT (reify (natCode n5)))
                 (Comp2 Pair (KT (reify (codeF2 h)))
                   (Comp2 Pair (KT (reify (codeF1 f)))
                     (Comp2 Pair (KT (reify (codeF1 g))) I)))

d1Comp2Red : (h : Fun2) (f g : Fun1) (x : Term) ->
  Deriv (atomic (eqn (ap1 (D1Comp2 h f g) (reify (code x)))
                     (encAxComp2 (reify (codeF2 h)) (reify (codeF1 f))
                                 (reify (codeF1 g)) (reify (code x)))))
d1Comp2Red h f g x =
  let xC : Term ; xC = reify (code x)
      hCR : Term ; hCR = reify (codeF2 h)
      fCR : Term ; fCR = reify (codeF1 f)
      gCR : Term ; gCR = reify (codeF1 g)
      tagR : Term ; tagR = reify (natCode n5)
      l4 : Fun1 ; l4 = Comp2 Pair (KT gCR) I
      l3 : Fun1 ; l3 = Comp2 Pair (KT fCR) l4
      l2 : Fun1 ; l2 = Comp2 Pair (KT hCR) l3
      i4 : Deriv (atomic (eqn (ap1 l4 xC) (ap2 Pair gCR xC)))
      i4 = ruleTrans (axComp2 Pair (KT gCR) I xC)
             (ruleTrans (congL Pair (ap1 I xC) (axKT gCR xC))
                        (congR Pair gCR (axI xC)))
      i3 : Deriv (atomic (eqn (ap1 l3 xC) (ap2 Pair fCR (ap2 Pair gCR xC))))
      i3 = ruleTrans (axComp2 Pair (KT fCR) l4 xC)
             (ruleTrans (congL Pair (ap1 l4 xC) (axKT fCR xC))
                        (congR Pair fCR i4))
      i2 : Deriv (atomic (eqn (ap1 l2 xC)
                              (ap2 Pair hCR (ap2 Pair fCR (ap2 Pair gCR xC)))))
      i2 = ruleTrans (axComp2 Pair (KT hCR) l3 xC)
             (ruleTrans (congL Pair (ap1 l3 xC) (axKT hCR xC))
                        (congR Pair hCR i3))
  in ruleTrans (axComp2 Pair (KT tagR) l2 xC)
       (ruleTrans (congL Pair (ap1 l2 xC) (axKT tagR xC))
                  (congR Pair tagR i2))

thm13Fun1Comp2 : (h : Fun2) (f g : Fun1) (x : Term) ->
  Deriv (atomic (eqn (ap1 thmT (ap1 (D1Comp2 h f g) (reify (code x))))
                     (reify (codeFormula
                       (atomic (eqn (ap1 (Comp2 h f g) x)
                                     (ap2 h (ap1 f x) (ap1 g x))))))))
thm13Fun1Comp2 h f g x =
  let xC : Term ; xC = reify (code x)
      hCR : Term ; hCR = reify (codeF2 h)
      fCR : Term ; fCR = reify (codeF1 f)
      gCR : Term ; gCR = reify (codeF1 g)
  in ruleTrans (cong1 thmT (d1Comp2Red h f g x))
               (encAxComp2Corr hCR fCR gCR xC)

------------------------------------------------------------------------
-- Fun2 base case:  Const .
--
--   ap2 D2Const aC bC
--     = ap2 Pair (ap2 (Lift (KT (reify (natCode n3)))) aC bC)
--                (ap2 Pair aC bC)                             [axFan]
--     = ap2 Pair (reify (natCode n3)) (ap2 Pair aC bC)        [axLift, axKT]
--     = encAxConst aC bC .

D2Const : Fun2
D2Const = Fan (Lift (KT (reify (natCode n3)))) Pair Pair

d2ConstRed : (a b : Term) ->
  Deriv (atomic (eqn (ap2 D2Const (reify (code a)) (reify (code b)))
                     (encAxConst (reify (code a)) (reify (code b)))))
d2ConstRed a b =
  let aC : Term ; aC = reify (code a)
      bC : Term ; bC = reify (code b)
      tagR : Term ; tagR = reify (natCode n3)
      s1 : Deriv (atomic (eqn (ap2 D2Const aC bC)
                              (ap2 Pair (ap2 (Lift (KT tagR)) aC bC)
                                        (ap2 Pair aC bC))))
      s1 = axFan (Lift (KT tagR)) Pair Pair aC bC
      s2 : Deriv (atomic (eqn (ap2 (Lift (KT tagR)) aC bC) tagR))
      s2 = ruleTrans (axLift (KT tagR) aC bC) (axKT tagR aC)
  in ruleTrans s1 (congL Pair (ap2 Pair aC bC) s2)

thm13Fun2Const : (a b : Term) ->
  Deriv (atomic (eqn (ap1 thmT (ap2 D2Const (reify (code a)) (reify (code b))))
                     (reify (codeFormula
                       (atomic (eqn (ap2 Const a b) a))))))
thm13Fun2Const a b =
  let aC : Term ; aC = reify (code a)
      bC : Term ; bC = reify (code b)
  in ruleTrans (cong1 thmT (d2ConstRed a b)) (encAxConstCorr aC bC)

------------------------------------------------------------------------
-- Fun2 base case:  IfLfL .
--
-- The axiom is  axIfLfL a b : ap2 IfLf O (ap2 Pair a b) = a .  Its
-- canonical inputs are (O, ap2 Pair a b); coded these become
--
--   x1C = reify (code O)             = ap2 Pair O O                 (trivial).
--   x2C = reify (code (ap2 Pair a b))
--       = ap2 Pair (reify tagAp2)
--                  (ap2 Pair (reify (codeF2 Pair))
--                            (ap2 Pair aC bC))
--
-- The target encoding  encAxIfLfL aC bC  = Pair (natCode n11) (Pair aC bC)
-- requires extracting the innermost pair  (Pair aC bC)  from  x2C :
-- a  Snd . Snd  applied to  x2C  does this.  We use
--  Post (Comp (Comp Snd Snd) Snd) Pair  to build a Fun2 that ignores
--  x1  and returns  Snd (Snd x2) .

D2IfLfL : Fun2
D2IfLfL = Fan (Lift (KT (reify (natCode n11))))
              (Post (Comp (Comp Snd Snd) Snd) Pair)
              Pair

d2IfLfLRed : (a b : Term) ->
  Deriv (atomic (eqn (ap2 D2IfLfL (reify (code O))
                                  (reify (code (ap2 Pair a b))))
                     (encAxIfLfL (reify (code a)) (reify (code b)))))
d2IfLfLRed a b =
  let aC : Term ; aC = reify (code a)
      bC : Term ; bC = reify (code b)
      x1C : Term ; x1C = reify (code O)
      x2C : Term ; x2C = reify (code (ap2 Pair a b))
      tagR : Term ; tagR = reify (natCode n11)
      mid : Term ; mid = ap2 Pair (reify (codeF2 Pair)) (ap2 Pair aC bC)
      -- H1 = Lift (KT tagR): applied to (x1C, x2C) gives tagR.
      s1 : Deriv (atomic (eqn (ap2 (Lift (KT tagR)) x1C x2C) tagR))
      s1 = ruleTrans (axLift (KT tagR) x1C x2C) (axKT tagR x1C)
      -- H2 = Post (Comp (Comp Snd Snd) Snd) Pair:
      --   applied to (x1C, x2C) reduces via axPost to
      --   ap1 (Comp (Comp Snd Snd) Snd) (ap2 Pair x1C x2C) ,
      --   and then by axComp / axSnd chains to  Snd (Snd x2C) .
      s2a : Deriv (atomic (eqn (ap2 (Post (Comp (Comp Snd Snd) Snd) Pair) x1C x2C)
                               (ap1 (Comp (Comp Snd Snd) Snd)
                                    (ap2 Pair x1C x2C))))
      s2a = axPost (Comp (Comp Snd Snd) Snd) Pair x1C x2C
      s2b : Deriv (atomic (eqn (ap1 (Comp (Comp Snd Snd) Snd)
                                    (ap2 Pair x1C x2C))
                               (ap1 (Comp Snd Snd)
                                    (ap1 Snd (ap2 Pair x1C x2C)))))
      s2b = axComp (Comp Snd Snd) Snd (ap2 Pair x1C x2C)
      s2c : Deriv (atomic (eqn (ap1 Snd (ap2 Pair x1C x2C)) x2C))
      s2c = axSnd x1C x2C
      s2d : Deriv (atomic (eqn (ap1 (Comp Snd Snd) x2C)
                               (ap1 Snd (ap1 Snd x2C))))
      s2d = axComp Snd Snd x2C
      s2e : Deriv (atomic (eqn (ap1 Snd x2C) mid))
      s2e = axSnd (reify tagAp2) mid
      s2f : Deriv (atomic (eqn (ap1 Snd mid) (ap2 Pair aC bC)))
      s2f = axSnd (reify (codeF2 Pair)) (ap2 Pair aC bC)
      s2 : Deriv (atomic (eqn (ap2 (Post (Comp (Comp Snd Snd) Snd) Pair) x1C x2C)
                              (ap2 Pair aC bC)))
      s2 = ruleTrans s2a
             (ruleTrans s2b
               (ruleTrans (cong1 (Comp Snd Snd) s2c)
                 (ruleTrans s2d
                   (ruleTrans (cong1 Snd s2e) s2f))))
      -- Outer Fan reduction.
      s0 : Deriv (atomic (eqn (ap2 D2IfLfL x1C x2C)
                              (ap2 Pair
                                (ap2 (Lift (KT tagR)) x1C x2C)
                                (ap2 (Post (Comp (Comp Snd Snd) Snd) Pair) x1C x2C))))
      s0 = axFan (Lift (KT tagR)) (Post (Comp (Comp Snd Snd) Snd) Pair) Pair x1C x2C
  in ruleTrans s0
       (ruleTrans (congL Pair (ap2 (Post (Comp (Comp Snd Snd) Snd) Pair) x1C x2C) s1)
                  (congR Pair tagR s2))

thm13Fun2IfLfL : (a b : Term) ->
  Deriv (atomic (eqn (ap1 thmT (ap2 D2IfLfL (reify (code O))
                                             (reify (code (ap2 Pair a b)))))
                     (reify (codeFormula
                       (atomic (eqn (ap2 IfLf O (ap2 Pair a b)) a))))))
thm13Fun2IfLfL a b =
  let aC : Term ; aC = reify (code a)
      bC : Term ; bC = reify (code b)
  in ruleTrans (cong1 thmT (d2IfLfLRed a b)) (encAxIfLfLCorr aC bC)

------------------------------------------------------------------------
-- Fun2 base case:  TreeEqLL .
--
-- axTreeEqLL : ap2 TreeEq O O = O .  Zero-arg axiom: the canonical
-- inputs are both O, and the encoded proof  encAxTreeEqLL  is
--  Pair (natCode n13) O  with no parameters.  D2TreeEqLL is thus a
-- constant Fun2 that ignores its inputs.

D2TreeEqLL : Fun2
D2TreeEqLL = Fan (Lift (KT (reify (natCode n13))))
                 (Lift (KT O))
                 Pair

d2TreeEqLLRed :
  Deriv (atomic (eqn (ap2 D2TreeEqLL (reify (code O)) (reify (code O)))
                     encAxTreeEqLL))
d2TreeEqLLRed =
  let x1C : Term ; x1C = reify (code O)
      x2C : Term ; x2C = reify (code O)
      tagR : Term ; tagR = reify (natCode n13)
      s0 : Deriv (atomic (eqn (ap2 D2TreeEqLL x1C x2C)
                              (ap2 Pair (ap2 (Lift (KT tagR)) x1C x2C)
                                        (ap2 (Lift (KT O))   x1C x2C))))
      s0 = axFan (Lift (KT tagR)) (Lift (KT O)) Pair x1C x2C
      s1 : Deriv (atomic (eqn (ap2 (Lift (KT tagR)) x1C x2C) tagR))
      s1 = ruleTrans (axLift (KT tagR) x1C x2C) (axKT tagR x1C)
      s2 : Deriv (atomic (eqn (ap2 (Lift (KT O)) x1C x2C) O))
      s2 = ruleTrans (axLift (KT O) x1C x2C) (axKT O x1C)
  in ruleTrans s0
       (ruleTrans (congL Pair (ap2 (Lift (KT O)) x1C x2C) s1)
                  (congR Pair tagR s2))

thm13Fun2TreeEqLL :
  Deriv (atomic (eqn (ap1 thmT (ap2 D2TreeEqLL (reify (code O)) (reify (code O))))
                     (reify (codeFormula
                       (atomic (eqn (ap2 TreeEq O O) O))))))
thm13Fun2TreeEqLL =
  ruleTrans (cong1 thmT d2TreeEqLLRed) encAxTreeEqLLCorr

------------------------------------------------------------------------
-- Fun2 base case:  TreeEqLN .
--
-- axTreeEqLN a b : ap2 TreeEq O (ap2 Pair a b) = ap2 Pair O O .
-- Same shape as IfLfL: second input is a 3-deep Pair; extract the
-- innermost (Pair aC bC) via Snd.Snd.  Tag is n14.

D2TreeEqLN : Fun2
D2TreeEqLN = Fan (Lift (KT (reify (natCode n14))))
                 (Post (Comp (Comp Snd Snd) Snd) Pair)
                 Pair

d2TreeEqLNRed : (a b : Term) ->
  Deriv (atomic (eqn (ap2 D2TreeEqLN (reify (code O))
                                     (reify (code (ap2 Pair a b))))
                     (encAxTreeEqLN (reify (code a)) (reify (code b)))))
d2TreeEqLNRed a b =
  let aC : Term ; aC = reify (code a)
      bC : Term ; bC = reify (code b)
      x1C : Term ; x1C = reify (code O)
      x2C : Term ; x2C = reify (code (ap2 Pair a b))
      tagR : Term ; tagR = reify (natCode n14)
      mid : Term ; mid = ap2 Pair (reify (codeF2 Pair)) (ap2 Pair aC bC)
      s1 : Deriv (atomic (eqn (ap2 (Lift (KT tagR)) x1C x2C) tagR))
      s1 = ruleTrans (axLift (KT tagR) x1C x2C) (axKT tagR x1C)
      s2 : Deriv (atomic (eqn (ap2 (Post (Comp (Comp Snd Snd) Snd) Pair) x1C x2C)
                              (ap2 Pair aC bC)))
      s2 = ruleTrans (axPost (Comp (Comp Snd Snd) Snd) Pair x1C x2C)
             (ruleTrans (axComp (Comp Snd Snd) Snd (ap2 Pair x1C x2C))
               (ruleTrans (cong1 (Comp Snd Snd) (axSnd x1C x2C))
                 (ruleTrans (axComp Snd Snd x2C)
                   (ruleTrans (cong1 Snd (axSnd (reify tagAp2) mid))
                              (axSnd (reify (codeF2 Pair)) (ap2 Pair aC bC))))))
      s0 : Deriv (atomic (eqn (ap2 D2TreeEqLN x1C x2C)
                              (ap2 Pair
                                (ap2 (Lift (KT tagR)) x1C x2C)
                                (ap2 (Post (Comp (Comp Snd Snd) Snd) Pair) x1C x2C))))
      s0 = axFan (Lift (KT tagR)) (Post (Comp (Comp Snd Snd) Snd) Pair) Pair x1C x2C
  in ruleTrans s0
       (ruleTrans (congL Pair (ap2 (Post (Comp (Comp Snd Snd) Snd) Pair) x1C x2C) s1)
                  (congR Pair tagR s2))

thm13Fun2TreeEqLN : (a b : Term) ->
  Deriv (atomic (eqn (ap1 thmT (ap2 D2TreeEqLN (reify (code O))
                                                (reify (code (ap2 Pair a b)))))
                     (reify (codeFormula
                       (atomic (eqn (ap2 TreeEq O (ap2 Pair a b))
                                    (ap2 Pair O O)))))))
thm13Fun2TreeEqLN a b =
  let aC : Term ; aC = reify (code a)
      bC : Term ; bC = reify (code b)
  in ruleTrans (cong1 thmT (d2TreeEqLNRed a b)) (encAxTreeEqLNCorr aC bC)

------------------------------------------------------------------------
-- Fun2 base case:  TreeEqNL .
--
-- axTreeEqNL a b : ap2 TreeEq (ap2 Pair a b) O = ap2 Pair O O .
-- Mirror image of TreeEqLN: here the FIRST input is the 3-deep Pair;
-- extract via  Lift (Comp Snd Snd) .  Tag is n15.

D2TreeEqNL : Fun2
D2TreeEqNL = Fan (Lift (KT (reify (natCode n15))))
                 (Lift (Comp Snd Snd))
                 Pair

d2TreeEqNLRed : (a b : Term) ->
  Deriv (atomic (eqn (ap2 D2TreeEqNL (reify (code (ap2 Pair a b)))
                                     (reify (code O)))
                     (encAxTreeEqNL (reify (code a)) (reify (code b)))))
d2TreeEqNLRed a b =
  let aC : Term ; aC = reify (code a)
      bC : Term ; bC = reify (code b)
      x1C : Term ; x1C = reify (code (ap2 Pair a b))
      x2C : Term ; x2C = reify (code O)
      tagR : Term ; tagR = reify (natCode n15)
      mid : Term ; mid = ap2 Pair (reify (codeF2 Pair)) (ap2 Pair aC bC)
      s1 : Deriv (atomic (eqn (ap2 (Lift (KT tagR)) x1C x2C) tagR))
      s1 = ruleTrans (axLift (KT tagR) x1C x2C) (axKT tagR x1C)
      s2 : Deriv (atomic (eqn (ap2 (Lift (Comp Snd Snd)) x1C x2C)
                              (ap2 Pair aC bC)))
      s2 = ruleTrans (axLift (Comp Snd Snd) x1C x2C)
             (ruleTrans (axComp Snd Snd x1C)
               (ruleTrans (cong1 Snd (axSnd (reify tagAp2) mid))
                          (axSnd (reify (codeF2 Pair)) (ap2 Pair aC bC))))
      s0 : Deriv (atomic (eqn (ap2 D2TreeEqNL x1C x2C)
                              (ap2 Pair (ap2 (Lift (KT tagR)) x1C x2C)
                                        (ap2 (Lift (Comp Snd Snd)) x1C x2C))))
      s0 = axFan (Lift (KT tagR)) (Lift (Comp Snd Snd)) Pair x1C x2C
  in ruleTrans s0
       (ruleTrans (congL Pair (ap2 (Lift (Comp Snd Snd)) x1C x2C) s1)
                  (congR Pair tagR s2))

thm13Fun2TreeEqNL : (a b : Term) ->
  Deriv (atomic (eqn (ap1 thmT (ap2 D2TreeEqNL (reify (code (ap2 Pair a b)))
                                                (reify (code O))))
                     (reify (codeFormula
                       (atomic (eqn (ap2 TreeEq (ap2 Pair a b) O)
                                    (ap2 Pair O O)))))))
thm13Fun2TreeEqNL a b =
  let aC : Term ; aC = reify (code a)
      bC : Term ; bC = reify (code b)
  in ruleTrans (cong1 thmT (d2TreeEqNLRed a b)) (encAxTreeEqNLCorr aC bC)

------------------------------------------------------------------------
-- Shared extractor: a Fun2 that ignores its first argument and
-- returns  Snd (Snd x2) .  Used in both IfLfN and TreeEqNN below
-- to pull  Pair aC bC  / Pair b1C b2C  out of the second coded input.

private
  snd2X2 : Fun2
  snd2X2 = Post (Comp (Comp Snd Snd) Snd) Pair

  -- Reduction lemma for snd2X2 when the second argument is of the
  -- canonical 3-deep Pair shape  Pair tagAp2T (Pair pairCF (Pair uC vC)) .
  snd2X2Red : (x1 uC vC : Term) ->
    Deriv (atomic (eqn
      (ap2 snd2X2 x1
        (ap2 Pair (reify tagAp2)
          (ap2 Pair (reify (codeF2 Pair)) (ap2 Pair uC vC))))
      (ap2 Pair uC vC)))
  snd2X2Red x1 uC vC =
    let x2C : Term
        x2C = ap2 Pair (reify tagAp2)
                (ap2 Pair (reify (codeF2 Pair)) (ap2 Pair uC vC))
        mid : Term
        mid = ap2 Pair (reify (codeF2 Pair)) (ap2 Pair uC vC)
    in ruleTrans (axPost (Comp (Comp Snd Snd) Snd) Pair x1 x2C)
         (ruleTrans (axComp (Comp Snd Snd) Snd (ap2 Pair x1 x2C))
           (ruleTrans (cong1 (Comp Snd Snd) (axSnd x1 x2C))
             (ruleTrans (axComp Snd Snd x2C)
               (ruleTrans (cong1 Snd (axSnd (reify tagAp2) mid))
                          (axSnd (reify (codeF2 Pair)) (ap2 Pair uC vC))))))

------------------------------------------------------------------------
-- Fun2 base case:  IfLfN .
--
-- axIfLfN x y a b : ap2 IfLf (ap2 Pair x y) (ap2 Pair a b) = b .
-- Both inputs are 3-deep Pairs; we must pluck  xC  and  yC  out of
--  x1 = Pair tagAp2T (Pair pairCF (Pair xC yC))  and  Pair aC bC
-- out of  x2 , then reassemble in the order  (xC, yC, aC, bC) .
--
-- The Fun2 layout:
--   D2IfLfN = Fan tag (Fan fstInner1 (Fan sndInner1 extractPair2 Pair) Pair) Pair
-- where  fstInner1 = Lift (Comp Fst (Comp Snd Snd))  -- Fst (Snd (Snd x1))
--        sndInner1 = Lift (Comp Snd (Comp Snd Snd))  -- Snd (Snd (Snd x1))
--        extractPair2 = snd2X2                       -- Snd (Snd x2)

private
  fstInner1 : Fun2
  fstInner1 = Lift (Comp Fst (Comp Snd Snd))

  sndInner1 : Fun2
  sndInner1 = Lift (Comp Snd (Comp Snd Snd))

  -- Reduction lemma for fstInner1 / sndInner1 at a canonical 3-deep
  -- Pair first argument.
  fstInner1Red : (uC vC x2 : Term) ->
    Deriv (atomic (eqn
      (ap2 fstInner1
        (ap2 Pair (reify tagAp2)
          (ap2 Pair (reify (codeF2 Pair)) (ap2 Pair uC vC))) x2)
      uC))
  fstInner1Red uC vC x2 =
    let x1C : Term
        x1C = ap2 Pair (reify tagAp2)
                (ap2 Pair (reify (codeF2 Pair)) (ap2 Pair uC vC))
        mid : Term
        mid = ap2 Pair (reify (codeF2 Pair)) (ap2 Pair uC vC)
    in ruleTrans (axLift (Comp Fst (Comp Snd Snd)) x1C x2)
         (ruleTrans (axComp Fst (Comp Snd Snd) x1C)
           (ruleTrans (cong1 Fst (axComp Snd Snd x1C))
             (ruleTrans (cong1 Fst (cong1 Snd (axSnd (reify tagAp2) mid)))
               (ruleTrans (cong1 Fst (axSnd (reify (codeF2 Pair)) (ap2 Pair uC vC)))
                          (axFst uC vC)))))

  sndInner1Red : (uC vC x2 : Term) ->
    Deriv (atomic (eqn
      (ap2 sndInner1
        (ap2 Pair (reify tagAp2)
          (ap2 Pair (reify (codeF2 Pair)) (ap2 Pair uC vC))) x2)
      vC))
  sndInner1Red uC vC x2 =
    let x1C : Term
        x1C = ap2 Pair (reify tagAp2)
                (ap2 Pair (reify (codeF2 Pair)) (ap2 Pair uC vC))
        mid : Term
        mid = ap2 Pair (reify (codeF2 Pair)) (ap2 Pair uC vC)
    in ruleTrans (axLift (Comp Snd (Comp Snd Snd)) x1C x2)
         (ruleTrans (axComp Snd (Comp Snd Snd) x1C)
           (ruleTrans (cong1 Snd (axComp Snd Snd x1C))
             (ruleTrans (cong1 Snd (cong1 Snd (axSnd (reify tagAp2) mid)))
               (ruleTrans (cong1 Snd (axSnd (reify (codeF2 Pair)) (ap2 Pair uC vC)))
                          (axSnd uC vC)))))

D2IfLfN : Fun2
D2IfLfN = Fan (Lift (KT (reify (natCode n12))))
              (Fan fstInner1 (Fan sndInner1 snd2X2 Pair) Pair)
              Pair

d2IfLfNRed : (x y a b : Term) ->
  Deriv (atomic (eqn (ap2 D2IfLfN (reify (code (ap2 Pair x y)))
                                   (reify (code (ap2 Pair a b))))
                     (encAxIfLfN (reify (code x)) (reify (code y))
                                 (reify (code a)) (reify (code b)))))
d2IfLfNRed x y a b =
  let xC : Term ; xC = reify (code x)
      yC : Term ; yC = reify (code y)
      aC : Term ; aC = reify (code a)
      bC : Term ; bC = reify (code b)
      x1C : Term ; x1C = reify (code (ap2 Pair x y))
      x2C : Term ; x2C = reify (code (ap2 Pair a b))
      tagR : Term ; tagR = reify (natCode n12)
      -- Tag side.
      s1 : Deriv (atomic (eqn (ap2 (Lift (KT tagR)) x1C x2C) tagR))
      s1 = ruleTrans (axLift (KT tagR) x1C x2C) (axKT tagR x1C)
      -- Innermost Pair (sndInner1, snd2X2) — extract yC and Pair aC bC.
      s2a : Deriv (atomic (eqn (ap2 sndInner1 x1C x2C) yC))
      s2a = sndInner1Red xC yC x2C
      s2b : Deriv (atomic (eqn (ap2 snd2X2 x1C x2C) (ap2 Pair aC bC)))
      s2b = snd2X2Red x1C aC bC
      s2Fan : Deriv (atomic (eqn (ap2 (Fan sndInner1 snd2X2 Pair) x1C x2C)
                                  (ap2 Pair (ap2 sndInner1 x1C x2C)
                                            (ap2 snd2X2 x1C x2C))))
      s2Fan = axFan sndInner1 snd2X2 Pair x1C x2C
      s2 : Deriv (atomic (eqn (ap2 (Fan sndInner1 snd2X2 Pair) x1C x2C)
                              (ap2 Pair yC (ap2 Pair aC bC))))
      s2 = ruleTrans s2Fan
             (ruleTrans (congL Pair (ap2 snd2X2 x1C x2C) s2a)
                        (congR Pair yC s2b))
      -- Outer Pair (fstInner1, above) — extract xC and inner pair.
      s3a : Deriv (atomic (eqn (ap2 fstInner1 x1C x2C) xC))
      s3a = fstInner1Red xC yC x2C
      s3Fan : Deriv (atomic (eqn (ap2 (Fan fstInner1 (Fan sndInner1 snd2X2 Pair) Pair) x1C x2C)
                                  (ap2 Pair (ap2 fstInner1 x1C x2C)
                                            (ap2 (Fan sndInner1 snd2X2 Pair) x1C x2C))))
      s3Fan = axFan fstInner1 (Fan sndInner1 snd2X2 Pair) Pair x1C x2C
      s3 : Deriv (atomic (eqn (ap2 (Fan fstInner1 (Fan sndInner1 snd2X2 Pair) Pair) x1C x2C)
                              (ap2 Pair xC (ap2 Pair yC (ap2 Pair aC bC)))))
      s3 = ruleTrans s3Fan
             (ruleTrans (congL Pair (ap2 (Fan sndInner1 snd2X2 Pair) x1C x2C) s3a)
                        (congR Pair xC s2))
      -- Outermost Fan.
      s0 : Deriv (atomic (eqn (ap2 D2IfLfN x1C x2C)
                              (ap2 Pair
                                (ap2 (Lift (KT tagR)) x1C x2C)
                                (ap2 (Fan fstInner1 (Fan sndInner1 snd2X2 Pair) Pair)
                                     x1C x2C))))
      s0 = axFan (Lift (KT tagR))
                 (Fan fstInner1 (Fan sndInner1 snd2X2 Pair) Pair)
                 Pair x1C x2C
  in ruleTrans s0
       (ruleTrans (congL Pair (ap2 (Fan fstInner1 (Fan sndInner1 snd2X2 Pair) Pair) x1C x2C) s1)
                  (congR Pair tagR s3))

thm13Fun2IfLfN : (x y a b : Term) ->
  Deriv (atomic (eqn (ap1 thmT (ap2 D2IfLfN (reify (code (ap2 Pair x y)))
                                             (reify (code (ap2 Pair a b)))))
                     (reify (codeFormula
                       (atomic (eqn (ap2 IfLf (ap2 Pair x y) (ap2 Pair a b)) b))))))
thm13Fun2IfLfN x y a b =
  let xC : Term ; xC = reify (code x)
      yC : Term ; yC = reify (code y)
      aC : Term ; aC = reify (code a)
      bC : Term ; bC = reify (code b)
  in ruleTrans (cong1 thmT (d2IfLfNRed x y a b)) (encAxIfLfNCorr xC yC aC bC)

------------------------------------------------------------------------
-- Fun2 base case:  TreeEqNN .
--
-- axTreeEqNN a1 a2 b1 b2 :
--   ap2 TreeEq (Pair a1 a2) (Pair b1 b2)
--     = ap2 IfLf (ap2 TreeEq a1 b1) (ap2 Pair (ap2 TreeEq a2 b2) (ap2 Pair O O)) .
-- Same extraction structure as IfLfN -- only the tag differs (n16
-- versus n12) and the encoded body orders the pulled-out pieces as
--  (a1C, a2C, b1C, b2C) .  We reuse fstInner1 / sndInner1 / snd2X2 .

D2TreeEqNN : Fun2
D2TreeEqNN = Fan (Lift (KT (reify (natCode n16))))
                 (Fan fstInner1 (Fan sndInner1 snd2X2 Pair) Pair)
                 Pair

d2TreeEqNNRed : (a1 a2 b1 b2 : Term) ->
  Deriv (atomic (eqn (ap2 D2TreeEqNN (reify (code (ap2 Pair a1 a2)))
                                      (reify (code (ap2 Pair b1 b2))))
                     (encAxTreeEqNN (reify (code a1)) (reify (code a2))
                                    (reify (code b1)) (reify (code b2)))))
d2TreeEqNNRed a1 a2 b1 b2 =
  let a1C : Term ; a1C = reify (code a1)
      a2C : Term ; a2C = reify (code a2)
      b1C : Term ; b1C = reify (code b1)
      b2C : Term ; b2C = reify (code b2)
      x1C : Term ; x1C = reify (code (ap2 Pair a1 a2))
      x2C : Term ; x2C = reify (code (ap2 Pair b1 b2))
      tagR : Term ; tagR = reify (natCode n16)
      s1 : Deriv (atomic (eqn (ap2 (Lift (KT tagR)) x1C x2C) tagR))
      s1 = ruleTrans (axLift (KT tagR) x1C x2C) (axKT tagR x1C)
      s2a : Deriv (atomic (eqn (ap2 sndInner1 x1C x2C) a2C))
      s2a = sndInner1Red a1C a2C x2C
      s2b : Deriv (atomic (eqn (ap2 snd2X2 x1C x2C) (ap2 Pair b1C b2C)))
      s2b = snd2X2Red x1C b1C b2C
      s2 : Deriv (atomic (eqn (ap2 (Fan sndInner1 snd2X2 Pair) x1C x2C)
                              (ap2 Pair a2C (ap2 Pair b1C b2C))))
      s2 = ruleTrans (axFan sndInner1 snd2X2 Pair x1C x2C)
             (ruleTrans (congL Pair (ap2 snd2X2 x1C x2C) s2a)
                        (congR Pair a2C s2b))
      s3a : Deriv (atomic (eqn (ap2 fstInner1 x1C x2C) a1C))
      s3a = fstInner1Red a1C a2C x2C
      s3 : Deriv (atomic (eqn (ap2 (Fan fstInner1 (Fan sndInner1 snd2X2 Pair) Pair) x1C x2C)
                              (ap2 Pair a1C (ap2 Pair a2C (ap2 Pair b1C b2C)))))
      s3 = ruleTrans (axFan fstInner1 (Fan sndInner1 snd2X2 Pair) Pair x1C x2C)
             (ruleTrans (congL Pair (ap2 (Fan sndInner1 snd2X2 Pair) x1C x2C) s3a)
                        (congR Pair a1C s2))
      s0 : Deriv (atomic (eqn (ap2 D2TreeEqNN x1C x2C)
                              (ap2 Pair
                                (ap2 (Lift (KT tagR)) x1C x2C)
                                (ap2 (Fan fstInner1 (Fan sndInner1 snd2X2 Pair) Pair)
                                     x1C x2C))))
      s0 = axFan (Lift (KT tagR))
                 (Fan fstInner1 (Fan sndInner1 snd2X2 Pair) Pair)
                 Pair x1C x2C
  in ruleTrans s0
       (ruleTrans (congL Pair (ap2 (Fan fstInner1 (Fan sndInner1 snd2X2 Pair) Pair) x1C x2C) s1)
                  (congR Pair tagR s3))

thm13Fun2TreeEqNN : (a1 a2 b1 b2 : Term) ->
  Deriv (atomic (eqn (ap1 thmT (ap2 D2TreeEqNN (reify (code (ap2 Pair a1 a2)))
                                                (reify (code (ap2 Pair b1 b2)))))
                     (reify (codeFormula
                       (atomic (eqn
                         (ap2 TreeEq (ap2 Pair a1 a2) (ap2 Pair b1 b2))
                         (ap2 IfLf (ap2 TreeEq a1 b1)
                                   (ap2 Pair (ap2 TreeEq a2 b2)
                                             (ap2 Pair O O)))))))))
thm13Fun2TreeEqNN a1 a2 b1 b2 =
  let a1C : Term ; a1C = reify (code a1)
      a2C : Term ; a2C = reify (code a2)
      b1C : Term ; b1C = reify (code b1)
      b2C : Term ; b2C = reify (code b2)
  in ruleTrans (cong1 thmT (d2TreeEqNNRed a1 a2 b1 b2))
               (encAxTreeEqNNCorr a1C a2C b1C b2C)
