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
  ( encAxI      ; encAxICorr
  ; encAxFst    ; encAxFstCorr
  ; encAxSnd    ; encAxSndCorr
  ; encAxKT     ; encAxKTCorr
  ; encAxConst  ; encAxConstCorr
  ; encAxIfLfL  ; encAxIfLfLCorr
  )

private
  n1  : Nat ; n1  = suc zero
  n2  : Nat ; n2  = suc n1
  n3  : Nat ; n3  = suc n2
  n11 : Nat
  n11 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
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
