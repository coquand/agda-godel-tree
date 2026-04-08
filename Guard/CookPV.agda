{-# OPTIONS --safe --without-K --exact-split #-}

-- CookPV.agda
-- Cook-style definitions and lemmas, following Cook (1975).
--
-- Defines basic PV-like functions as Guard functors:
--   sg    : sign function — sg(O) = O, sg(Pair x y) = falseT
--   notF  : boolean negation — notF(O) = falseT, notF(Pair x y) = O
--   tr    : trim (left projection) — tr(O) = O, tr(Pair x y) = x
--
-- Proves via Schema F:
--   dblNotIsSg : notF(notF(t)) = sg(t) for all t
--
-- Convention: trueT = O, falseT = Pair O O (as in GodelIIFull).

module Guard.CookPV where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce

private
  trueT : Term ; trueT = O
  falseT : Term ; falseT = ap2 Pair O O
  v0 : Term ; v0 = var zero
  v1 : Term ; v1 = var (suc zero)

------------------------------------------------------------------------
-- sg: sign function (Cook 2.14)
--
-- Cook: sg(0) = 0, sg(xi) = 1.
-- Guard: sg(O) = O, sg(Pair x y) = Pair O O.
-- Implementation: sg(t) = IfLf(t, Pair(O, falseT)).

sg : Fun1
sg = Comp2 IfLf I (KT (ap2 Pair O falseT))

sgLf : {hyp : Equation} -> Deriv hyp (eqn (ap1 sg O) O)
sgLf = ruleTrans (axComp2 IfLf I (KT (ap2 Pair O falseT)) O)
       (ruleTrans (congL IfLf (ap1 (KT (ap2 Pair O falseT)) O) (axI O))
       (ruleTrans (congR IfLf O (axKT (ap2 Pair O falseT) O))
       (axIfLfL O falseT)))

sgNd : (x y : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap1 sg (ap2 Pair x y)) falseT)
sgNd x y =
  ruleTrans (axComp2 IfLf I (KT (ap2 Pair O falseT)) (ap2 Pair x y))
  (ruleTrans (congL IfLf (ap1 (KT (ap2 Pair O falseT)) (ap2 Pair x y))
               (axI (ap2 Pair x y)))
  (ruleTrans (congR IfLf (ap2 Pair x y)
               (axKT (ap2 Pair O falseT) (ap2 Pair x y)))
  (axIfLfN x y O falseT)))

------------------------------------------------------------------------
-- notF: boolean negation (Cook's negation on {0,1})
--
-- notF(O) = falseT, notF(Pair x y) = O.
-- Implementation: notF(t) = IfLf(t, Pair(falseT, O)).

notF : Fun1
notF = Comp2 IfLf I (KT (ap2 Pair falseT O))

notFLf : {hyp : Equation} -> Deriv hyp (eqn (ap1 notF O) falseT)
notFLf = ruleTrans (axComp2 IfLf I (KT (ap2 Pair falseT O)) O)
         (ruleTrans (congL IfLf (ap1 (KT (ap2 Pair falseT O)) O) (axI O))
         (ruleTrans (congR IfLf O (axKT (ap2 Pair falseT O) O))
         (axIfLfL falseT O)))

notFNd : (x y : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap1 notF (ap2 Pair x y)) O)
notFNd x y =
  ruleTrans (axComp2 IfLf I (KT (ap2 Pair falseT O)) (ap2 Pair x y))
  (ruleTrans (congL IfLf (ap1 (KT (ap2 Pair falseT O)) (ap2 Pair x y))
               (axI (ap2 Pair x y)))
  (ruleTrans (congR IfLf (ap2 Pair x y)
               (axKT (ap2 Pair falseT O) (ap2 Pair x y)))
  (axIfLfN x y falseT O)))

------------------------------------------------------------------------
-- tr: trim / left projection (Cook's TR)
--
-- Cook: TR(0) = 0, TR(xi) = x.
-- Guard: tr(O) = O, tr(Pair x y) = x.
-- Implementation: tr = Rec O (Lift Fst).
-- Step: Lift Fst (Pair a b) (Pair(tr a)(tr b)) = Fst(Pair a b) = a.

tr : Fun1
tr = Rec O (Lift Fst)

trLf : {hyp : Equation} -> Deriv hyp (eqn (ap1 tr O) O)
trLf = axRecLf O (Lift Fst)

trNd : (x y : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap1 tr (ap2 Pair x y)) x)
trNd x y =
  ruleTrans (axRecNd O (Lift Fst) x y)
  (ruleTrans (liftRed Fst (ap2 Pair x y) (ap2 Pair (ap1 tr x) (ap1 tr y)))
  (axFst x y))

------------------------------------------------------------------------
-- Double negation = sign, via Schema F.
--
-- f = Comp notF notF, g = sg.
-- Both satisfy base O -> O and step Pair x y -> falseT.
-- Schema F gives: f(t) = g(t) for all t.

private
  dblNot : Fun1
  dblNot = Comp notF notF

  dblNotStep : Fun2
  dblNotStep = Lift (KT falseT)

  fBase : {hyp : Equation} -> Deriv hyp (eqn (ap1 dblNot O) O)
  fBase = ruleTrans (axComp notF notF O)
          (ruleTrans (cong1 notF notFLf) (notFNd O O))

  fStep : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 dblNot (ap2 Pair v0 v1))
                   (ap2 dblNotStep (ap2 Pair v0 v1)
                        (ap2 Pair (ap1 dblNot v0) (ap1 dblNot v1))))
  fStep =
    ruleTrans (axComp notF notF (ap2 Pair v0 v1))
    (ruleTrans (cong1 notF (notFNd v0 v1))
    (ruleTrans notFLf
    (ruleSym (ruleTrans (liftRed (KT falseT) (ap2 Pair v0 v1)
               (ap2 Pair (ap1 dblNot v0) (ap1 dblNot v1)))
             (axKT falseT (ap2 Pair v0 v1))))))

  gBase : {hyp : Equation} -> Deriv hyp (eqn (ap1 sg O) O)
  gBase = sgLf

  gStep : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 sg (ap2 Pair v0 v1))
                   (ap2 dblNotStep (ap2 Pair v0 v1)
                        (ap2 Pair (ap1 sg v0) (ap1 sg v1))))
  gStep =
    ruleTrans (sgNd v0 v1)
    (ruleSym (ruleTrans (liftRed (KT falseT) (ap2 Pair v0 v1)
               (ap2 Pair (ap1 sg v0) (ap1 sg v1)))
             (axKT falseT (ap2 Pair v0 v1))))

-- notF(notF(t)) = sg(t) for all t.
dblNotIsSg : {hyp : Equation} ->
  Deriv hyp (eqn (ap1 dblNot (var zero)) (ap1 sg (var zero)))
dblNotIsSg = ruleF dblNot sg O dblNotStep fBase fStep gBase gStep

------------------------------------------------------------------------
-- andF: boolean conjunction (Cook-style)
--
-- andF(O, y) = y,  andF(Pair a b, y) = O.
-- Convention: trueT = O, falseT = Pair O O.
-- So and(true,y)=y, and(false,y)=true=O... wait, that is wrong.
-- Actually with Cook's convention: true=O false=PairOO:
--   and(true, true) = O = true   good
--   and(true, false) = PairOO = false  good
--   and(false, y) = should be false = PairOO
--
-- So: andF(O, y) = y,  andF(Pair a b, y) = falseT.
-- Implementation: IfLf(x, Pair(y, falseT))
-- As Fan: andF = Fan (Lift I) (Fan (Post Snd Pair) (Lift (KT falseT)) Pair) IfLf

andF : Fun2
andF = Fan (Lift I) (Fan (Post Snd Pair) (Lift (KT falseT)) Pair) IfLf

andFLf : (y : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 andF O y) y)
andFLf y =
  ruleTrans (fanRed (Lift I) (Fan (Post Snd Pair) (Lift (KT falseT)) Pair) IfLf O y)
  (ruleTrans (congL IfLf (ap2 (Fan (Post Snd Pair) (Lift (KT falseT)) Pair) O y) (liftRed I O y))
  (ruleTrans (congL IfLf (ap2 (Fan (Post Snd Pair) (Lift (KT falseT)) Pair) O y) (axI O))
  (ruleTrans (congR IfLf O
    (ruleTrans (fanRed (Post Snd Pair) (Lift (KT falseT)) Pair O y)
    (ruleTrans (congL Pair (ap2 (Lift (KT falseT)) O y)
      (ruleTrans (postRed Snd Pair O y) (axSnd O y)))
    (congR Pair y (constF2Red falseT O y)))))
  (axIfLfL y falseT))))

andFNd : (a b y : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 andF (ap2 Pair a b) y) falseT)
andFNd a b y =
  ruleTrans (fanRed (Lift I) (Fan (Post Snd Pair) (Lift (KT falseT)) Pair) IfLf (ap2 Pair a b) y)
  (ruleTrans (congL IfLf (ap2 (Fan (Post Snd Pair) (Lift (KT falseT)) Pair) (ap2 Pair a b) y)
    (ruleTrans (liftRed I (ap2 Pair a b) y) (axI (ap2 Pair a b))))
  (ruleTrans (congR IfLf (ap2 Pair a b)
    (ruleTrans (fanRed (Post Snd Pair) (Lift (KT falseT)) Pair (ap2 Pair a b) y)
    (ruleTrans (congL Pair (ap2 (Lift (KT falseT)) (ap2 Pair a b) y)
      (ruleTrans (postRed Snd Pair (ap2 Pair a b) y) (axSnd (ap2 Pair a b) y)))
    (congR Pair y (constF2Red falseT (ap2 Pair a b) y)))))
  (axIfLfN a b y falseT)))

------------------------------------------------------------------------
-- orF: boolean disjunction
--
-- orF(O, y) = O (= trueT),  orF(Pair a b, y) = y.
-- So or(true,y)=true, or(false,y)=y.  Correct.
-- Implementation: IfLf(x, Pair(trueT, y))
-- As Fan: orF = Fan (Lift I) (Fan (Lift (KT trueT)) (Post Snd Pair) Pair) IfLf

orF : Fun2
orF = Fan (Lift I) (Fan (Lift (KT trueT)) (Post Snd Pair) Pair) IfLf

orFLf : (y : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 orF O y) trueT)
orFLf y =
  ruleTrans (fanRed (Lift I) (Fan (Lift (KT trueT)) (Post Snd Pair) Pair) IfLf O y)
  (ruleTrans (congL IfLf (ap2 (Fan (Lift (KT trueT)) (Post Snd Pair) Pair) O y)
    (ruleTrans (liftRed I O y) (axI O)))
  (ruleTrans (congR IfLf O
    (ruleTrans (fanRed (Lift (KT trueT)) (Post Snd Pair) Pair O y)
    (ruleTrans (congL Pair (ap2 (Post Snd Pair) O y)
      (constF2Red trueT O y))
    (congR Pair trueT
      (ruleTrans (postRed Snd Pair O y) (axSnd O y))))))
  (axIfLfL trueT y)))

orFNd : (a b y : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 orF (ap2 Pair a b) y) y)
orFNd a b y =
  ruleTrans (fanRed (Lift I) (Fan (Lift (KT trueT)) (Post Snd Pair) Pair) IfLf (ap2 Pair a b) y)
  (ruleTrans (congL IfLf (ap2 (Fan (Lift (KT trueT)) (Post Snd Pair) Pair) (ap2 Pair a b) y)
    (ruleTrans (liftRed I (ap2 Pair a b) y) (axI (ap2 Pair a b))))
  (ruleTrans (congR IfLf (ap2 Pair a b)
    (ruleTrans (fanRed (Lift (KT trueT)) (Post Snd Pair) Pair (ap2 Pair a b) y)
    (ruleTrans (congL Pair (ap2 (Post Snd Pair) (ap2 Pair a b) y)
      (constF2Red trueT (ap2 Pair a b) y))
    (congR Pair trueT
      (ruleTrans (postRed Snd Pair (ap2 Pair a b) y) (axSnd (ap2 Pair a b) y))))))
  (axIfLfN a b trueT y)))

------------------------------------------------------------------------
-- implF: boolean implication (Cook-style)
--
-- implF(O, y) = y,  implF(Pair a b, y) = O (= trueT).
-- So impl(true,y)=y, impl(false,y)=true.  Correct: false => anything = true.
-- Note: implF has the same table as andF! Because:
--   impl(x,y) = or(not(x), y) = and(x,y) when we think of it differently...
-- Wait: impl(true,y) = y. and(true,y) = y. impl(false,y) = true. and(false,y) = false.
-- These are different! impl(false,y) = true = O but and(false,y) = false = PairOO.
--
-- So: implF(O, y) = y,  implF(Pair a b, y) = trueT = O.
-- Implementation: IfLf(x, Pair(y, trueT))

implF : Fun2
implF = Fan (Lift I) (Fan (Post Snd Pair) (Lift (KT trueT)) Pair) IfLf

implFLf : (y : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 implF O y) y)
implFLf y =
  ruleTrans (fanRed (Lift I) (Fan (Post Snd Pair) (Lift (KT trueT)) Pair) IfLf O y)
  (ruleTrans (congL IfLf (ap2 (Fan (Post Snd Pair) (Lift (KT trueT)) Pair) O y)
    (ruleTrans (liftRed I O y) (axI O)))
  (ruleTrans (congR IfLf O
    (ruleTrans (fanRed (Post Snd Pair) (Lift (KT trueT)) Pair O y)
    (ruleTrans (congL Pair (ap2 (Lift (KT trueT)) O y)
      (ruleTrans (postRed Snd Pair O y) (axSnd O y)))
    (congR Pair y (constF2Red trueT O y)))))
  (axIfLfL y trueT)))

implFNd : (a b y : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 implF (ap2 Pair a b) y) trueT)
implFNd a b y =
  ruleTrans (fanRed (Lift I) (Fan (Post Snd Pair) (Lift (KT trueT)) Pair) IfLf (ap2 Pair a b) y)
  (ruleTrans (congL IfLf (ap2 (Fan (Post Snd Pair) (Lift (KT trueT)) Pair) (ap2 Pair a b) y)
    (ruleTrans (liftRed I (ap2 Pair a b) y) (axI (ap2 Pair a b))))
  (ruleTrans (congR IfLf (ap2 Pair a b)
    (ruleTrans (fanRed (Post Snd Pair) (Lift (KT trueT)) Pair (ap2 Pair a b) y)
    (ruleTrans (congL Pair (ap2 (Lift (KT trueT)) (ap2 Pair a b) y)
      (ruleTrans (postRed Snd Pair (ap2 Pair a b) y) (axSnd (ap2 Pair a b) y)))
    (congR Pair y (constF2Red trueT (ap2 Pair a b) y)))))
  (axIfLfN a b y trueT)))

------------------------------------------------------------------------
-- De Morgan: not(and(x,y)) = or(not(x), not(y)), via Schema F.
--
-- We prove this by defining:
--   f(t) = notF(andF(t, v1))   [free var v1 for the second argument]
--   g(t) = orF(notF(t), notF(v1))
-- and showing both satisfy the same Rec specification,
-- then Schema F gives f = g.
--
-- Base (t = O):
--   f(O) = notF(andF(O, v1)) = notF(v1)
--   g(O) = orF(notF(O), notF(v1)) = orF(falseT, notF(v1)) = notF(v1)
--
-- Step (t = Pair a b):
--   f(Pair a b) = notF(andF(Pair a b, v1)) = notF(falseT) = O = trueT
--   g(Pair a b) = orF(notF(Pair a b), notF(v1)) = orF(O, notF(v1)) = O = trueT
--
-- Both step cases give trueT = O, which is constant in the recursion variable.
-- So the step functor is: s(t, recs) = trueT = Lift (KT trueT).
-- Wait — but the step needs to match. Let me use the constant step.

private
  -- De Morgan helper: f(t) = notF(andF(t, v1))
  -- This is a Fun1 in t (with v1 free).
  dmF : Fun1
  dmF = Comp notF (Comp2 andF I (KT v1))

  -- g(t) = orF(notF(t), notF(v1))
  dmG : Fun1
  dmG = Comp2 orF notF (KT (ap1 notF v1))

  dmStep : Fun2
  dmStep = Lift (KT trueT)

  dmFBase : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 dmF O) (ap1 notF v1))
  dmFBase =
    ruleTrans (axComp notF (Comp2 andF I (KT v1)) O)
    (ruleTrans (cong1 notF (axComp2 andF I (KT v1) O))
    (ruleTrans (cong1 notF (congL andF (ap1 (KT v1) O) (axI O)))
    (ruleTrans (cong1 notF (congR andF O (axKT v1 O)))
    (cong1 notF (andFLf v1)))))

  dmGBase : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 dmG O) (ap1 notF v1))
  dmGBase =
    ruleTrans (axComp2 orF notF (KT (ap1 notF v1)) O)
    (ruleTrans (congL orF (ap1 (KT (ap1 notF v1)) O) notFLf)
    (ruleTrans (congR orF falseT (axKT (ap1 notF v1) O))
    (orFNd O O (ap1 notF v1))))

  dmFStep : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 dmF (ap2 Pair v0 v1))
                   (ap2 dmStep (ap2 Pair v0 v1)
                        (ap2 Pair (ap1 dmF v0) (ap1 dmF v1))))
  dmFStep =
    ruleTrans (axComp notF (Comp2 andF I (KT v1)) (ap2 Pair v0 v1))
    (ruleTrans (cong1 notF (axComp2 andF I (KT v1) (ap2 Pair v0 v1)))
    (ruleTrans (cong1 notF (congL andF (ap1 (KT v1) (ap2 Pair v0 v1))
                              (axI (ap2 Pair v0 v1))))
    (ruleTrans (cong1 notF (congR andF (ap2 Pair v0 v1)
                              (axKT v1 (ap2 Pair v0 v1))))
    (ruleTrans (cong1 notF (andFNd v0 v1 v1))
    (ruleTrans (notFNd O O)
    (ruleSym (constF2Red trueT (ap2 Pair v0 v1)
               (ap2 Pair (ap1 dmF v0) (ap1 dmF v1)))))))))

  dmGStep : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 dmG (ap2 Pair v0 v1))
                   (ap2 dmStep (ap2 Pair v0 v1)
                        (ap2 Pair (ap1 dmG v0) (ap1 dmG v1))))
  dmGStep =
    ruleTrans (axComp2 orF notF (KT (ap1 notF v1)) (ap2 Pair v0 v1))
    (ruleTrans (congL orF (ap1 (KT (ap1 notF v1)) (ap2 Pair v0 v1))
                  (notFNd v0 v1))
    (ruleTrans (congR orF O (axKT (ap1 notF v1) (ap2 Pair v0 v1)))
    (ruleTrans (orFLf (ap1 notF v1))
    (ruleSym (constF2Red trueT (ap2 Pair v0 v1)
               (ap2 Pair (ap1 dmG v0) (ap1 dmG v1)))))))

-- De Morgan's law: not(and(t, v1)) = or(not(t), not(v1)) for all t.
-- (v1 is free — this holds for all values of the second argument.)
deMorgan : {hyp : Equation} ->
  Deriv hyp (eqn (ap1 dmF v0) (ap1 dmG v0))
deMorgan = ruleF dmF dmG (ap1 notF v1) dmStep dmFBase dmFStep dmGBase dmGStep

------------------------------------------------------------------------
-- Excluded middle: or(t, not(t)) = trueT for all t, via Schema F.
--
-- emF(t) = orF(t, notF(t))
-- emG(t) = KT trueT (t) = trueT
--
-- Base: emF(O) = orF(O, notF(O)) = orF(O, falseT) = trueT.
-- Step: emF(Pair a b) = orF(Pair a b, notF(Pair a b)) = orF(Pair a b, O) = O = trueT.
-- Both reduce to trueT, matching KT trueT.

private
  emF : Fun1
  emF = Comp2 orF I notF

  emStep : Fun2
  emStep = Lift (KT trueT)

  emFBase : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 emF O) trueT)
  emFBase =
    ruleTrans (axComp2 orF I notF O)
    (ruleTrans (congL orF (ap1 notF O) (axI O))
    (ruleTrans (congR orF O notFLf)
    (orFLf falseT)))

  emGBase : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (KT trueT) O) trueT)
  emGBase = axKT trueT O

  emFStep : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 emF (ap2 Pair v0 v1))
                   (ap2 emStep (ap2 Pair v0 v1)
                        (ap2 Pair (ap1 emF v0) (ap1 emF v1))))
  emFStep =
    ruleTrans (axComp2 orF I notF (ap2 Pair v0 v1))
    (ruleTrans (congL orF (ap1 notF (ap2 Pair v0 v1)) (axI (ap2 Pair v0 v1)))
    (ruleTrans (congR orF (ap2 Pair v0 v1) (notFNd v0 v1))
    (ruleTrans (orFNd v0 v1 trueT)
    (ruleSym (constF2Red trueT (ap2 Pair v0 v1)
               (ap2 Pair (ap1 emF v0) (ap1 emF v1)))))))

  emGStep : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (KT trueT) (ap2 Pair v0 v1))
                   (ap2 emStep (ap2 Pair v0 v1)
                        (ap2 Pair (ap1 (KT trueT) v0) (ap1 (KT trueT) v1))))
  emGStep =
    ruleTrans (axKT trueT (ap2 Pair v0 v1))
    (ruleSym (constF2Red trueT (ap2 Pair v0 v1)
               (ap2 Pair (ap1 (KT trueT) v0) (ap1 (KT trueT) v1))))

-- Excluded middle: or(t, not(t)) = trueT for all t.
excludedMiddle : {hyp : Equation} ->
  Deriv hyp (eqn (ap1 emF v0) (ap1 (KT trueT) v0))
excludedMiddle = ruleF emF (KT trueT) trueT emStep emFBase emFStep emGBase emGStep

------------------------------------------------------------------------
-- Second De Morgan: not(or(t, v1)) = and(not(t), not(v1)), via Schema F.
--
-- dm2F(t) = notF(orF(t, v1)) ;  dm2G(t) = andF(notF(t), notF(v1))
-- Both have base falseT and step notF(v1).
-- Step functor: Lift (Comp notF Snd).

private
  dm2F : Fun1
  dm2F = Comp notF (Comp2 orF I (KT v1))

  dm2G : Fun1
  dm2G = Comp2 andF notF (KT (ap1 notF v1))

  dm2Step : Fun2
  dm2Step = Lift (Comp notF Snd)

  dm2FBase : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 dm2F O) falseT)
  dm2FBase =
    ruleTrans (axComp notF (Comp2 orF I (KT v1)) O)
    (ruleTrans (cong1 notF (axComp2 orF I (KT v1) O))
    (ruleTrans (cong1 notF (congL orF (ap1 (KT v1) O) (axI O)))
    (ruleTrans (cong1 notF (congR orF O (axKT v1 O)))
    (ruleTrans (cong1 notF (orFLf v1))
    notFLf))))

  dm2GBase : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 dm2G O) falseT)
  dm2GBase =
    ruleTrans (axComp2 andF notF (KT (ap1 notF v1)) O)
    (ruleTrans (congL andF (ap1 (KT (ap1 notF v1)) O) notFLf)
    (ruleTrans (congR andF falseT (axKT (ap1 notF v1) O))
    (andFNd O O (ap1 notF v1))))

  dm2FStep : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 dm2F (ap2 Pair v0 v1))
                   (ap2 dm2Step (ap2 Pair v0 v1)
                        (ap2 Pair (ap1 dm2F v0) (ap1 dm2F v1))))
  dm2FStep =
    ruleTrans (axComp notF (Comp2 orF I (KT v1)) (ap2 Pair v0 v1))
    (ruleTrans (cong1 notF (axComp2 orF I (KT v1) (ap2 Pair v0 v1)))
    (ruleTrans (cong1 notF (congL orF (ap1 (KT v1) (ap2 Pair v0 v1))
                              (axI (ap2 Pair v0 v1))))
    (ruleTrans (cong1 notF (congR orF (ap2 Pair v0 v1) (axKT v1 (ap2 Pair v0 v1))))
    (ruleTrans (cong1 notF (orFNd v0 v1 v1))
    (ruleSym (ruleTrans (liftRed (Comp notF Snd) (ap2 Pair v0 v1)
               (ap2 Pair (ap1 dm2F v0) (ap1 dm2F v1)))
             (ruleTrans (axComp notF Snd (ap2 Pair v0 v1))
             (cong1 notF (axSnd v0 v1)))))))))

  dm2GStep : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 dm2G (ap2 Pair v0 v1))
                   (ap2 dm2Step (ap2 Pair v0 v1)
                        (ap2 Pair (ap1 dm2G v0) (ap1 dm2G v1))))
  dm2GStep =
    ruleTrans (axComp2 andF notF (KT (ap1 notF v1)) (ap2 Pair v0 v1))
    (ruleTrans (congL andF (ap1 (KT (ap1 notF v1)) (ap2 Pair v0 v1))
                  (notFNd v0 v1))
    (ruleTrans (congR andF trueT (axKT (ap1 notF v1) (ap2 Pair v0 v1)))
    (ruleTrans (andFLf (ap1 notF v1))
    (ruleSym (ruleTrans (liftRed (Comp notF Snd) (ap2 Pair v0 v1)
               (ap2 Pair (ap1 dm2G v0) (ap1 dm2G v1)))
             (ruleTrans (axComp notF Snd (ap2 Pair v0 v1))
             (cong1 notF (axSnd v0 v1))))))))

-- Second De Morgan: not(or(t, v1)) = and(not(t), not(v1)) for all t.
deMorgan2 : {hyp : Equation} ->
  Deriv hyp (eqn (ap1 dm2F v0) (ap1 dm2G v0))
deMorgan2 = ruleF dm2F dm2G falseT dm2Step dm2FBase dm2FStep dm2GBase dm2GStep
