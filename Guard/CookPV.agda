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
