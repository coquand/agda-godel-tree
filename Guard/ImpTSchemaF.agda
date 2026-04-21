{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.ImpTSchemaF -- Schema-F derivations of impT reflexivity and
-- vacuous-consequent laws.
--
-- impT A B = IfLf A (Pair B O).  The laws  impT A A = trueT  and
-- impT A trueT = trueT  hold for ARBITRARY A -- both branches of A's
-- head shape (O and Pair) reduce to O via  axIfLfL / axIfLfN .  The
-- equational derivations case-split via Schema F (ruleF), exactly as
-- treeEqSelf proves TreeEq A A = O from ruleF.
--
-- These are the Goodstein-style equational reflexivity laws needed to
-- build Rose's Lemma 1 in object-level impT form.  No new axioms, no
-- postulates, no holes.

module Guard.ImpTSchemaF where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.ImpT

------------------------------------------------------------------------
-- Local abbreviations.

private
  v0T : Term ; v0T = var zero
  v1T : Term ; v1T = var (suc zero)
  pv  : Term ; pv  = ap2 Pair v0T v1T

------------------------------------------------------------------------
-- The constant-O Fun1 used as the RHS of both Schema-F applications.

zFun : Fun1
zFun = KT O

zFunReduces : (A : Term) {hyp : Equation} ->
  Deriv hyp (eqn (ap1 zFun A) O)
zFunReduces A = axKT O A

------------------------------------------------------------------------
-- The universal step Fun2:  s(a, b) = O  for all a, b.
--
-- s = Post (KT O) Pair :   ap2 s a b  -ax-  ap1 (KT O) (ap2 Pair a b)
--                         -ax-  O .

sFun : Fun2
sFun = Post (KT O) Pair

sFunReduces : (a b : Term) {hyp : Equation} ->
  Deriv hyp (eqn (ap2 sFun a b) O)
sFunReduces a b =
  ruleTrans (axPost (KT O) Pair a b) (axKT O (ap2 Pair a b))

------------------------------------------------------------------------
-- Shared Schema-F skeleton: for any Fun1  fF  such that  fF(O) = O
-- and  fF(Pair v0 v1) = O  (both established via Deriv premises), ruleF
-- concludes  fF (var 0) = zFun (var 0) = O .
--
-- The step-case premise for  fF  is always  fF(Pair v0 v1) = sFun(..)
-- with  sFun(..) = O , so  fF(Pair v0 v1) = O  suffices.

-- RHS of the Schema-F step premise (same for f and g, since sFun
-- ignores its second argument).
sStepRHS : (fF : Fun1) -> Term
sStepRHS fF = ap2 sFun pv (ap2 Pair (ap1 fF v0T) (ap1 fF v1T))

-- The step premise  s(Pair v0 v1, Pair (f v0) (f v1)) = O  holds for
-- any  f , since s ignores its second argument.
sStepReducesToO : (fF : Fun1) {hyp : Equation} ->
  Deriv hyp (eqn (sStepRHS fF) O)
sStepReducesToO fF = sFunReduces pv (ap2 Pair (ap1 fF v0T) (ap1 fF v1T))

-- Base case for g = zFun:  zFun(O) = O .
zFunBase : {hyp : Equation} -> Deriv hyp (eqn (ap1 zFun O) O)
zFunBase = zFunReduces O

-- Step case for g = zFun:  zFun(Pair v0 v1) = sStepRHS zFun .
-- Both sides = O .
zFunStep : {hyp : Equation} ->
  Deriv hyp (eqn (ap1 zFun pv) (sStepRHS zFun))
zFunStep = ruleTrans (zFunReduces pv) (ruleSym (sStepReducesToO zFun))

------------------------------------------------------------------------
-- Lemma A: impTSelf -- impT A A = trueT  for any A.
--
-- f(A) = impT A A = IfLf A (Pair A O) as Fun1.

impTSelfFun : Fun1
impTSelfFun = Comp2 IfLf I (Comp2 Pair I (KT O))

-- Unfolding:  ap1 impTSelfFun A = impT A A.
impTSelfFunUnfold : (A : Term) {hyp : Equation} ->
  Deriv hyp (eqn (ap1 impTSelfFun A) (impT A A))
impTSelfFunUnfold A =
  ruleTrans (axComp2 IfLf I (Comp2 Pair I (KT O)) A)
  (ruleTrans (congL IfLf (ap1 (Comp2 Pair I (KT O)) A) (axI A))
  (congR IfLf A
    (ruleTrans (axComp2 Pair I (KT O) A)
    (ruleTrans (congL Pair (ap1 (KT O) A) (axI A))
               (congR Pair A (axKT O A))))))

-- Base:  ap1 impTSelfFun O = O  via unfold + axIfLfL.
impTSelfFunBase : {hyp : Equation} ->
  Deriv hyp (eqn (ap1 impTSelfFun O) O)
impTSelfFunBase =
  ruleTrans (impTSelfFunUnfold O) (axIfLfL O O)

-- Step:  ap1 impTSelfFun (Pair v0 v1) = sStepRHS impTSelfFun .
-- Both reduce to O :  LHS via unfold + axIfLfN ;  RHS via sStepReducesToO.
impTSelfFunStep : {hyp : Equation} ->
  Deriv hyp (eqn (ap1 impTSelfFun pv) (sStepRHS impTSelfFun))
impTSelfFunStep =
  ruleTrans lhsIsO (ruleSym (sStepReducesToO impTSelfFun))
  where
  lhsIsO : _
  lhsIsO =
    ruleTrans (impTSelfFunUnfold pv) (axIfLfN v0T v1T pv O)

-- Schema F:  ap1 impTSelfFun (var 0) = ap1 zFun (var 0) = O .
impTSelfRuleF : {hyp : Equation} ->
  Deriv hyp (eqn (ap1 impTSelfFun v0T) (ap1 zFun v0T))
impTSelfRuleF = ruleF impTSelfFun zFun O sFun
  impTSelfFunBase impTSelfFunStep zFunBase zFunStep

-- Bridge to  impT v0T v0T = trueT .
impTSelfAtVarZero : {hyp : Equation} ->
  Deriv hyp (eqn (impT v0T v0T) trueT)
impTSelfAtVarZero =
  ruleTrans (ruleSym (impTSelfFunUnfold v0T))
    (ruleTrans impTSelfRuleF (zFunReduces v0T))

-- Specialize to arbitrary A via ruleInst.
impTSelf : (A : Term) {hyp : Equation} ->
  Deriv hyp (eqn (impT A A) trueT)
impTSelf A = ruleInst zero A impTSelfAtVarZero

------------------------------------------------------------------------
-- Lemma B: impTAnyTrueT -- impT A trueT = trueT  for any A.
--
-- f(A) = impT A trueT = IfLf A (Pair trueT O) = IfLf A (Pair O O) as Fun1.

impTAnyTrueTFun : Fun1
impTAnyTrueTFun = Comp2 IfLf I (KT (ap2 Pair O O))

impTAnyTrueTFunUnfold : (A : Term) {hyp : Equation} ->
  Deriv hyp (eqn (ap1 impTAnyTrueTFun A) (impT A trueT))
impTAnyTrueTFunUnfold A =
  ruleTrans (axComp2 IfLf I (KT (ap2 Pair O O)) A)
  (ruleTrans (congL IfLf (ap1 (KT (ap2 Pair O O)) A) (axI A))
             (congR IfLf A (axKT (ap2 Pair O O) A)))

-- Base:  ap1 impTAnyTrueTFun O = O  via unfold + axIfLfL.
impTAnyTrueTFunBase : {hyp : Equation} ->
  Deriv hyp (eqn (ap1 impTAnyTrueTFun O) O)
impTAnyTrueTFunBase =
  ruleTrans (impTAnyTrueTFunUnfold O) (axIfLfL O O)

-- Step:  ap1 impTAnyTrueTFun (Pair v0 v1) = sStepRHS impTAnyTrueTFun .
-- Both reduce to O.
impTAnyTrueTFunStep : {hyp : Equation} ->
  Deriv hyp (eqn (ap1 impTAnyTrueTFun pv) (sStepRHS impTAnyTrueTFun))
impTAnyTrueTFunStep =
  ruleTrans lhsIsO (ruleSym (sStepReducesToO impTAnyTrueTFun))
  where
  lhsIsO : _
  lhsIsO =
    ruleTrans (impTAnyTrueTFunUnfold pv) (axIfLfN v0T v1T trueT O)

-- Schema F.
impTAnyTrueTRuleF : {hyp : Equation} ->
  Deriv hyp (eqn (ap1 impTAnyTrueTFun v0T) (ap1 zFun v0T))
impTAnyTrueTRuleF = ruleF impTAnyTrueTFun zFun O sFun
  impTAnyTrueTFunBase impTAnyTrueTFunStep zFunBase zFunStep

impTAnyTrueTAtVarZero : {hyp : Equation} ->
  Deriv hyp (eqn (impT v0T trueT) trueT)
impTAnyTrueTAtVarZero =
  ruleTrans (ruleSym (impTAnyTrueTFunUnfold v0T))
    (ruleTrans impTAnyTrueTRuleF (zFunReduces v0T))

impTAnyTrueT : (A : Term) {hyp : Equation} ->
  Deriv hyp (eqn (impT A trueT) trueT)
impTAnyTrueT A = ruleInst zero A impTAnyTrueTAtVarZero

------------------------------------------------------------------------
-- Corollary: impTConsTrue -- given  B = trueT , conclude  impT A B =
-- trueT  for any A.  Bridges "consequent is true at Triv" to
-- "implication is true at Triv" unconditionally in the antecedent.

impTConsTrue : (A B : Term) {hyp : Equation} ->
  Deriv hyp (eqn B trueT) ->
  Deriv hyp (eqn (impT A B) trueT)
impTConsTrue A B dB =
  ruleTrans (congR IfLf A (congL Pair O dB)) (impTAnyTrueT A)

------------------------------------------------------------------------
-- Summary
--
-- Lemmas provided:
--   * impTSelf A      :  impT A A     = trueT   (polymorphic in A)
--   * impTAnyTrueT A  :  impT A trueT = trueT   (polymorphic in A)
--   * impTConsTrue A B dB  : given B = trueT, impT A B = trueT
--
-- Proofs use Schema F (ruleF) with the universal step  sFun = Post
-- (KT O) Pair , mirroring how treeEqSelf proves TreeEq A A = O .  No
-- new axioms, no postulates, no holes.
