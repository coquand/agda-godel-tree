{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.GammaCtx -- the Carneiro "internalized deduction theorem" kit: a single
-- coded-conjunction context  Cnj A B = neg (imp A (neg B))  with projections,
-- pairing, curry/uncurry, plus depth-1 combinators for reasoning under one
-- conjunction antecedent  Gam .  This replaces the nested-imp CtxKit towers:
-- every step is  imp Gam X  and conjuncts are projected on demand.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.GammaCtx where

open import T4.Base
open import T4.Code using ( falseF )

open import BRA3.Contrapositive
  using ( compI ; liftP ; bComb ; bCombTwo ; identP ; DNE ; axExFalso ; axContrapos )
open import T4.Counting using ( impFalseToNeg_imp )
open import T4.CountingObj using ( swapImp )
open import T4.CtxKit using ( lift2 ; lift3 ; ap2c ; ap3c ; get3a ; get3b ; get3c )
open import T4.Thm12.ImpHelpers using ( impEqTrans ; impCong1 )

private
  negToImpFalse_imp : (X : Formula) -> Deriv (imp (neg X) (imp X falseF))
  negToImpFalse_imp X = swapImp (axExFalso X falseF)

------------------------------------------------------------------------
-- The coded conjunction and its laws.

Cnj : Formula -> Formula -> Formula
Cnj A B = neg (imp A (neg B))

cnjL : (A B : Formula) -> Deriv (imp (Cnj A B) A)
cnjL A B =
  let exf' : Deriv (imp (neg A) (imp A (neg B)))
      exf' = swapImp (axExFalso A (neg B))
      contra : Deriv (imp (neg (imp A (neg B))) (neg (neg A)))
      contra = mp (axContrapos (neg A) (imp A (neg B))) exf'
  in compI contra (DNE A)

cnjR : (A B : Formula) -> Deriv (imp (Cnj A B) B)
cnjR A B =
  let k : Deriv (imp (neg B) (imp A (neg B)))
      k = axK (neg B) A
      contra : Deriv (imp (neg (imp A (neg B))) (neg (neg B)))
      contra = mp (axContrapos (neg B) (imp A (neg B))) k
  in compI contra (DNE B)

cnjPair : (A B : Formula) -> Deriv (imp A (imp B (Cnj A B)))
cnjPair A B =
  let H : Formula
      H = imp A (neg B)
      aA : Deriv (imp A (imp B (imp H A)))
      aA = get3a A B H
      bB : Deriv (imp A (imp B (imp H B)))
      bB = get3b A B H
      hH : Deriv (imp A (imp B (imp H H)))
      hH = get3c A B H
      negB : Deriv (imp A (imp B (imp H (neg B))))
      negB = ap3c hH aA
      negB' : Deriv (imp A (imp B (imp H (imp B falseF))))
      negB' = ap3c (lift3 A B H (negToImpFalse_imp B)) negB
      falseD : Deriv (imp A (imp B (imp H falseF)))
      falseD = ap3c negB' bB
  in ap2c (lift2 A B (impFalseToNeg_imp H)) falseD

cnjUncurry : {A B Cf : Formula} ->
  Deriv (imp A (imp B Cf)) -> Deriv (imp (Cnj A B) Cf)
cnjUncurry {A} {B} {Cf} d =
  bComb (bComb (liftP (Cnj A B) d) (cnjL A B)) (cnjR A B)

cnjCurry : {A B Cf : Formula} ->
  Deriv (imp (Cnj A B) Cf) -> Deriv (imp A (imp B Cf))
cnjCurry {A} {B} {Cf} d = ap2c (lift2 A B d) (cnjPair A B)

------------------------------------------------------------------------
-- Depth-1 reasoning under one context  Gam .

-- weaken a bare fact into the context.
gWeak : (Gam : Formula) {X : Formula} -> Deriv X -> Deriv (imp Gam X)
gWeak Gam d = liftP Gam d

-- modus ponens under the context.
gMp : {Gam A B : Formula} -> Deriv (imp Gam (imp A B)) -> Deriv (imp Gam A) -> Deriv (imp Gam B)
gMp d1 d2 = bComb d1 d2

-- apply a bare implication lemma to a context-fact.
gApply : {Gam A B : Formula} -> Deriv (imp A B) -> Deriv (imp Gam A) -> Deriv (imp Gam B)
gApply {Gam} lemma projA = compI projA lemma

-- equational transitivity / congruence under the context.
gTrans : {Gam : Formula} (a b c : Term) ->
  Deriv (imp Gam (eqF a b)) -> Deriv (imp Gam (eqF b c)) -> Deriv (imp Gam (eqF a c))
gTrans a b c f g = impEqTrans a b c f g

gCong : {Gam : Formula} (f : Fun1) (a b : Term) ->
  Deriv (imp Gam (eqF a b)) -> Deriv (imp Gam (eqF (ap1 f a) (ap1 f b)))
gCong f a b d = impCong1 f a b d
