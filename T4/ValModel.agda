{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ValModel -- the denotational VALUE MODEL of the equational theory Eq
-- (the addition TRS, T4.EqProvConv : eRO, eRS, eRefl, eSym, eTrans, eSu, eAd1,
-- eAd2).  Every Eq-derivable equation  a = b  is VALID in the value model, i.e.
-- valF a = valF b (T4.ValF).  This file ships the per-rule soundness building
-- blocks; refl/sym/trans are just axRefl/ruleSym/ruleTrans on the value
-- equation, and the two base rewrite rules + the three congruence rules are:
--
--   vRO  :  valF (ad# ze# y)      = valF y                       (0 + y = y)
--   vRS  :  valF (ad# (su# x) y)  = valF (su# (ad# x y))         ((sx)+y = s(x+y))
--   vSu  :  valF t = valF u  =>  valF (su# t) = valF (su# u)
--   vAd1 :  valF a = valF a' =>  valF (ad# a b) = valF (ad# a' b)
--   vAd2 :  valF b = valF b' =>  valF (ad# a b) = valF (ad# a b')
--
-- and the clash:  valF ze# = O  while  valF (su# ze#) = s O , so 0 and s0 have
-- DISTINCT values -- the model refutes  0 = s0 .  This is the semantic core of
-- the object Con(Eq): the soundness induction (over the theorem enumerator)
-- discharges each rule by one of these, and the headline by the clash.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.ValModel where

open import T4.Base

open import T4.ValF using ( valF ; valF_ze# ; valF_su# ; valF_ad# )
open import T4.TrsCodeObj using ( ze# ; su# ; ad# )

open import BRA3.Church using ( sigma ; T33sym ; T35 )
open import BRA3.RuleInst2 using ( ruleInst2 )

------------------------------------------------------------------------
-- SECTION 0.  Equation coding.

codeEqn : Term -> Term -> Term
codeEqn a b = ap2 Pair a b

lhsE : Term -> Term
lhsE e = ap1 Fst e
rhsE : Term -> Term
rhsE e = ap1 Snd e

lhsE_eq : (a b : Term) -> Deriv (eqF (lhsE (codeEqn a b)) a)
lhsE_eq a b = axFst a b
rhsE_eq : (a b : Term) -> Deriv (eqF (rhsE (codeEqn a b)) b)
rhsE_eq a b = axSnd a b

------------------------------------------------------------------------
-- SECTION 1.  The two base rewrite rules are value-sound.

-- rO :  valF (ad# ze# y) = valF y .
--   valF (ad# ze# y) = sigma (valF ze#) (valF y) = sigma O (valF y) = valF y .
vRO : (y : Term) -> Deriv (eqF (ap1 valF (ad# ze# y)) (ap1 valF y))
vRO y =
  ruleTrans (valF_ad# ze# y)
    (ruleTrans (congL sigma (ap1 valF y) valF_ze#)
               (ruleInst 1 (ap1 valF y) T33sym))

-- rS :  valF (ad# (su# x) y) = valF (su# (ad# x y)) .
--   sigma (valF (su# x)) (valF y) = sigma (s (valF x)) (valF y)
--                                 = s (sigma (valF x) (valF y)) = s (valF (ad# x y))
--                                 = valF (su# (ad# x y)) .
vRS : (x y : Term) ->
  Deriv (eqF (ap1 valF (ad# (su# x) y)) (ap1 valF (su# (ad# x y))))
vRS x y =
  ruleTrans (valF_ad# (su# x) y)
    (ruleTrans (congL sigma (ap1 valF y) (valF_su# x))
      (ruleTrans (ruleInst2 0 (ap1 valF x) 1 (ap1 valF y) refl T35)
        (ruleTrans (cong1 s (ruleSym (valF_ad# x y)))
                   (ruleSym (valF_su# (ad# x y))))))

------------------------------------------------------------------------
-- SECTION 2.  The three congruence rules preserve value-equality.

vSu : (tA uA : Term) -> Deriv (eqF (ap1 valF tA) (ap1 valF uA)) ->
  Deriv (eqF (ap1 valF (su# tA)) (ap1 valF (su# uA)))
vSu tA uA e =
  ruleTrans (valF_su# tA) (ruleTrans (cong1 s e) (ruleSym (valF_su# uA)))

vAd1 : (a a' b : Term) -> Deriv (eqF (ap1 valF a) (ap1 valF a')) ->
  Deriv (eqF (ap1 valF (ad# a b)) (ap1 valF (ad# a' b)))
vAd1 a a' b e =
  ruleTrans (valF_ad# a b)
    (ruleTrans (congL sigma (ap1 valF b) e) (ruleSym (valF_ad# a' b)))

vAd2 : (a b b' : Term) -> Deriv (eqF (ap1 valF b) (ap1 valF b')) ->
  Deriv (eqF (ap1 valF (ad# a b)) (ap1 valF (ad# a b')))
vAd2 a b b' e =
  ruleTrans (valF_ad# a b)
    (ruleTrans (congR sigma (ap1 valF a) e) (ruleSym (valF_ad# a b')))

------------------------------------------------------------------------
-- SECTION 3.  The clash:  0 and s0 have distinct values.

vZe : Deriv (eqF (ap1 valF ze#) O)
vZe = valF_ze#

vSuZe : Deriv (eqF (ap1 valF (su# ze#)) (ap1 s O))
vSuZe = ruleTrans (valF_su# ze#) (cong1 s valF_ze#)
