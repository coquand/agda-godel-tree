{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.KolmMonusLemmas -- the truncated-subtraction <-> order bridges used by
-- the Berry search:  monus (suc a) b = 0  iff  a < b .

module T4.KolmMonusLemmas where

open import T4.Base
open import T4.KolmEvalMeta using ( predN ; monus )
open import BRA3.RuleInst2  using ( NatLe ; le-zero ; le-suc )
open import T4.SurpriseG2.MetaPigeonhole using
  ( Lt ; ltZ ; ltS ; Or ; inl ; inr ; sucNotZero )

------------------------------------------------------------------------
-- monus (zero) b = 0 ;  monus (suc a) (suc b) = monus a b .

monusZeroLeft : (b : Nat) -> Eq (monus zero b) zero
monusZeroLeft zero    = refl
monusZeroLeft (suc k) = eqCong predN (monusZeroLeft k)

monusSucSuc : (a b : Nat) -> Eq (monus (suc a) (suc b)) (monus a b)
monusSucSuc a zero    = refl
monusSucSuc a (suc k) = eqCong predN (monusSucSuc a k)

------------------------------------------------------------------------
-- monus (suc a) b = 0  ->  a < b .

monusZeroLt : (a b : Nat) -> Eq (monus (suc a) b) zero -> Lt a b
monusZeroLt a zero    h = emptyElim (sucNotZero a h)
monusZeroLt zero    (suc k) h = ltZ k
monusZeroLt (suc a) (suc k) h =
  ltS a k (monusZeroLt a k (eqTrans (eqSym (monusSucSuc (suc a) k)) h))

------------------------------------------------------------------------
-- a < b  ->  monus (suc a) b = 0 .

ltMonusZero : (a b : Nat) -> Lt a b -> Eq (monus (suc a) b) zero
ltMonusZero zero    (suc k) (ltZ _)      =
  eqTrans (monusSucSuc zero k) (monusZeroLeft k)
ltMonusZero (suc a) (suc k) (ltS _ _ h) =
  eqTrans (monusSucSuc (suc a) k) (ltMonusZero a k h)

------------------------------------------------------------------------
-- trichotomy-ish:  NatLe b a  or  Lt a b .

leLt : (a b : Nat) -> Or (NatLe b a) (Lt a b)
leLt a zero          = inl (le-zero a)
leLt zero    (suc b) = inr (ltZ b)
leLt (suc a) (suc b) with leLt a b
... | inl h = inl (le-suc h)
... | inr h = inr (ltS a b h)

------------------------------------------------------------------------
-- monus (suc a) b /= 0  ->  b <= a .

monusPosLe : (a b : Nat) -> (Eq (monus (suc a) b) zero -> Empty) -> NatLe b a
monusPosLe a b hyp with leLt a b
... | inl h  = h
... | inr lt = emptyElim (hyp (ltMonusZero a b lt))
