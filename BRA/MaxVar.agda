{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.MaxVar -- bounded-fresh-variable infrastructure for Term.
--
-- Used to lift schematic Theorem 12 statements (Deriv P_outer, with
-- var 0 / var (suc zero) free) to the universal form (x v : Term) ->
-- Deriv (P at x v) without the spurious closure  subst (suc zero) v x = x.
--
-- The trick: choose k = pickFresh v fresh in v (and >= 2), do
-- ruleInst zero (var k) -> ruleInst (suc zero) v -> ruleInst k x .
-- Step 3 substitutes var k with x in the formula; v's contents are
-- recursed into, but since k is fresh in v, v stays put.
--
-- No postulates, no holes, --safe --without-K --exact-split.

module BRA.MaxVar where

open import BRA.Base
open import BRA.Term
open import BRA.SubstClosure using (Fun1_closed ; Fun2_closed)

------------------------------------------------------------------------
-- natMax: pointwise maximum.

natMax : Nat -> Nat -> Nat
natMax zero    m       = m
natMax (suc n) zero    = suc n
natMax (suc n) (suc m) = suc (natMax n m)

------------------------------------------------------------------------
-- Geq: greater-or-equal predicate on Nat.

data Geq : Nat -> Nat -> Set where
  geqZero : (n : Nat) -> Geq n zero
  geqSuc  : {n m : Nat} -> Geq n m -> Geq (suc n) (suc m)

geqRefl : (n : Nat) -> Geq n n
geqRefl zero    = geqZero zero
geqRefl (suc n) = geqSuc (geqRefl n)

geqTrans : {n m k : Nat} -> Geq n m -> Geq m k -> Geq n k
geqTrans p           (geqZero _) = geqZero _
geqTrans (geqSuc pq) (geqSuc qr) = geqSuc (geqTrans pq qr)

------------------------------------------------------------------------
-- natMax is upper bound on both arguments.

natMax_geqL : (n m : Nat) -> Geq (natMax n m) n
natMax_geqL zero    m       = geqZero m
natMax_geqL (suc n) zero    = geqRefl (suc n)
natMax_geqL (suc n) (suc m) = geqSuc (natMax_geqL n m)

natMax_geqR : (n m : Nat) -> Geq (natMax n m) m
natMax_geqR zero    m       = geqRefl m
natMax_geqR (suc n) zero    = geqZero (suc n)
natMax_geqR (suc n) (suc m) = geqSuc (natMax_geqR n m)

------------------------------------------------------------------------
-- natEq is symmetric, and natEq n k = false when k > n.

natEq_sym : (n m : Nat) -> Eq (natEq n m) (natEq m n)
natEq_sym zero    zero    = refl
natEq_sym zero    (suc _) = refl
natEq_sym (suc _) zero    = refl
natEq_sym (suc n) (suc m) = natEq_sym n m

natEq_refl : (n : Nat) -> Eq (natEq n n) true
natEq_refl zero    = refl
natEq_refl (suc n) = natEq_refl n

natEq_false_aboveSuc : (n k : Nat) -> Geq k (suc n) -> Eq (natEq n k) false
natEq_false_aboveSuc n        zero      ()
natEq_false_aboveSuc zero     (suc k')  (geqSuc _) = refl
natEq_false_aboveSuc (suc n)  (suc k')  (geqSuc ge) = natEq_false_aboveSuc n k' ge

natEq_false_aboveSuc' : (n k : Nat) -> Geq k (suc n) -> Eq (natEq k n) false
natEq_false_aboveSuc' n k ge =
  eqTrans (natEq_sym k n) (natEq_false_aboveSuc n k ge)

------------------------------------------------------------------------
-- maxVarT : Term -> Nat. One more than the maximum free variable index
-- in t (zero if t has no free variables).  Note: Fun1 / Fun2 have no
-- Term arguments, so do not contribute.

maxVarT : Term -> Nat
maxVarT O           = zero
maxVarT (var n)     = suc n
maxVarT (ap1 f t)   = maxVarT t
maxVarT (ap2 g a b) = natMax (maxVarT a) (maxVarT b)

------------------------------------------------------------------------
-- subst_aboveMax: when k >= maxVarT t, subst k r t = t.

subst_aboveMax : (k : Nat) (r t : Term) -> Geq k (maxVarT t) -> Eq (subst k r t) t
subst_aboveMax k r O           ge = refl
subst_aboveMax k r (var n)     ge =
  eqCong (\ b -> boolCase b r (var n)) (natEq_false_aboveSuc n k ge)
subst_aboveMax k r (ap1 f t)   ge =
  eqTrans (eqCong (\ F -> ap1 F (subst k r t)) (Fun1_closed k r f))
          (eqCong (\ T -> ap1 f T) (subst_aboveMax k r t ge))
subst_aboveMax k r (ap2 g a b) ge =
  let geA : Geq k (maxVarT a)
      geA = geqTrans ge (natMax_geqL (maxVarT a) (maxVarT b))
      geB : Geq k (maxVarT b)
      geB = geqTrans ge (natMax_geqR (maxVarT a) (maxVarT b))
  in eqTrans (eqCong (\ G -> ap2 G (subst k r a) (subst k r b)) (Fun2_closed k r g))
             (eqTrans (eqCong (\ A -> ap2 g A (subst k r b)) (subst_aboveMax k r a geA))
                      (eqCong (\ B -> ap2 g a B) (subst_aboveMax k r b geB)))

------------------------------------------------------------------------
-- pickFresh: a Nat >= 2 and fresh in t.

pickFresh : Term -> Nat
pickFresh t = natMax (suc (suc zero)) (maxVarT t)

pickFresh_geq2 : (t : Term) -> Geq (pickFresh t) (suc (suc zero))
pickFresh_geq2 t = natMax_geqL (suc (suc zero)) (maxVarT t)

pickFresh_geqMax : (t : Term) -> Geq (pickFresh t) (maxVarT t)
pickFresh_geqMax t = natMax_geqR (suc (suc zero)) (maxVarT t)

-- Geq (suc (suc zero)) (suc zero), used to derive "pickFresh t >= 1"
-- from "pickFresh t >= 2".

geq_two_one : Geq (suc (suc zero)) (suc zero)
geq_two_one = geqSuc (geqZero (suc zero))

geq_two_zero : Geq (suc (suc zero)) zero
geq_two_zero = geqZero (suc (suc zero))

pickFresh_geq1 : (t : Term) -> Geq (pickFresh t) (suc zero)
pickFresh_geq1 t = geqTrans (pickFresh_geq2 t) geq_two_one

subst_pickFresh : (r t : Term) -> Eq (subst (pickFresh t) r t) t
subst_pickFresh r t = subst_aboveMax (pickFresh t) r t (pickFresh_geqMax t)

------------------------------------------------------------------------
-- Useful corollaries: pickFresh t is not zero / not (suc zero).

pickFresh_natEq_zero : (t : Term) -> Eq (natEq zero (pickFresh t)) false
pickFresh_natEq_zero t =
  natEq_false_aboveSuc zero (pickFresh t) (pickFresh_geq1 t)

pickFresh_natEq_one  : (t : Term) -> Eq (natEq (suc zero) (pickFresh t)) false
pickFresh_natEq_one t =
  natEq_false_aboveSuc (suc zero) (pickFresh t) (pickFresh_geq2 t)

pickFresh_natEq_zero' : (t : Term) -> Eq (natEq (pickFresh t) zero) false
pickFresh_natEq_zero' t =
  eqTrans (natEq_sym (pickFresh t) zero) (pickFresh_natEq_zero t)

pickFresh_natEq_one' : (t : Term) -> Eq (natEq (pickFresh t) (suc zero)) false
pickFresh_natEq_one' t =
  eqTrans (natEq_sym (pickFresh t) (suc zero)) (pickFresh_natEq_one t)
