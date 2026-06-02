{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.NumContract -- the Deriv-level contract that  num : Fun1
-- realises  n |-> codeTerm (natCode n)  on every numeral input.
--
-- Our T4.Num.num  satisfies this contract unconditionally via the
-- meta-induction in T4.IsNat: every natCode-shaped Term is in
-- isNat, so num_eq_code applies.

module T4.NumContract where

open import T4.Base
open import T4.Tags
open import T4.Code
open import T4.Num
open import T4.IsNat

------------------------------------------------------------------------
-- Contract record.

record NumContract (num1 : Fun1) : Set where
  field
    numEq :
      (n : Nat) ->
      Deriv (eqF (ap1 num1 (natCode n))
                  (codeTerm (natCode n)))

------------------------------------------------------------------------
-- Every natCode-shaped Term is isNat.

isNat_natCode : (n : Nat) -> isNat (natCode n)
isNat_natCode zero    = isNat_O
isNat_natCode (suc n) = isNat_S (natCode n) (isNat_natCode n)

------------------------------------------------------------------------
-- Our T4.Num.num satisfies NumContract.

numContract : NumContract num
numContract = record { numEq = lemma }
  where
    lemma :
      (n : Nat) ->
      Deriv (eqF (ap1 num (natCode n)) (codeTerm (natCode n)))
    lemma n = num_eq_code (natCode n) (isNat_natCode n)
