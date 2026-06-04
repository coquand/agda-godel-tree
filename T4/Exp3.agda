{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.Exp3 -- the object  exp3 : Fun1  computing  3^n , the base-3 analog of
-- T4.Exp.exp2 ( for the number-code Chaitin guard threshold  N = 3^(L*+1) ).
-- Mirrors T4.Exp verbatim with the doubling functor replaced by tripling
--   triple_F1 x = sigma x (sigma x x) = 3x  ( = C sigma u double_F1 ).
-- exp3_natCode lands on  TreeDigitsSize.pow3  ( same  3^k  recurrence ), so the
-- combinatorial size bound and the object threshold share one  pow3 .

module T4.Exp3 where

open import T4.Base
open import T4.Exp using ( double_F1 ; double_F1_eq )
open import T4.TreeDigitsSize using ( pow3 )

open import BRA3.Church         using ( sigma )
open import BRA3.CourseOfValues using ( iter ; iter_base ; iter_step )
open import BRA3.Numerals       using ( sigma_natCode )
open import BRA3.Code.Tag       using ( addN )

------------------------------------------------------------------------
-- Tripling functor:  triple_F1 x = sigma x (sigma x x) = 3x .

triple_F1 : Fun1
triple_F1 = C sigma u double_F1

triple_F1_eq :
  (x : Term) -> Deriv (eqF (ap1 triple_F1 x) (ap2 sigma x (ap2 sigma x x)))
triple_F1_eq x =
  let s1 : Deriv (eqF (ap1 triple_F1 x) (ap2 sigma (ap1 u x) (ap1 double_F1 x)))
      s1 = ax_C sigma u double_F1 x
      ux : Deriv (eqF (ap1 u x) x)
      ux = ax_u x
  in ruleTrans s1
       (ruleTrans (congL sigma (ap1 double_F1 x) ux)
                  (congR sigma x (double_F1_eq x)))

triple_F1_natCode :
  (m : Nat) ->
  Deriv (eqF (ap1 triple_F1 (natCode m)) (natCode (addN m (addN m m))))
triple_F1_natCode m =
  ruleTrans (triple_F1_eq (natCode m))
    (ruleTrans (congR sigma (natCode m) (sigma_natCode m m))
               (sigma_natCode m (addN m m)))

------------------------------------------------------------------------
-- exp3 : Fun1 .

exp3 : Fun1
exp3 = C (iter triple_F1) (constN (suc zero)) u

exp3_unfold :
  (n : Term) ->
  Deriv (eqF (ap1 exp3 n) (ap2 (iter triple_F1) (natCode (suc zero)) n))
exp3_unfold n =
  let s1 :
        Deriv (eqF (ap1 exp3 n)
                    (ap2 (iter triple_F1) (ap1 (constN (suc zero)) n) (ap1 u n)))
      s1 = ax_C (iter triple_F1) (constN (suc zero)) u n
      cn : Deriv (eqF (ap1 (constN (suc zero)) n) (natCode (suc zero)))
      cn = constN_eq (suc zero) n
      un : Deriv (eqF (ap1 u n) n)
      un = ax_u n
  in ruleTrans s1
       (ruleTrans (congL (iter triple_F1) (ap1 u n) cn)
                  (congR (iter triple_F1) (natCode (suc zero)) un))

exp3_at_O : Deriv (eqF (ap1 exp3 O) (natCode (suc zero)))
exp3_at_O =
  ruleTrans (exp3_unfold O) (iter_base triple_F1 (natCode (suc zero)))

------------------------------------------------------------------------
-- exp3_natCode :  ap1 exp3 (natCode k) = natCode (pow3 k) .
--   pow3 (suc j) = addN (pow3 j) (addN (pow3 j) (pow3 j))  definitionally,
--   matching  triple_F1_natCode (pow3 j) .

exp3_natCode :
  (k : Nat) -> Deriv (eqF (ap1 exp3 (natCode k)) (natCode (pow3 k)))
exp3_natCode zero = exp3_at_O
exp3_natCode (suc j) =
  let u1 :
        Deriv (eqF (ap1 exp3 (natCode (suc j)))
                    (ap2 (iter triple_F1) (natCode (suc zero)) (natCode (suc j))))
      u1 = exp3_unfold (natCode (suc j))
      st :
        Deriv (eqF (ap2 (iter triple_F1) (natCode (suc zero)) (natCode (suc j)))
                    (ap1 triple_F1 (ap2 (iter triple_F1) (natCode (suc zero)) (natCode j))))
      st = iter_step triple_F1 (natCode (suc zero)) (natCode j) (closed_natCode j)
      ih : Deriv (eqF (ap1 exp3 (natCode j)) (natCode (pow3 j)))
      ih = exp3_natCode j
      iter_eq_pow :
        Deriv (eqF (ap2 (iter triple_F1) (natCode (suc zero)) (natCode j))
                    (natCode (pow3 j)))
      iter_eq_pow = ruleTrans (ruleSym (exp3_unfold (natCode j))) ih
      trp :
        Deriv (eqF (ap1 triple_F1 (ap2 (iter triple_F1) (natCode (suc zero)) (natCode j)))
                    (natCode (addN (pow3 j) (addN (pow3 j) (pow3 j)))))
      trp = ruleTrans (cong1 triple_F1 iter_eq_pow) (triple_F1_natCode (pow3 j))
  in ruleTrans u1 (ruleTrans st trp)
