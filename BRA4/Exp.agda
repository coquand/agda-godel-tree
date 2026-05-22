{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Exp -- the object  exp2 : Fun1  computing  2^n , for the Berry
-- counting bound (Phase A of KRIVINE-BERRY-PLAN.md):  the number of
-- formula-codes of length  < n  is bounded by  2^{c n} .
--
-- exp2 is PLAIN primitive recursion on  n  (not a tree fold), so it is
-- built directly from  BRA3.CourseOfValues.iter  (k-fold iteration) with
-- the object doubling functor  double_F1 = C sigma u u  (sigma is BRA's
-- addition, so  sigma x x = 2x ):
--
--   exp2 = C (iter double_F1) (constN 1) u
--   ap1 exp2 n = ap2 (iter double_F1) (natCode 1) n = double_F1 ^ n (1)
--
-- Closures:
--   exp2_at_O     :  ap1 exp2 O          = natCode 1
--   exp2_at_succ  :  ap1 exp2 (s n)      = sigma (exp2 n) (exp2 n)     (Closed n)
--   exp2_natCode  :  ap1 exp2 (natCode k) = natCode (powN k)           (powN = meta 2^k)

module BRA4.Exp where

open import BRA4.Base

open import BRA3.Church         using ( sigma )
open import BRA3.CourseOfValues using ( iter ; iter_base ; iter_step )
open import BRA3.Numerals       using ( sigma_natCode )
open import BRA3.Code.Tag       using ( addN )

------------------------------------------------------------------------
-- Meta  2^k , in  addN  form so  sigma_natCode  lands on it definitionally.

powN : Nat -> Nat
powN zero    = suc zero
powN (suc k) = addN (powN k) (powN k)

------------------------------------------------------------------------
-- Object doubling:  double_F1 x = sigma x x .

double_F1 : Fun1
double_F1 = C sigma u u

double_F1_eq :
  (x : Term) -> Deriv (eqF (ap1 double_F1 x) (ap2 sigma x x))
double_F1_eq x =
  let s1 : Deriv (eqF (ap1 double_F1 x) (ap2 sigma (ap1 u x) (ap1 u x)))
      s1 = ax_C sigma u u x

      ux : Deriv (eqF (ap1 u x) x)
      ux = ax_u x
  in ruleTrans s1
       (ruleTrans (congL sigma (ap1 u x) ux) (congR sigma x ux))

double_F1_natCode :
  (m : Nat) -> Deriv (eqF (ap1 double_F1 (natCode m)) (natCode (addN m m)))
double_F1_natCode m =
  ruleTrans (double_F1_eq (natCode m)) (sigma_natCode m m)

------------------------------------------------------------------------
-- exp2 : Fun1 .

exp2 : Fun1
exp2 = C (iter double_F1) (constN (suc zero)) u

exp2_unfold :
  (n : Term) ->
  Deriv (eqF (ap1 exp2 n) (ap2 (iter double_F1) (natCode (suc zero)) n))
exp2_unfold n =
  let s1 :
        Deriv (eqF (ap1 exp2 n)
                    (ap2 (iter double_F1) (ap1 (constN (suc zero)) n) (ap1 u n)))
      s1 = ax_C (iter double_F1) (constN (suc zero)) u n

      cn : Deriv (eqF (ap1 (constN (suc zero)) n) (natCode (suc zero)))
      cn = constN_eq (suc zero) n

      un : Deriv (eqF (ap1 u n) n)
      un = ax_u n
  in ruleTrans s1
       (ruleTrans (congL (iter double_F1) (ap1 u n) cn)
                  (congR (iter double_F1) (natCode (suc zero)) un))

------------------------------------------------------------------------
-- exp2_at_O :  ap1 exp2 O = natCode 1 .

exp2_at_O : Deriv (eqF (ap1 exp2 O) (natCode (suc zero)))
exp2_at_O =
  ruleTrans (exp2_unfold O) (iter_base double_F1 (natCode (suc zero)))

------------------------------------------------------------------------
-- exp2_at_succ :  ap1 exp2 (s n) = sigma (exp2 n) (exp2 n)   (Closed n).

exp2_at_succ :
  (n : Term) -> Closed n ->
  Deriv (eqF (ap1 exp2 (ap1 s n)) (ap2 sigma (ap1 exp2 n) (ap1 exp2 n)))
exp2_at_succ n cn =
  let u1 :
        Deriv (eqF (ap1 exp2 (ap1 s n))
                    (ap2 (iter double_F1) (natCode (suc zero)) (ap1 s n)))
      u1 = exp2_unfold (ap1 s n)

      st :
        Deriv (eqF (ap2 (iter double_F1) (natCode (suc zero)) (ap1 s n))
                    (ap1 double_F1 (ap2 (iter double_F1) (natCode (suc zero)) n)))
      st = iter_step double_F1 (natCode (suc zero)) n cn

      iter_eq :
        Deriv (eqF (ap2 (iter double_F1) (natCode (suc zero)) n) (ap1 exp2 n))
      iter_eq = ruleSym (exp2_unfold n)

      d1 :
        Deriv (eqF (ap1 double_F1 (ap2 (iter double_F1) (natCode (suc zero)) n))
                    (ap1 double_F1 (ap1 exp2 n)))
      d1 = cong1 double_F1 iter_eq

      d2 :
        Deriv (eqF (ap1 double_F1 (ap1 exp2 n)) (ap2 sigma (ap1 exp2 n) (ap1 exp2 n)))
      d2 = double_F1_eq (ap1 exp2 n)
  in ruleTrans u1 (ruleTrans st (ruleTrans d1 d2))

------------------------------------------------------------------------
-- exp2_natCode :  ap1 exp2 (natCode k) = natCode (powN k) .
--
-- Meta-induction on k.  Base = exp2_at_O.  Step uses iter_step at the
-- closed numeral  natCode j , the IH, and  double_F1_natCode , with
--  powN (suc j) = addN (powN j) (powN j)  definitionally.

exp2_natCode :
  (k : Nat) -> Deriv (eqF (ap1 exp2 (natCode k)) (natCode (powN k)))
exp2_natCode zero = exp2_at_O
exp2_natCode (suc j) =
  let u1 :
        Deriv (eqF (ap1 exp2 (natCode (suc j)))
                    (ap2 (iter double_F1) (natCode (suc zero)) (natCode (suc j))))
      u1 = exp2_unfold (natCode (suc j))

      st :
        Deriv (eqF (ap2 (iter double_F1) (natCode (suc zero)) (natCode (suc j)))
                    (ap1 double_F1 (ap2 (iter double_F1) (natCode (suc zero)) (natCode j))))
      st = iter_step double_F1 (natCode (suc zero)) (natCode j) (closed_natCode j)

      ih : Deriv (eqF (ap1 exp2 (natCode j)) (natCode (powN j)))
      ih = exp2_natCode j

      iter_eq_pow :
        Deriv (eqF (ap2 (iter double_F1) (natCode (suc zero)) (natCode j))
                    (natCode (powN j)))
      iter_eq_pow = ruleTrans (ruleSym (exp2_unfold (natCode j))) ih

      dbl :
        Deriv (eqF (ap1 double_F1 (ap2 (iter double_F1) (natCode (suc zero)) (natCode j)))
                    (natCode (addN (powN j) (powN j))))
      dbl = ruleTrans (cong1 double_F1 iter_eq_pow) (double_F1_natCode (powN j))
  in ruleTrans u1 (ruleTrans st dbl)
