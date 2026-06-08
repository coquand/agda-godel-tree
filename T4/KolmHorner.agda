{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.KolmHorner -- a base-3 Horner program for the Kolmogorov-complexity
-- upper bound  K(x) <= c . log_3 x + c' .
--
-- For a digit list  ds  (least-significant digit first, each digit < 3 in
-- the intended use, though correctness here needs no such bound) we build a
-- closed  Fun1
--
--   horner ds : Fun1
--
-- whose value at  O  is the Horner number  hVal ds = sum_i d_i . 3^i :
--
--   horner_correct ds : ap1 (horner ds) O = natCode (hVal ds) .
--
-- Each digit contributes a FIXED-size code chunk
--   compose1U (addD d) (compose1U triple_F1 _) ,
-- so the program's code is linear in the number of digits = O(log_3 x);
-- that size accounting + the universal-machine run live in the next files.

module T4.KolmHorner where

open import T4.Base
open import BRA3.Fan      using ( compose1U_eq )
open import BRA3.Code.Tag using ( addN )
open import T4.Exp3       using ( triple_F1 ; triple_F1_natCode )

------------------------------------------------------------------------
-- Digit lists (least-significant digit first).

data DL : Set where
  dnil  : DL
  dcons : Nat -> DL -> DL

-- 3 * v , written so that  addN  reduces (recursion on first arg).
threeT : Nat -> Nat
threeT wv = addN wv (addN wv wv)

-- Horner value, LSD first:  hVal (d :: ds) = d + 3 * (hVal ds) .
hVal : DL -> Nat
hVal dnil         = zero
hVal (dcons d ds) = addN d (threeT (hVal ds))

------------------------------------------------------------------------
-- addD d : the constant-add functor  m |-> d + m  (d successors).

addD : Nat -> Fun1
addD zero    = u
addD (suc d) = compose1U s (addD d)

addD_natCode :
  (d m : Nat) -> Deriv (eqF (ap1 (addD d) (natCode m)) (natCode (addN d m)))
addD_natCode zero    m = ax_u (natCode m)
addD_natCode (suc d) m =
  ruleTrans (compose1U_eq s (addD d) (natCode m))
            (cong1 s (addD_natCode d m))

------------------------------------------------------------------------
-- The Horner program and its correctness.

horner : DL -> Fun1
horner dnil         = constN zero
horner (dcons d ds) = compose1U (addD d) (compose1U triple_F1 (horner ds))

horner_correct :
  (ds : DL) -> Deriv (eqF (ap1 (horner ds) O) (natCode (hVal ds)))
horner_correct dnil         = constN_eq zero O
horner_correct (dcons d ds) =
  let wv : Nat
      wv = hVal ds

      ih : Deriv (eqF (ap1 (horner ds) O) (natCode wv))
      ih = horner_correct ds

      -- peel the outer  addD d .
      e1 : Deriv (eqF (ap1 (horner (dcons d ds)) O)
                      (ap1 (addD d) (ap1 (compose1U triple_F1 (horner ds)) O)))
      e1 = compose1U_eq (addD d) (compose1U triple_F1 (horner ds)) O

      -- peel the  triple_F1  (times 3).
      e2 : Deriv (eqF (ap1 (compose1U triple_F1 (horner ds)) O)
                      (ap1 triple_F1 (ap1 (horner ds) O)))
      e2 = compose1U_eq triple_F1 (horner ds) O

      e3 : Deriv (eqF (ap1 (addD d) (ap1 (compose1U triple_F1 (horner ds)) O))
                      (ap1 (addD d) (ap1 triple_F1 (ap1 (horner ds) O))))
      e3 = cong1 (addD d) e2

      -- run the inner Horner (IH).
      e4 : Deriv (eqF (ap1 (addD d) (ap1 triple_F1 (ap1 (horner ds) O)))
                      (ap1 (addD d) (ap1 triple_F1 (natCode wv))))
      e4 = cong1 (addD d) (cong1 triple_F1 ih)

      -- times 3 :  triple_F1 (natCode wv) = natCode (v + (v + v)) = natCode (threeT wv).
      e5 : Deriv (eqF (ap1 (addD d) (ap1 triple_F1 (natCode wv)))
                      (ap1 (addD d) (natCode (threeT wv))))
      e5 = cong1 (addD d) (triple_F1_natCode wv)

      -- add the digit d.
      e6 : Deriv (eqF (ap1 (addD d) (natCode (threeT wv)))
                      (natCode (addN d (threeT wv))))
      e6 = addD_natCode d (threeT wv)
  in ruleTrans e1 (ruleTrans e3 (ruleTrans e4 (ruleTrans e5 e6)))
