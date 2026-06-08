{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.KolmDigits -- base-3 digit extraction for the Kolmogorov bound.
--
--   digits3 x : DL          ( least-significant digit first, digits < 3 )
--   digits3_correct x : hVal (digits3 x) = x
--
-- so  horner (digits3 x)  is a closed program whose value at O is exactly x.
-- The number of digits is logarithmic in x (handled in the size file).

module T4.KolmDigits where

open import T4.Base
open import BRA3.Code.Tag       using ( addN )
open import BRA3.Code.NatLemmas using ( addN_suc_right )
open import BRA3.RuleInst2       using ( NatLe ; le-zero ; le-suc ; le-refl
                                       ; le-suc-right ; le-trans )
open import T4.KolmHorner        using ( DL ; dnil ; dcons ; threeT ; hVal )

------------------------------------------------------------------------
-- div / mod by 3 (structural 3-peel recursion).

mod3 : Nat -> Nat
mod3 zero                = zero
mod3 (suc zero)          = suc zero
mod3 (suc (suc zero))    = suc (suc zero)
mod3 (suc (suc (suc n))) = mod3 n

div3 : Nat -> Nat
div3 zero                = zero
div3 (suc zero)          = zero
div3 (suc (suc zero))    = zero
div3 (suc (suc (suc n))) = suc (div3 n)

------------------------------------------------------------------------
-- threeT (suc q) = suc (suc (suc (threeT q))) .

threeT_suc : (q : Nat) -> Eq (threeT (suc q)) (suc (suc (suc (threeT q))))
threeT_suc q =
  -- threeT (suc q) = addN (suc q) (addN (suc q) (suc q))
  --                = suc (addN q (addN (suc q) (suc q)))          [def]
  -- addN (suc q) (suc q) = suc (addN q (suc q)) = suc (suc (addN q q))
  let A : Nat
      A = addN q q
      -- addN (suc q) (suc q) = suc (suc A)
      ss : Eq (addN (suc q) (suc q)) (suc (suc A))
      ss = eqCong suc (addN_suc_right q q)
      -- addN q (addN (suc q) (suc q)) = addN q (suc (suc A))
      h1 : Eq (addN q (addN (suc q) (suc q))) (addN q (suc (suc A)))
      h1 = eqCong (\ z -> addN q z) ss
      -- addN q (suc (suc A)) = suc (suc (addN q A))
      h2 : Eq (addN q (suc (suc A))) (suc (suc (addN q A)))
      h2 = eqTrans (addN_suc_right q (suc A)) (eqCong suc (addN_suc_right q A))
      -- combine, then one outer suc (the def-peel of addN (suc q) _).
      inner : Eq (addN q (addN (suc q) (suc q))) (suc (suc (addN q A)))
      inner = eqTrans h1 h2
  in eqCong suc inner

------------------------------------------------------------------------
-- Euclid:  mod3 x + 3 * (div3 x) = x .

euclid3 : (x : Nat) -> Eq (addN (mod3 x) (threeT (div3 x))) x
euclid3 zero                = refl
euclid3 (suc zero)          = refl
euclid3 (suc (suc zero))    = refl
euclid3 (suc (suc (suc n))) =
  -- mod3 = mod3 n , div3 = suc (div3 n) .
  -- addN (mod3 n) (threeT (suc (div3 n)))
  --   = addN (mod3 n) (suc (suc (suc (threeT (div3 n)))))        [threeT_suc]
  --   = suc (suc (suc (addN (mod3 n) (threeT (div3 n)))))         [addN_suc_right x3]
  --   = suc (suc (suc n))                                          [IH]
  let q : Nat
      q = div3 n
      m : Nat
      m = mod3 n
      -- push threeT_suc through addN (mod3 n) _ .
      e0 : Eq (addN m (threeT (suc q))) (addN m (suc (suc (suc (threeT q)))))
      e0 = eqCong (\ z -> addN m z) (threeT_suc q)
      -- addN m (suc (suc (suc K))) = suc (suc (suc (addN m K))) .
      e1 : Eq (addN m (suc (suc (suc (threeT q)))))
              (suc (suc (suc (addN m (threeT q)))))
      e1 = eqTrans (addN_suc_right m (suc (suc (threeT q))))
            (eqCong suc (eqTrans (addN_suc_right m (suc (threeT q)))
              (eqCong suc (addN_suc_right m (threeT q)))))
      -- IH : addN m (threeT q) = n
      ih : Eq (addN m (threeT q)) n
      ih = euclid3 n
  in eqTrans e0 (eqTrans e1 (eqCong (\ z -> suc (suc (suc z))) ih))

------------------------------------------------------------------------
-- div3 bounds (for the fuel termination).

div3_le : (x : Nat) -> NatLe (div3 x) x
div3_le zero                = le-zero zero
div3_le (suc zero)          = le-zero (suc zero)
div3_le (suc (suc zero))    = le-zero (suc (suc zero))
div3_le (suc (suc (suc n))) =
  le-suc (le-suc-right (le-suc-right (div3_le n)))

div3_suc_le : (x : Nat) -> NatLe (div3 (suc x)) x
div3_suc_le zero          = le-zero zero
div3_suc_le (suc zero)     = le-zero (suc zero)
div3_suc_le (suc (suc n)) = le-suc (le-suc-right (div3_le n))

------------------------------------------------------------------------
-- Fuelled digit extraction.

digitsFuel : Nat -> Nat -> DL
digitsFuel zero    x       = dnil
digitsFuel (suc f) zero    = dnil
digitsFuel (suc f) (suc x) = dcons (mod3 (suc x)) (digitsFuel f (div3 (suc x)))

-- correctness:  if the fuel is at least x, the digits recover x.
digitsFuel_correct :
  (f x : Nat) -> NatLe x f -> Eq (hVal (digitsFuel f x)) x
digitsFuel_correct zero    zero    _  = refl
digitsFuel_correct (suc f) zero    _  = refl
digitsFuel_correct (suc f) (suc x) le =
  -- NatLe (suc x) (suc f)  ->  NatLe x f ;  and  div3 (suc x) <= x <= f .
  let lexf : NatLe x f
      lexf = le-pred le
      lediv : NatLe (div3 (suc x)) f
      lediv = le-trans (div3_suc_le x) lexf
      ih : Eq (hVal (digitsFuel f (div3 (suc x)))) (div3 (suc x))
      ih = digitsFuel_correct f (div3 (suc x)) lediv
      -- hVal (dcons (mod3 (suc x)) rest) = addN (mod3 (suc x)) (threeT (hVal rest))
      step : Eq (addN (mod3 (suc x)) (threeT (hVal (digitsFuel f (div3 (suc x))))))
                (addN (mod3 (suc x)) (threeT (div3 (suc x))))
      step = eqCong (\ z -> addN (mod3 (suc x)) (threeT z)) ih
  in eqTrans step (euclid3 (suc x))
  where
    le-pred : {m n : Nat} -> NatLe (suc m) (suc n) -> NatLe m n
    le-pred (le-suc h) = h

------------------------------------------------------------------------
-- The digit list of x and its correctness ( fuel = x ).

digits3 : Nat -> DL
digits3 x = digitsFuel x x

digits3_correct : (x : Nat) -> Eq (hVal (digits3 x)) x
digits3_correct x = digitsFuel_correct x x (le-refl x)
