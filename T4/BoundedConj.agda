{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.BoundedConj -- the OBJECT bounded conjunction (sum) carrier for the
-- INTERNAL course-of-values induction behind internal Church-Rosser.
--
--   bigC f  is a Fun2 with (the first argument is an inert dummy)
--     ap2 (bigC f) x O       = f O
--     ap2 (bigC f) x (s n)   = sigma (f (s n)) (ap2 (bigC f) x n)
--
-- so  ap2 (bigC f) x K = sigma_{i=0..K} (f i) , and  bigC f x K = O  is the
-- single object equation encoding "f i = O for every i <= K".  Built from the
-- object recursor R and the Fan / Lift1 / compose1U combinators:
--
--   bigC f = R (compose1U f o) (Fan (Lift1 (compose1U f s)) v sigma) v
--
-- This file delivers the two defining equations; the projection lemma
-- (bigC f x K = O => f p = O  for p <= K) and the CR step are downstream.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.BoundedConj where

open import T4.Base

open import BRA3.Church      using ( sigma )
open import BRA3.PairAlgebra using ( Lift1 ; axLift ; Fan ; axFan ; compose1U ; compose1U_eq )

------------------------------------------------------------------------
-- SECTION 1.  The carrier.

bigC : Fun1 -> Fun2
bigC f = R (compose1U f o) (Fan (Lift1 (compose1U f s)) v sigma) v

private
  stepH : Fun1 -> Fun2
  stepH f = Fan (Lift1 (compose1U f s)) v sigma

------------------------------------------------------------------------
-- SECTION 2.  Base equation:  bigC f x O = f O .

bigC_base : (f : Fun1) (x : Term) -> Deriv (eqF (ap2 (bigC f) x O) (ap1 f O))
bigC_base f x =
  ruleTrans (ax_R_base (compose1U f o) (stepH f) v x)
    (ruleTrans (compose1U_eq f o x) (cong1 f (ax_o x)))

------------------------------------------------------------------------
-- SECTION 3.  Step equation:  bigC f x (s n) = sigma (f (s n)) (bigC f x n) .

bigC_step : (f : Fun1) (x n : Term) ->
  Deriv (eqF (ap2 (bigC f) x (ap1 s n))
             (ap2 sigma (ap1 f (ap1 s n)) (ap2 (bigC f) x n)))
bigC_step f x n =
  let rec : Term
      rec = ap2 (bigC f) x n
      vxn : Term
      vxn = ap2 v x n
      rstep : Deriv (eqF (ap2 (bigC f) x (ap1 s n)) (ap2 (stepH f) vxn rec))
      rstep = ax_R_step (compose1U f o) (stepH f) v x n
      fanEq : Deriv (eqF (ap2 (stepH f) vxn rec)
                         (ap2 sigma (ap2 (Lift1 (compose1U f s)) vxn rec)
                                    (ap2 v vxn rec)))
      fanEq = axFan (Lift1 (compose1U f s)) v sigma vxn rec
      aEq : Deriv (eqF (ap2 (Lift1 (compose1U f s)) vxn rec) (ap1 f (ap1 s n)))
      aEq = ruleTrans (axLift (compose1U f s) vxn rec)
              (ruleTrans (compose1U_eq f s vxn) (cong1 f (cong1 s (ax_v x n))))
      bEq : Deriv (eqF (ap2 v vxn rec) rec)
      bEq = ax_v vxn rec
      sigEq : Deriv (eqF (ap2 sigma (ap2 (Lift1 (compose1U f s)) vxn rec) (ap2 v vxn rec))
                         (ap2 sigma (ap1 f (ap1 s n)) rec))
      sigEq = ruleTrans (congL sigma (ap2 v vxn rec) aEq)
                        (congR sigma (ap1 f (ap1 s n)) bEq)
  in ruleTrans rstep (ruleTrans fanEq sigEq)
