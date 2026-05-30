{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.StepU2CorrectAPI -- record bundles exposing meta-level Fun1/Fun2
-- fuels alongside the Reaches-style runs equations.
--
-- The Reaches-only API (with opaque  fuel : Term ) is insufficient for
-- the R-case construction: when building paired_R as a Fun2 R-recursion,
-- the parent's step function (an F2 : Fun2 expression) needs to compose
-- the meta Fun1/Fun2 fuels of g, h1, h2 INSIDE its body.  Hence the
-- bundle exposes  fuelF : Fun1  /  fuelG : Fun2  as a first-class field,
-- and the runs equation uses  ap1 fuelF x  /  ap2 fuelG x y  in place
-- of an opaque Term fuel.
--
-- The shape of  fuelF / fuelG  is INTENTIONALLY a Fun1/Fun2 (not a Term)
-- so that parent R-cases can use it directly in their Fun2 step bodies.

module BRA4.StepU2CorrectAPI where

open import BRA4.Base
open import BRA4.StepU2

open import BRA3.Church          using ( pi )
open import BRA3.CourseOfValues  using ( iter )

------------------------------------------------------------------------
-- Completeness bundle for a single Fun1.

record Correct1 (f : Fun1) : Set where
  constructor mkC1
  field
    fuelF : Fun1
    runs1 : (x K : Term) ->
            Deriv (eqF (ap2 (iter step) (cfgEV (mcode1 f) x K)
                                          (ap1 fuelF x))
                       (cfgRT (ap1 f x) K))

open Correct1 public

------------------------------------------------------------------------
-- Completeness bundle for a single Fun2.

record Correct2 (g : Fun2) : Set where
  constructor mkC2
  field
    fuelG : Fun2
    runs2 : (x y K : Term) ->
            Deriv (eqF (ap2 (iter step) (cfgEV (mcode2 g) (ap2 pi x y) K)
                                          (ap2 fuelG x y))
                       (cfgRT (ap2 g x y) K))

open Correct2 public
