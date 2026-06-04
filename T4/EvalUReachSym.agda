{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.EvalUReachSym -- the per-position interpreter-correctness lemmas in
-- SYMBOLIC form: the universal CK machine, run on the code of ANY Fun1 / Fun2
-- at numeral arguments, reaches the SYMBOLIC application  ap1 f a / ap2 g x y
-- (NOT the computed numeral).
--
--   ev1_reaches f n K : Reaches (cfgEV (mcode1 f) (natCode n) K)
--                               (cfgRT (ap1 f (natCode n)) K)
--   ev2_reaches g x y K : Reaches (cfgEV (mcode2 g) (ap2 pi (natCode x) (natCode y)) K)
--                                 (cfgRT (ap2 g (natCode x) (natCode y)) K)
--
-- These are the existing  runs1 / runs2  (which reach the reference-semantics
-- numeral  natCode (evalN f ...) ) post-composed with the soundness bridge
--  evalN_sound : natCode (evalN f ..) = ap_ f ..  .  Kept GENERIC in f / g and
-- SEALED  abstract , exactly as the size lemmas are: proven once with f / g as
-- VARIABLES (so  runs1 / evalN1_sound  stay NEUTRAL -- the recursion on the
-- function structure never fires), then instantiated at a concrete predicate
-- (e.g.  predFlip L , which embeds  thmT ) as a NEUTRAL application.  So the
-- proof never traverses  thmT : there is no computation, only instantiation.
-- This discharges the  predReaches / outLReaches  black boxes of T4.KGodel1.

module T4.EvalUReachSym where

open import T4.Base
open import T4.EvalU        using ( mcode1 ; mcode2 ; cfgEV ; cfgRT )
open import T4.EvalUCorrect using
  ( Reaches ; reach_eq_target ; cfgRT_val
  ; runs1 ; runs2 ; evalN1 ; evalN2 ; evalN1_sound ; evalN2_sound )

open import BRA3.Church using ( pi )

abstract
  ev1_reaches :
    (f : Fun1) (n : Nat) (K : Term) ->
    Reaches (cfgEV (mcode1 f) (natCode n) K) (cfgRT (ap1 f (natCode n)) K)
  ev1_reaches f n K =
    reach_eq_target (runs1 f n K)
      (cfgRT_val (natCode (evalN1 f n)) (ap1 f (natCode n)) K
                 (evalN1_sound f n))

  ev2_reaches :
    (g : Fun2) (x y : Nat) (K : Term) ->
    Reaches (cfgEV (mcode2 g) (ap2 pi (natCode x) (natCode y)) K)
            (cfgRT (ap2 g (natCode x) (natCode y)) K)
  ev2_reaches g x y K =
    reach_eq_target (runs2 g x y K)
      (cfgRT_val (natCode (evalN2 g x y)) (ap2 g (natCode x) (natCode y)) K
                 (evalN2_sound g x y))
