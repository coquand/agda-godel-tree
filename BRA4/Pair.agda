{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Pair -- Cantor pairing at the Term level, using the BRA3
-- Pair (= pi) algebra.
--
-- DESIGN.  Per learnt.md: "Use notation Pair, Fst, Snd for Cantor
-- coding."  In BRA3 we already have
--
--   Pair      = pi             ( = ap2 Pair a b )
--   Fst, Snd  : Fun1            ( = projections )
--   axFst : Deriv (Fst (Pair a b) = a)
--   axSnd : Deriv (Snd (Pair a b) = b)
--
-- which are re-exported by BRA4.Base.  BRA4 uses these AS-IS for the
-- user-facing pairing.
--
-- BOUNDARY.  BRA's pi at the Cantor encoding has  J(0,0) = 0 , so at
-- the meta-Nat level "pi 0 0" collapses to "0".  At the Term level,
-- however,  ap2 pi O O  is a syntactically distinct Term from  O .  Our
-- coding scheme avoids the Nat-level collision by reserving the bare
-- Term  O  for the special leaf case  code O = O  ; every other code
-- is  Pair (natCode tag) body  with  tag >= 1 , so  Fst code = natCode
-- tag != O .

module BRA4.Pair where

open import BRA4.Base public

-- Pair, Fst, Snd, axFst, axSnd are re-exported from BRA4.Base
-- (which gets them from BRA3.PairAlgebra).
--
-- Below we record the intended shape conventions for codes:

------------------------------------------------------------------------
-- Notation: a "tagged" code is  Pair (natCode tag) body  for some
-- natCode-form tag and arbitrary body.  Fst of such a code is
-- natCode tag (a definite leaf); Snd is body.

-- isPair (informal):  x  is a tagged code iff  Fst x = natCode tag  for
-- some tag >= 1 .  The leaf case  x = O  is distinguished from any
-- tagged code at the Agda meta level (different Term constructors).
