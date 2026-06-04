{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SurpriseG2.KdefDiagConj -- the diagonal program for the new
-- conjunction-shape route (parallel to  T4.KdefDiag ).   Re-pointed
-- from the OLD  hitKdef / outKdef  at  Kcode Lstar  to the NEW
-- hitKdefConj / outKdefConj  at  KcodeConj M enum  (per
-- T4/NEXT-SESSION-CGICONJ-BODY.md).
--
-- =====================================================================
-- WHAT THIS FILE SHIPS.
-- =====================================================================
--
--   predFlipDefConj M enum   = compose1U isZero (hitKdefConj M enum (outKdefConj M enum))
--   gCodeOfDefConj  M enum   = mcode2 (Lift1 (outKdefConj M enum))
--   gLcodeDefConj   M enum   = the encoded diagonal program code.
--
--   inAlph_gLcodeDefConj   = the InAlph membership of  gLcodeDefConj M enum .
--   dRT_gLDefConj          = the parse round-trip
--                            parse (enc (gLcodeDefConj M enum)) = gLcodeDefConj M enum .
--
-- Mechanical parallel of  T4.KdefDiag .   No  Lstar : Term  parameter ;
-- in its place the meta  M : Nat  +  enum : Fun1  thread through the
-- recogniser .

module T4.SurpriseG2.KdefDiagConj where

open import T4.Base
open import T4.Tags        using ( tag_C )
open import T4.SurpriseG2.KdefRecogConj
  using ( hitKdefConj ; outKdefConj )
open import T4.EvalU       using ( mcode1 ; mcode2 ; mcodeMu )
open import T4.McodeInAlph using
  ( inAlph_natCode ; inAlph_mcode1 ; inAlph_mcode2 ; inAlph_mcodeMu )
open import T4.ProgEnc     using ( enc )
open import T4.ProgParse   using ( parse ; parse_enc ; InAlph ; iaPi )

open import BRA3.Church      using ( pi ; isZero )
open import BRA3.Fan         using ( Lift1 ; compose1U )

------------------------------------------------------------------------
-- Concrete diagonal pieces, functions of  M : Nat  +  enum : Fun1 .

-- the mu-predicate :  predFlipDefConj M enum n = isZero (hitKdefConj M enum (outKdefConj M enum) n)
--   ( = O iff hitKdefConj ... n = s O ,  i.e. the recogniser fires at n ).
predFlipDefConj : Nat -> Fun1 -> Fun1
predFlipDefConj M enum =
  compose1U isZero (hitKdefConj M enum (outKdefConj M enum))

-- the output transform .
gCodeOfDefConj : Nat -> Fun1 -> Term
gCodeOfDefConj M enum = mcode2 (Lift1 (outKdefConj M enum))

-- the diagonal program code  ⌜g_L⌝  = C (Lift1 outKdefConj) (mu predFlipDefConj) u .
gLcodeDefConj : Nat -> Fun1 -> Term
gLcodeDefConj M enum =
  ap2 pi (natCode tag_C)
    (ap2 pi (gCodeOfDefConj M enum)
       (ap2 pi (mcodeMu (mcode1 (predFlipDefConj M enum))) (mcode1 u)))

------------------------------------------------------------------------
-- The round-trip  parse (enc gLcodeDefConj) = gLcodeDefConj  via the
-- InAlph membership of the C-wrapper over  mcode2 ... ,  mcodeMu (mcode1 ...) ,
-- mcode1 u .

inAlph_gLcodeDefConj : (M : Nat) (enum : Fun1) -> InAlph (gLcodeDefConj M enum)
inAlph_gLcodeDefConj M enum =
  iaPi (natCode tag_C)
       (ap2 pi (gCodeOfDefConj M enum)
          (ap2 pi (mcodeMu (mcode1 (predFlipDefConj M enum))) (mcode1 u)))
    (inAlph_natCode tag_C)
    (iaPi (gCodeOfDefConj M enum)
          (ap2 pi (mcodeMu (mcode1 (predFlipDefConj M enum))) (mcode1 u))
      (inAlph_mcode2 (Lift1 (outKdefConj M enum)))
      (iaPi (mcodeMu (mcode1 (predFlipDefConj M enum))) (mcode1 u)
        (inAlph_mcodeMu (mcode1 (predFlipDefConj M enum))
                         (inAlph_mcode1 (predFlipDefConj M enum)))
        (inAlph_mcode1 u)))

-- the parse round-trip :  parse (enc (gLcodeDefConj M enum)) = gLcodeDefConj M enum .
dRT_gLDefConj :
  (M : Nat) (enum : Fun1) ->
  Deriv (eqF (ap1 parse (enc (gLcodeDefConj M enum))) (gLcodeDefConj M enum))
dRT_gLDefConj M enum =
  parse_enc (gLcodeDefConj M enum) (inAlph_gLcodeDefConj M enum)
