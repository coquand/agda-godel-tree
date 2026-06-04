{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.KdefDiagAlph -- the diagonal program for the  checkAlphN -guard route.
-- Analog of  T4.KdefDiag , re-pointed from  hitKdef / outKdef  to
-- hitKdefAlph / outKdefAlph  (T4.KdefRecogAlph).  Bodies are generic.

open import T4.Base

module T4.KdefDiagAlph (Lstar_meta : Nat) where

open import T4.Tags        using ( tag_C )
open import T4.KdefRecogAlph Lstar_meta using ( hitKdefAlph ; outKdefAlph )
open import T4.EvalU       using ( mcode1 ; mcode2 ; mcodeMu )
open import T4.McodeInAlph using
  ( inAlph_natCode ; inAlph_mcode1 ; inAlph_mcode2 ; inAlph_mcodeMu )
open import T4.ProgEnc     using ( enc )
open import T4.ProgParse   using ( parse ; parse_enc ; InAlph ; iaPi )

open import BRA3.Church      using ( pi ; isZero )
open import BRA3.Fan         using ( Lift1 ; compose1U )

------------------------------------------------------------------------
-- Concrete diagonal pieces.

predFlipDefAlph : Fun1
predFlipDefAlph = compose1U isZero (hitKdefAlph outKdefAlph)

gCodeOfDefAlph : Term
gCodeOfDefAlph = mcode2 (Lift1 outKdefAlph)

gLcodeDefAlph : Term
gLcodeDefAlph =
  ap2 pi (natCode tag_C)
    (ap2 pi gCodeOfDefAlph
       (ap2 pi (mcodeMu (mcode1 predFlipDefAlph)) (mcode1 u)))

------------------------------------------------------------------------
-- The parse round-trip.

inAlph_gLcodeDefAlph : InAlph gLcodeDefAlph
inAlph_gLcodeDefAlph =
  iaPi (natCode tag_C)
       (ap2 pi gCodeOfDefAlph
          (ap2 pi (mcodeMu (mcode1 predFlipDefAlph)) (mcode1 u)))
    (inAlph_natCode tag_C)
    (iaPi gCodeOfDefAlph
          (ap2 pi (mcodeMu (mcode1 predFlipDefAlph)) (mcode1 u))
      (inAlph_mcode2 (Lift1 outKdefAlph))
      (iaPi (mcodeMu (mcode1 predFlipDefAlph)) (mcode1 u)
        (inAlph_mcodeMu (mcode1 predFlipDefAlph) (inAlph_mcode1 predFlipDefAlph))
        (inAlph_mcode1 u)))

dRT_gLDefAlph : Deriv (eqF (ap1 parse (enc gLcodeDefAlph)) gLcodeDefAlph)
dRT_gLDefAlph = parse_enc gLcodeDefAlph inAlph_gLcodeDefAlph
