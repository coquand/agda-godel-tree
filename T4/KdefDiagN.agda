{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.KdefDiagN -- the number-code re-pointing of T4.KdefDiag : the diagonal
-- program code  gLcodeDefN  whose mu-loop recognises the honest  KdefN  code
-- ( via  hitKdefN / outKdefN , T4.KdefRecogN ), with the parse round-trip.
-- Verbatim mirror : KdefDiag is generic in the recogniser; only the
-- KdefRecog -> KdefRecogN swap is needed, L absorbed into predN .

open import T4.Base

module T4.KdefDiagN (predN : Term) where

open import T4.Tags        using ( tag_C )
open import T4.KdefRecogN predN using ( hitKdefN ; outKdefN )
open import T4.EvalU       using ( mcode1 ; mcode2 ; mcodeMu )
open import T4.McodeInAlph using
  ( inAlph_natCode ; inAlph_mcode1 ; inAlph_mcode2 ; inAlph_mcodeMu )
open import T4.ProgEnc     using ( enc )
open import T4.ProgParse   using ( parse ; parse_enc ; InAlph ; iaPi )

open import BRA3.Church      using ( pi ; isZero )
open import BRA3.Fan         using ( Lift1 ; compose1U )

------------------------------------------------------------------------
-- Concrete diagonal pieces ( the threshold is the module's  predN ).

-- the mu-predicate:  predFlipDefN n = isZero (hitKdefN outKdefN n) .
predFlipDefN : Fun1
predFlipDefN = compose1U isZero (hitKdefN outKdefN)

-- the output transform.
gCodeOfDefN : Term
gCodeOfDefN = mcode2 (Lift1 outKdefN)

-- the diagonal program code  ⌜g_L⌝  = C (Lift1 outKdefN) (mu predFlipDefN) u .
gLcodeDefN : Term
gLcodeDefN =
  ap2 pi (natCode tag_C)
    (ap2 pi gCodeOfDefN
       (ap2 pi (mcodeMu (mcode1 predFlipDefN)) (mcode1 u)))

------------------------------------------------------------------------
-- InAlph membership and the parse round-trip.

inAlph_gLcodeDefN : InAlph gLcodeDefN
inAlph_gLcodeDefN =
  iaPi (natCode tag_C)
       (ap2 pi gCodeOfDefN
          (ap2 pi (mcodeMu (mcode1 predFlipDefN)) (mcode1 u)))
    (inAlph_natCode tag_C)
    (iaPi gCodeOfDefN
          (ap2 pi (mcodeMu (mcode1 predFlipDefN)) (mcode1 u))
      (inAlph_mcode2 (Lift1 outKdefN))
      (iaPi (mcodeMu (mcode1 predFlipDefN)) (mcode1 u)
        (inAlph_mcodeMu (mcode1 predFlipDefN) (inAlph_mcode1 predFlipDefN))
        (inAlph_mcode1 u)))

dRT_gLDefN : Deriv (eqF (ap1 parse (enc gLcodeDefN)) gLcodeDefN)
dRT_gLDefN = parse_enc gLcodeDefN inAlph_gLcodeDefN
