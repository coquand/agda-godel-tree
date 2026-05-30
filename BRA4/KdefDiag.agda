{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.KdefDiag -- The diagonal program for the num-raw route.  Analog of
-- BRA4.KDiag, re-pointed from the OLD  hitK / out_L  to my num-raw  hitKdef /
-- outKdef  (BRA4.KdefRecog).  Establishes the program code  gLcodeDef L  whose
-- run is what  evalU(parse (enc gLcodeDef Lstar), n0) = s z  asserts.  This is
-- the substrate for the object-induction Mu (next).

module BRA4.KdefDiag where

open import BRA4.Base
open import BRA4.Tags        using ( tag_C )
open import BRA4.KdefRecog   using ( hitKdef ; outKdef )
open import BRA4.EvalU       using ( mcode1 ; mcode2 ; mcodeMu )
open import BRA4.McodeInAlph using
  ( inAlph_natCode ; inAlph_mcode1 ; inAlph_mcode2 ; inAlph_mcodeMu )
open import BRA4.ProgEnc     using ( enc )
open import BRA4.ProgParse   using ( parse ; parse_enc ; InAlph ; iaPi )

open import BRA3.Church      using ( pi ; isZero )
open import BRA3.Fan         using ( Lift1 ; compose1U )

------------------------------------------------------------------------
-- Concrete diagonal pieces, functions of the threshold  L .

-- the mu-predicate:  predFlipDef L n = isZero (hitKdef L (outKdef L) n)
--   ( = O iff hitKdef ... n = s O ,  i.e. the recogniser fires at n ).
predFlipDef : Term -> Fun1
predFlipDef L = compose1U isZero (hitKdef L (outKdef L))

-- the output transform  (apply outKdef to the first component, ignore the second).
gCodeOfDef : Term -> Term
gCodeOfDef L = mcode2 (Lift1 (outKdef L))

-- the diagonal program code  ⌜g_L⌝  = C (Lift1 outKdef) (mu predFlipDef) u .
gLcodeDef : Term -> Term
gLcodeDef L =
  ap2 pi (natCode tag_C)
    (ap2 pi (gCodeOfDef L)
       (ap2 pi (mcodeMu (mcode1 (predFlipDef L))) (mcode1 u)))

------------------------------------------------------------------------
-- The round-trip  parse (enc ⌜g_L⌝) = ⌜g_L⌝  via the InAlph membership of
-- the C-wrapper over  mcode2 ... ,  mcodeMu (mcode1 ...) ,  mcode1 u .

inAlph_gLcodeDef : (L : Term) -> InAlph (gLcodeDef L)
inAlph_gLcodeDef L =
  iaPi (natCode tag_C)
       (ap2 pi (gCodeOfDef L)
          (ap2 pi (mcodeMu (mcode1 (predFlipDef L))) (mcode1 u)))
    (inAlph_natCode tag_C)
    (iaPi (gCodeOfDef L)
          (ap2 pi (mcodeMu (mcode1 (predFlipDef L))) (mcode1 u))
      (inAlph_mcode2 (Lift1 (outKdef L)))
      (iaPi (mcodeMu (mcode1 (predFlipDef L))) (mcode1 u)
        (inAlph_mcodeMu (mcode1 (predFlipDef L)) (inAlph_mcode1 (predFlipDef L)))
        (inAlph_mcode1 u)))

-- the parse round-trip: parse (enc gLcodeDef L) = gLcodeDef L.
dRT_gLDef : (L : Term) -> Deriv (eqF (ap1 parse (enc (gLcodeDef L))) (gLcodeDef L))
dRT_gLDef L = parse_enc (gLcodeDef L) (inAlph_gLcodeDef L)
