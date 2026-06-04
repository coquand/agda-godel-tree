{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.KdefDiagConj -- BLOCK 4, part 2: the diagonal program at the two-slot
-- conjunction K-shape.  The exact analog of  T4.KdefDiag , re-pointed from the
-- single-atom  hitKdef / outKdef  (T4.KdefRecog) to the conjunction-shape
-- recogniser  hitKdefConj N / outKdefConj N  (T4.KdefConjRecog).
--
-- Everything here is mechanical: the FirstHit / mu-loop substrate is GENERIC in
-- the recogniser  Fun1 , so the diagonal program code  gLcodeConj N  is built by
-- the identical  C (Lift1 outKdefConj) (mu predFlipConj) u  shape and round-trips
-- by the universal  inAlph_mcode*  membership lemmas.

module T4.KdefDiagConj where

open import T4.Base
open import T4.Tags        using ( tag_C )
open import T4.KdefConjRecog using ( hitKdefConj ; outKdefConj )
open import T4.EvalU       using ( mcode1 ; mcode2 ; mcodeMu )
open import T4.McodeInAlph using
  ( inAlph_natCode ; inAlph_mcode1 ; inAlph_mcode2 ; inAlph_mcodeMu )
open import T4.ProgEnc     using ( enc )
open import T4.ProgParse   using ( parse ; parse_enc ; InAlph ; iaPi )

open import BRA3.Church      using ( pi ; isZero )
open import BRA3.Fan         using ( Lift1 ; compose1U )

module _ (enum : Fun1) where

 ----------------------------------------------------------------------
 -- Concrete diagonal pieces, functions of the conjunct count  N .

 -- the mu-predicate:  predFlipConj N n = isZero (hitKdefConj N (outKdefConj N) n)
 --   ( = O iff the conjunction-shape recogniser fires at n ).
 predFlipConj : Nat -> Fun1
 predFlipConj N = compose1U isZero (hitKdefConj enum N (outKdefConj enum N))

 -- the output transform: apply  outKdefConj N  to the first component.
 gCodeOfConj : Nat -> Term
 gCodeOfConj N = mcode2 (Lift1 (outKdefConj enum N))

 -- the diagonal program code  ⌜g_N⌝ = C (Lift1 outKdefConj) (mu predFlipConj) u .
 gLcodeConj : Nat -> Term
 gLcodeConj N =
   ap2 pi (natCode tag_C)
     (ap2 pi (gCodeOfConj N)
        (ap2 pi (mcodeMu (mcode1 (predFlipConj N))) (mcode1 u)))

 ----------------------------------------------------------------------
 -- The round-trip  parse (enc ⌜g_N⌝) = ⌜g_N⌝ .

 inAlph_gLcodeConj : (N : Nat) -> InAlph (gLcodeConj N)
 inAlph_gLcodeConj N =
   iaPi (natCode tag_C)
        (ap2 pi (gCodeOfConj N)
           (ap2 pi (mcodeMu (mcode1 (predFlipConj N))) (mcode1 u)))
     (inAlph_natCode tag_C)
     (iaPi (gCodeOfConj N)
           (ap2 pi (mcodeMu (mcode1 (predFlipConj N))) (mcode1 u))
       (inAlph_mcode2 (Lift1 (outKdefConj enum N)))
       (iaPi (mcodeMu (mcode1 (predFlipConj N))) (mcode1 u)
         (inAlph_mcodeMu (mcode1 (predFlipConj N)) (inAlph_mcode1 (predFlipConj N)))
         (inAlph_mcode1 u)))

 dRT_gLConj : (N : Nat) -> Deriv (eqF (ap1 parse (enc (gLcodeConj N))) (gLcodeConj N))
 dRT_gLConj N = parse_enc (gLcodeConj N) (inAlph_gLcodeConj N)
