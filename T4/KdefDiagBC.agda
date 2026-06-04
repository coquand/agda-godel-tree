{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.KdefDiagBC -- the diagonal program at the framework's  KdefBigConj
-- shape ( T4.KdefBigConjRecog ).   A mechanical port of  T4.KdefDiagConj ,
-- re-pointed from the block-4 recogniser  hitKdefConj / outKdefConj  to the
-- output-slot recogniser  hitBC enum M / outBC enum fuel M .
--
-- The FirstHit / mu-loop substrate is GENERIC in the recogniser  Fun1 , so
-- the diagonal program code  gLcodeBC M  is built by the identical
--  C (Lift1 outBC) (mu predFlipBC) u  shape and round-trips by the
-- universal  inAlph_mcode*  membership lemmas.

module T4.KdefDiagBC where

open import T4.Base
open import T4.Tags        using ( tag_C )
open import T4.KdefBigConjRecog using ( hitBC ; outBC )
open import T4.EvalU       using ( mcode1 ; mcode2 ; mcodeMu )
open import T4.McodeInAlph using
  ( inAlph_natCode ; inAlph_mcode1 ; inAlph_mcode2 ; inAlph_mcodeMu )
open import T4.ProgEnc     using ( enc )
open import T4.ProgParse   using ( parse ; parse_enc ; InAlph ; iaPi )

open import BRA3.Church      using ( pi ; isZero )
open import BRA3.Fan         using ( Lift1 ; compose1U )

module _ (enum : Fun1) (fuel : Term) where

 ----------------------------------------------------------------------
 -- Concrete diagonal pieces, functions of the conjunct count  M .

 -- the mu-predicate:  predFlipBC M n = isZero (hitBC enum fuel M (outBC enum fuel M) n)
 --   ( = O iff the output-slot recogniser fires at n ).
 predFlipBC : Nat -> Fun1
 predFlipBC M = compose1U isZero (hitBC enum fuel M (outBC enum fuel M))

 -- the output transform: apply  outBC enum fuel M  to the first component.
 gCodeOfBC : Nat -> Term
 gCodeOfBC M = mcode2 (Lift1 (outBC enum fuel M))

 -- the diagonal program code  = C (Lift1 outBC) (mu predFlipBC) u .
 gLcodeBC : Nat -> Term
 gLcodeBC M =
   ap2 pi (natCode tag_C)
     (ap2 pi (gCodeOfBC M)
        (ap2 pi (mcodeMu (mcode1 (predFlipBC M))) (mcode1 u)))

 ----------------------------------------------------------------------
 -- The round-trip  parse (enc gLcodeBC) = gLcodeBC .

 inAlph_gLcodeBC : (M : Nat) -> InAlph (gLcodeBC M)
 inAlph_gLcodeBC M =
   iaPi (natCode tag_C)
        (ap2 pi (gCodeOfBC M)
           (ap2 pi (mcodeMu (mcode1 (predFlipBC M))) (mcode1 u)))
     (inAlph_natCode tag_C)
     (iaPi (gCodeOfBC M)
           (ap2 pi (mcodeMu (mcode1 (predFlipBC M))) (mcode1 u))
       (inAlph_mcode2 (Lift1 (outBC enum fuel M)))
       (iaPi (mcodeMu (mcode1 (predFlipBC M))) (mcode1 u)
         (inAlph_mcodeMu (mcode1 (predFlipBC M)) (inAlph_mcode1 (predFlipBC M)))
         (inAlph_mcode1 u)))

 dRT_gLBC : (M : Nat) -> Deriv (eqF (ap1 parse (enc (gLcodeBC M))) (gLcodeBC M))
 dRT_gLBC M = parse_enc (gLcodeBC M) (inAlph_gLcodeBC M)
