{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.TreeToDigits -- brick 1 of the number-code Chaitin redo
-- (CHAITIN-NUMBER-CODE-HANDOFF.md S6.1).
--
-- The preorder digit-extractor  treeToDigits : Term -> TStr  mirroring
-- ProgEnc.encApp's tag assignment ( O/var -> t1 , ap1 -> t2 , ap2 -> t3 ),
-- with the headline meta law
--
--   toStr (treeToDigits t) = enc t .
--
-- Composed with CandidateCover.coverage this gives the DIAGONAL MEMBERSHIP
--   candidate (natCode (rank (treeToDigits gL))) = enc gL ,
-- i.e. the diagonal program  gL  IS the candidate at its base-3 rank, with
-- NO surjective pairing.  All meta ( Eq on Term ), structural recursion.

module T4.TreeToDigits where

open import T4.Base
open import T4.ProgEnc      using ( encApp ; enc ; tagLeaf ; tagUnary ; tagBinary )
open import T4.CandidateCover using ( Tri ; t1 ; t2 ; t3 ; TStr ; tnil ; tcons ; toStr )

open import BRA3.Church using ( pi )

------------------------------------------------------------------------
-- SECTION 1.  The threaded extractor.   treeToDigitsApp t rest =
-- (preorder digits of t) ++ rest , mirroring encApp's three cells.

treeToDigitsApp : Term -> TStr -> TStr
treeToDigitsApp O          rest = tcons t1 rest
treeToDigitsApp (var k)    rest = tcons t1 rest
treeToDigitsApp (ap1 f t)  rest = tcons t2 (treeToDigitsApp t rest)
treeToDigitsApp (ap2 g a b) rest = tcons t3 (treeToDigitsApp a (treeToDigitsApp b rest))

treeToDigits : Term -> TStr
treeToDigits t = treeToDigitsApp t tnil

------------------------------------------------------------------------
-- SECTION 2.  The threaded law:  toStr (treeToDigitsApp t rest) =
-- encApp t (toStr rest) .   Structural recursion on t, matching encApp.

toStr_treeToDigitsApp :
  (t : Term) (rest : TStr) ->
  Eq (toStr (treeToDigitsApp t rest)) (encApp t (toStr rest))
toStr_treeToDigitsApp O          rest = refl
toStr_treeToDigitsApp (var k)    rest = refl
toStr_treeToDigitsApp (ap1 f t)  rest =
  eqCong (ap2 pi (natCode tagUnary)) (toStr_treeToDigitsApp t rest)
toStr_treeToDigitsApp (ap2 g a b) rest =
  eqCong (ap2 pi (natCode tagBinary))
    (eqTrans (toStr_treeToDigitsApp a (treeToDigitsApp b rest))
             (eqCong (encApp a) (toStr_treeToDigitsApp b rest)))

------------------------------------------------------------------------
-- SECTION 3.  HEADLINE:  toStr (treeToDigits t) = enc t .

toStr_treeToDigits :
  (t : Term) -> Eq (toStr (treeToDigits t)) (enc t)
toStr_treeToDigits t = toStr_treeToDigitsApp t tnil
