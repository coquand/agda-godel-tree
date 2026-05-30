{-# OPTIONS --without-K --exact-split #-}
{-# OPTIONS --safe #-}

-- BRA4.ChaitinG1 -- the num-headed, Con-FREE Goedel-Chaitin G1 barrier:
-- the ASSEMBLY SPINE, with the ex-falso made MANIFEST.
--
-- Given the three num-headed legs (dPos, dNeg, dExF), all built WITHOUT
-- codeFormula (see CHAITIN-G1-PLAN.md / chaitin-G1-blueprint.tex), two shipped
-- encoded_mp assemble the constructed inconsistency proof  f  with
--   thmT f = codeFalse        (T proves 0=1) .
-- Supersedes the codeFormula-based  BRA4.Chaitin / BRA4.ChaitinComp .
--
-- NON-VACUITY, made manifest:  the general spine  chaitin_G1_assembly  takes a
-- single code  P  and states the negation as  cNeg P  LITERALLY -- so dNeg/dExF
-- are forced to be about  P  and its negation  cNeg P  (the genuine ex-falso
--   P -> (not P -> 0=1) ); the spine CANNOT be instantiated with non-complementary
-- codes.  The concrete  chaitin_G1  then takes  P = atomCompOf ell srch z0 ,
-- accepts dNeg in the recogniser's natural form  thmT w0 = negAtomCompOf ell srch
-- z0 , and BRIDGES it to  cNeg P  by the PROVED complementarity lemma
--   BRA4.AtomComp.negAtomCompOf_eq_cNeg_atomCompOf  (N = cNeg P).
-- No codeFormula anywhere.

module BRA4.ChaitinG1 where

open import BRA4.Base
open import BRA4.ThmT            using ( thmT )
open import BRA4.Code            using ( codeFalse )
open import BRA4.DefWit          using ( cImp ; cNeg )
open import BRA4.NegAtomComp     using ( negAtomCompOf )
open import BRA4.AtomComp        using ( atomCompOf ; negAtomCompOf_eq_cNeg_atomCompOf )
open import BRA4.ConInj          using ( cmp )
open import BRA4.Thm12.EncodedMp using ( encoded_mp )

------------------------------------------------------------------------
-- The general spine: ex-falso MANIFEST (negation = cNeg P by construction).
-- Two  encoded_mp  (code-agnostic, shipped):
--   mp1 :  thmT (cmp cExF cPos)          = cImp (cNeg P) codeFalse   (ex-falso applied to dPos)
--   mp2 :  thmT (cmp (cmp cExF cPos) w0) = codeFalse                 (then to dNeg)
-- with  f := cmp (cmp cExF cPos) w0 .
--
-- cImp a b   = ap2 Pair (natCode tag_imp) (ap2 Pair a b)   (DefWit)  -- the form encoded_mp reads
-- cmp pI pA  = ap2 Pair (natCode tag_mp)  (ap2 Pair pI pA) (ConInj)  -- and produces
-- cNeg c     = ap2 Pair (natCode tag_neg) c                (DefWit)

chaitin_G1_assembly :
  (P cPos cExF w0 : Term) ->
  -- dPos : T proves the positive atom  (code P)
  Deriv (eqF (ap1 thmT cPos) P) ->
  -- dNeg : T proves its NEGATION  (code  cNeg P  -- manifest)
  Deriv (eqF (ap1 thmT w0)  (cNeg P)) ->
  -- dExF : T proves   P -> (not P -> 0=1)   (manifestly the ex-falso for P / cNeg P)
  Deriv (eqF (ap1 thmT cExF) (cImp P (cImp (cNeg P) codeFalse))) ->
  -- conclusion: T proves 0=1, via  f := cmp (cmp cExF cPos) w0 .
  Deriv (eqF (ap1 thmT (cmp (cmp cExF cPos) w0)) codeFalse)
chaitin_G1_assembly P cPos cExF w0 dPos dNeg dExF =
  let mp1 : Deriv (eqF (ap1 thmT (cmp cExF cPos)) (cImp (cNeg P) codeFalse))
      mp1 = encoded_mp cExF cPos P (cImp (cNeg P) codeFalse) dExF dPos

      mp2 : Deriv (eqF (ap1 thmT (cmp (cmp cExF cPos) w0)) codeFalse)
      mp2 = encoded_mp (cmp cExF cPos) w0 (cNeg P) codeFalse mp1 dNeg
  in mp2

------------------------------------------------------------------------
-- The concrete barrier: P = atomCompOf ell srch z0.  dNeg is supplied in the
-- recogniser's natural form  (negAtomCompOf ell srch z0)  and BRIDGED to  cNeg P
-- by the proved complementarity lemma -- so the recogniser output is verified to
-- BE the negation of P.  dExF is the manifest ex-falso (cNeg P).  These leg types
-- are exactly what Phases 2-3 must produce.

chaitin_G1 :
  (ell : Term) (srch : Fun1) (z0 : Term) ->
  (cPos cExF w0 : Term) ->
  Deriv (eqF (ap1 thmT cPos) (ap1 (atomCompOf ell srch) z0)) ->
  Deriv (eqF (ap1 thmT w0)   (ap1 (negAtomCompOf ell srch) z0)) ->   -- recogniser form (= cNeg P)
  Deriv (eqF (ap1 thmT cExF)
             (cImp (ap1 (atomCompOf ell srch) z0)
                   (cImp (cNeg (ap1 (atomCompOf ell srch) z0)) codeFalse))) ->
  Deriv (eqF (ap1 thmT (cmp (cmp cExF cPos) w0)) codeFalse)
chaitin_G1 ell srch z0 cPos cExF w0 dPos dNeg dExF =
  chaitin_G1_assembly (ap1 (atomCompOf ell srch) z0) cPos cExF w0
    dPos
    (ruleTrans dNeg (negAtomCompOf_eq_cNeg_atomCompOf ell srch z0))   -- thmT w0 = negAtomCompOf z0 = cNeg P
    dExF
