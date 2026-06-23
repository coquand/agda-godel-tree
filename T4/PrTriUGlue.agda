{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.PrTriUGlue -- the per-tag GLUE for the full-PR bundled CR dispatch.  Each
-- glue proves  imp <tag-hyp> (imp PA (conj3 sK = O))  with sK = s (var 0) and
-- PA = (sigma bigK (wfRedFull sK) = O) packing PhiKU + validity, by assembling
-- conj3 sK = O from the three facts (V/S/T) via the imp-form opaque eqs + the
-- built per-constructor eqs + the child IH facts.  Mirrors T4.TriUGlue (toy),
-- adapted to wfRedFull / 9 tags.
--
-- This file: shared defs + the leaf (reflO) glue (validates the full assembly).
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.PrTriUGlue where

open import T4.Base

open import T4.PrDerCode using ( derLeaf ; dgReflO ; dgAp1c ; dgAp2c ; dgRo ; dgRu ; dgRv ; dgRC ; dgRb ; dgRs )
open import T4.DerCodeS using ( dtag ; pL ; pR )
open import T4.PrCodeObj using ( tmO )
open import T4.PrWfRed using ( wfRed ; wfRed_reflO )
open import T4.PrWfFunRec using ( wfFunRec ; wfFunRec_reflO )
open import T4.PrWfRedFull using ( wfRedFull ; wfRedFull_eq ; piBothO )
open import T4.PrTri using ( triF )
open import T4.PrSrc using ( srcF ; srcF_reflO )
open import T4.PrTgt using ( tgtF ; tgtF_reflO )
open import T4.PrDev using ( devF ) renaming ( devF_tmO to devFtmO )
open import T4.PrQCheckU using ( conj3 ; qcheckU )
open import T4.PrQCheckProjU using ( PhiKU ; QofChildU )
open import T4.PrCRGlueU using ( conj3_unfold )
open import T4.PrCRGlueImpU
  using ( childV_imp ; childS_imp ; childT_imp ; eqDecO_complete_imp ; sigmaBothO_imp )
open import T4.EqDecO using ( eqDecO )

open import T4.PrTriUOpaqueImp using ( triF_op_reflO_imp )
open import T4.PrSrcUOpaqueImp using ( srcF_op_reflO_imp )
open import T4.PrTgtUOpaqueImp using ( tgtF_op_reflO_imp )

open import T4.BoundedConj using ( bigC )
open import T4.WfRedExtract using ( pLValueBound ; pRValueBound )
open import T4.DescSnd using ( posNeqO )

open import BRA3.Church      using ( pi ; sigma ; sub ; predecessor ; T_p_S_v0 )
open import BRA3.ChurchLeq   using ( leq ; T76 )
open import BRA3.ChurchT78   using ( T78 )
open import BRA3.RuleInst2   using ( ruleInst2 )
open import T4.SigmaZeroN    using ( sigmaZeroL ; sigmaZeroR )
open import BRA3.Contrapositive using ( compI ; liftP ; identP )
open import T4.CtxKit using ( lift2 ; ap2c ; trans2c )
open import T4.Thm12.ImpHelpers using ( impCong1 )
open import BRA3.Logic using ( eqSymImp )

------------------------------------------------------------------------
-- Shared definitions for  sK = s (var 0) .

sK : Term
sK = ap1 s (var 0)

bigK : Term
bigK = ap2 (bigC qcheckU) O (var 0)

Aform : Formula
Aform = eqF (ap1 wfRedFull sK) O

PA : Formula
PA = eqF (ap2 sigma bigK (ap1 wfRedFull sK)) O

negLeaf : Formula
negLeaf = neg (eqF (ap1 Fst sK) (natCode 1))

Bgoal : Formula
Bgoal = eqF (ap1 conj3 sK) O

ne_sK : Deriv (neg (eqF sK O))
ne_sK = posNeqO sK (mp (ruleInst2 0 O 1 (var 0) refl T78) (ruleInst 0 (var 0) T76))

pa2a : Deriv (imp PA Aform)
pa2a = sigmaZeroR bigK (ap1 wfRedFull sK)

pa2phik : Deriv (imp PA PhiKU)
pa2phik = sigmaZeroL bigK (ap1 wfRedFull sK)

rebound : (c : Term) -> Deriv (leq c (ap1 predecessor sK)) -> Deriv (leq c (var 0))
rebound c d = ruleTrans (congR sub c (ruleSym (ruleInst 0 (var 0) T_p_S_v0))) d

------------------------------------------------------------------------
-- The leaf (reflO) glue.  Context [Hleaf, PA] (Hleaf = Fst sK = natCode 1).
-- triF sK = derLeaf ; no children ; all facts built (derLeaf / tmO).

Hleaf : Formula
Hleaf = eqF (ap1 Fst sK) (natCode 1)

private
  addPA2 : {X : Formula} -> Deriv (imp Hleaf X) -> Deriv (imp Hleaf (imp PA X))
  addPA2 {X} d = compI d (axK X PA)

  H2cong : (f : Fun1) (a b : Term) ->
    Deriv (imp Hleaf (imp PA (eqF a b))) ->
    Deriv (imp Hleaf (imp PA (eqF (ap1 f a) (ap1 f b))))
  H2cong f a b d = ap2c (lift2 Hleaf PA (impCong1 f a b (identP (eqF a b)))) d

  H2sym : (a b : Term) ->
    Deriv (imp Hleaf (imp PA (eqF a b))) -> Deriv (imp Hleaf (imp PA (eqF b a)))
  H2sym a b d = ap2c (lift2 Hleaf PA (eqSymImp a b)) d

  wfRedFullDerLeaf : Deriv (eqF (ap1 wfRedFull derLeaf) O)
  wfRedFullDerLeaf =
    ruleTrans (wfRedFull_eq derLeaf)
      (piBothO (ap1 wfRed derLeaf) (ap1 wfFunRec derLeaf) wfRed_reflO wfFunRec_reflO)

glue_reflO : Deriv (imp Hleaf (imp PA Bgoal))
glue_reflO =
  let triEqP : Deriv (imp Hleaf (imp PA (eqF (ap1 triF sK) derLeaf)))
      triEqP = addPA2 (triF_op_reflO_imp sK ne_sK)
      tgtEqP : Deriv (imp Hleaf (imp PA (eqF (ap1 tgtF sK) tmO)))
      tgtEqP = addPA2 (tgtF_op_reflO_imp sK ne_sK)
      srcEqP : Deriv (imp Hleaf (imp PA (eqF (ap1 srcF sK) tmO)))
      srcEqP = addPA2 (srcF_op_reflO_imp sK ne_sK)
      factV : Deriv (imp Hleaf (imp PA (eqF (ap1 wfRedFull (ap1 triF sK)) O)))
      factV = trans2c (ap1 wfRedFull (ap1 triF sK)) (ap1 wfRedFull derLeaf) O
                (H2cong wfRedFull (ap1 triF sK) derLeaf triEqP)
                (lift2 Hleaf PA wfRedFullDerLeaf)
      factS : Deriv (imp Hleaf (imp PA (eqF (ap1 srcF (ap1 triF sK)) (ap1 tgtF sK))))
      factS = trans2c (ap1 srcF (ap1 triF sK)) tmO (ap1 tgtF sK)
                (trans2c (ap1 srcF (ap1 triF sK)) (ap1 srcF derLeaf) tmO
                  (H2cong srcF (ap1 triF sK) derLeaf triEqP)
                  (lift2 Hleaf PA srcF_reflO))
                (H2sym (ap1 tgtF sK) tmO tgtEqP)
      factT : Deriv (imp Hleaf (imp PA (eqF (ap1 tgtF (ap1 triF sK)) (ap1 devF (ap1 srcF sK)))))
      factT = trans2c (ap1 tgtF (ap1 triF sK)) tmO (ap1 devF (ap1 srcF sK))
                (trans2c (ap1 tgtF (ap1 triF sK)) (ap1 tgtF derLeaf) tmO
                  (H2cong tgtF (ap1 triF sK) derLeaf triEqP)
                  (lift2 Hleaf PA tgtF_reflO))
                (H2sym (ap1 devF (ap1 srcF sK)) tmO
                  (trans2c (ap1 devF (ap1 srcF sK)) (ap1 devF tmO) tmO
                    (H2cong devF (ap1 srcF sK) tmO srcEqP)
                    (lift2 Hleaf PA devFtmO)))
      eqS = eqDecO (ap1 srcF (ap1 triF sK)) (ap1 tgtF sK)
      eqT = eqDecO (ap1 tgtF (ap1 triF sK)) (ap1 devF (ap1 srcF sK))
      sO_ctx = ap2c (lift2 Hleaf PA (eqDecO_complete_imp (ap1 srcF (ap1 triF sK)) (ap1 tgtF sK))) factS
      tO_ctx = ap2c (lift2 Hleaf PA (eqDecO_complete_imp (ap1 tgtF (ap1 triF sK)) (ap1 devF (ap1 srcF sK)))) factT
      inner_ctx = ap2c (ap2c (lift2 Hleaf PA (sigmaBothO_imp eqS eqT)) sO_ctx) tO_ctx
      outer_ctx = ap2c (ap2c (lift2 Hleaf PA
                    (sigmaBothO_imp (ap1 wfRedFull (ap1 triF sK)) (ap2 sigma eqS eqT))) factV) inner_ctx
  in trans2c (ap1 conj3 sK) (ap2 sigma (ap1 wfRedFull (ap1 triF sK)) (ap2 sigma eqS eqT)) O
       (lift2 Hleaf PA (conj3_unfold sK)) outer_ctx
