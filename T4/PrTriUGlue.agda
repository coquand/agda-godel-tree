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

open import T4.PrTriUOpaqueImp using ( triF_op_reflO_imp ; triF_op_O_imp ; triF_op_U_imp ; triF_op_V_imp )
open import T4.PrSrcUOpaqueImp using ( srcF_op_reflO_imp ; srcF_op_rO_imp ; srcF_op_rU_imp ; srcF_op_rV_imp )
open import T4.PrTgtUOpaqueImp using ( tgtF_op_reflO_imp ; tgtF_op_rO_imp ; tgtF_op_rU_imp ; tgtF_op_rV_imp )
open import T4.PrWfRedUOpaqueImp using ( wfRed_op_rO_imp ; wfRed_op_rU_imp ; wfRed_op_rV_imp )
open import T4.PrWfFunRecUOpaqueImp using ( wfFunRec_op_rO_imp ; wfFunRec_op_rU_imp ; wfFunRec_op_rV_imp )
open import T4.PrDevByHead using ( devF_ap1_o_h ; devF_ap1_u_h ; devF_ap2_v_h )
open import T4.PrCodeObj using ( cZero ; cId ; cProj ; tmAp1 ; tmAp2 ; hd_cZero ; hd_cId ; hd_cProj )
open import T4.PrCRGlueImpU using ( piBothO_imp ; piZeroL_imp ; piZeroR_imp )
open import BRA3.Logic using ( prependEqLeft )
open import T4.CtxKit using ( lift3 ; ap3c ; trans3c )

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

------------------------------------------------------------------------
-- Depth-3 [negLeaf, htag, PA] helpers (shared by the node glues).

private
  Gcong : (f : Fun1) (a b : Term) (htag : Formula) ->
    Deriv (imp negLeaf (imp htag (imp PA (eqF a b)))) ->
    Deriv (imp negLeaf (imp htag (imp PA (eqF (ap1 f a) (ap1 f b)))))
  Gcong f a b htag d = ap3c (lift3 negLeaf htag PA (impCong1 f a b (identP (eqF a b)))) d

  Gsym : (a b : Term) (htag : Formula) ->
    Deriv (imp negLeaf (imp htag (imp PA (eqF a b)))) ->
    Deriv (imp negLeaf (imp htag (imp PA (eqF b a))))
  Gsym a b htag d = ap3c (lift3 negLeaf htag PA (eqSymImp a b)) d

  addPA : {X : Formula} (htag : Formula) ->
    Deriv (imp negLeaf (imp htag X)) ->
    Deriv (imp negLeaf (imp htag (imp PA X)))
  addPA {X} htag d = ap2c (lift2 negLeaf htag (axK X PA)) d

  -- wfRedFull sK = O  =>  wfRed sK = O / wfFunRec sK = O  (bare, from Aform).
  afToPi : Deriv (imp Aform (eqF (ap2 pi (ap1 wfRed sK) (ap1 wfFunRec sK)) O))
  afToPi = prependEqLeft (ap2 pi (ap1 wfRed sK) (ap1 wfFunRec sK)) (ap1 wfRedFull sK) O
             (ruleSym (wfRedFull_eq sK))
  afToWfRed : Deriv (imp Aform (eqF (ap1 wfRed sK) O))
  afToWfRed = compI afToPi (piZeroL_imp (ap1 wfRed sK) (ap1 wfFunRec sK))
  afToWfFun : Deriv (imp Aform (eqF (ap1 wfFunRec sK) O))
  afToWfFun = compI afToPi (piZeroR_imp (ap1 wfRed sK) (ap1 wfFunRec sK))

  wfRedSK_ctx : (htag : Formula) -> Deriv (imp negLeaf (imp htag (imp PA (eqF (ap1 wfRed sK) O))))
  wfRedSK_ctx htag = ap3c (lift3 negLeaf htag PA afToWfRed) (lift2 negLeaf htag pa2a)
  wfFunSK_ctx : (htag : Formula) -> Deriv (imp negLeaf (imp htag (imp PA (eqF (ap1 wfFunRec sK) O))))
  wfFunSK_ctx htag = ap3c (lift3 negLeaf htag PA afToWfFun) (lift2 negLeaf htag pa2a)

  -- combine child wfRed=O and wfFunRec=O into wfRedFull child=O (ctx).
  mkWfRedFull : (htag : Formula) (child : Term) ->
    Deriv (imp negLeaf (imp htag (imp PA (eqF (ap1 wfRed child) O)))) ->
    Deriv (imp negLeaf (imp htag (imp PA (eqF (ap1 wfFunRec child) O)))) ->
    Deriv (imp negLeaf (imp htag (imp PA (eqF (ap1 wfRedFull child) O))))
  mkWfRedFull htag child wr wf =
    let piO = ap3c (ap3c (lift3 negLeaf htag PA (piBothO_imp (ap1 wfRed child) (ap1 wfFunRec child))) wr) wf
    in trans3c (ap1 wfRedFull child) (ap2 pi (ap1 wfRed child) (ap1 wfFunRec child)) O
         (lift3 negLeaf htag PA (wfRedFull_eq child)) piO

  -- child conj3 = O  from wfRedFull child = O + the IH.
  mkChildCjFull : (htag : Formula) (child : Term) -> Deriv (leq child (var 0)) ->
    Deriv (imp negLeaf (imp htag (imp PA (eqF (ap1 wfRedFull child) O)))) ->
    Deriv (imp negLeaf (imp htag (imp PA (eqF (ap1 conj3 child) O))))
  mkChildCjFull htag child leqCh cvf =
    ap3c (ap3c (lift3 negLeaf htag PA (QofChildU child leqCh)) (lift2 negLeaf htag pa2phik)) cvf

  -- assemble conj3 sK = O from the three facts (depth-3).
  assembleConj3 : (htag : Formula) ->
    Deriv (imp negLeaf (imp htag (imp PA (eqF (ap1 wfRedFull (ap1 triF sK)) O)))) ->
    Deriv (imp negLeaf (imp htag (imp PA (eqF (ap1 srcF (ap1 triF sK)) (ap1 tgtF sK))))) ->
    Deriv (imp negLeaf (imp htag (imp PA
       (eqF (ap1 tgtF (ap1 triF sK)) (ap1 devF (ap1 srcF sK)))))) ->
    Deriv (imp negLeaf (imp htag (imp PA Bgoal)))
  assembleConj3 htag factV factS factT =
    let eqS = eqDecO (ap1 srcF (ap1 triF sK)) (ap1 tgtF sK)
        eqT = eqDecO (ap1 tgtF (ap1 triF sK)) (ap1 devF (ap1 srcF sK))
        sO_ctx = ap3c (lift3 negLeaf htag PA
                   (eqDecO_complete_imp (ap1 srcF (ap1 triF sK)) (ap1 tgtF sK))) factS
        tO_ctx = ap3c (lift3 negLeaf htag PA
                   (eqDecO_complete_imp (ap1 tgtF (ap1 triF sK)) (ap1 devF (ap1 srcF sK)))) factT
        inner_ctx = ap3c (ap3c (lift3 negLeaf htag PA (sigmaBothO_imp eqS eqT)) sO_ctx) tO_ctx
        outer_ctx = ap3c (ap3c (lift3 negLeaf htag PA
                      (sigmaBothO_imp (ap1 wfRedFull (ap1 triF sK)) (ap2 sigma eqS eqT))) factV) inner_ctx
    in trans3c (ap1 conj3 sK) (ap2 sigma (ap1 wfRedFull (ap1 triF sK)) (ap2 sigma eqS eqT)) O
         (lift3 negLeaf htag PA (conj3_unfold sK)) outer_ctx

------------------------------------------------------------------------
-- glue_rO :  triF sK = derLeaf ; srcF sK = tmAp1 cZero (srcF pL) ; tgtF sK = tmO.
-- No children needed (endpoints collapse via the built derLeaf / devF_ap1_o eqs).

glue_rO : Deriv (imp negLeaf (imp (eqF (ap1 Fst (dtag sK)) dgRo) (imp PA Bgoal)))
glue_rO =
  let htag = eqF (ap1 Fst (dtag sK)) dgRo
      chL = pL sK
      triEq = addPA htag (triF_op_O_imp sK ne_sK)
      tgtEqSK = addPA htag (tgtF_op_rO_imp sK ne_sK)
      srcEqSK = addPA htag (srcF_op_rO_imp sK ne_sK)
      factV = trans3c (ap1 wfRedFull (ap1 triF sK)) (ap1 wfRedFull derLeaf) O
                (Gcong wfRedFull (ap1 triF sK) derLeaf htag triEq)
                (lift3 negLeaf htag PA wfRedFullDerLeaf)
      factS = trans3c (ap1 srcF (ap1 triF sK)) tmO (ap1 tgtF sK)
                (trans3c (ap1 srcF (ap1 triF sK)) (ap1 srcF derLeaf) tmO
                  (Gcong srcF (ap1 triF sK) derLeaf htag triEq)
                  (lift3 negLeaf htag PA srcF_reflO))
                (Gsym (ap1 tgtF sK) tmO htag tgtEqSK)
      devSrcEq = trans3c (ap1 devF (ap1 srcF sK)) (ap1 devF (tmAp1 cZero (ap1 srcF chL))) tmO
                   (Gcong devF (ap1 srcF sK) (tmAp1 cZero (ap1 srcF chL)) htag srcEqSK)
                   (lift3 negLeaf htag PA (devF_ap1_o_h cZero (ap1 srcF chL) hd_cZero))
      factT = trans3c (ap1 tgtF (ap1 triF sK)) tmO (ap1 devF (ap1 srcF sK))
                (trans3c (ap1 tgtF (ap1 triF sK)) (ap1 tgtF derLeaf) tmO
                  (Gcong tgtF (ap1 triF sK) derLeaf htag triEq)
                  (lift3 negLeaf htag PA tgtF_reflO))
                (Gsym (ap1 devF (ap1 srcF sK)) tmO htag devSrcEq)
  in assembleConj3 htag factV factS factT

------------------------------------------------------------------------
-- glue_rU :  triF sK = triF (pL sK) ; srcF sK = tmAp1 cId (srcF pL) ; tgtF sK = tgtF pL.

glue_rU : Deriv (imp negLeaf (imp (eqF (ap1 Fst (dtag sK)) dgRu) (imp PA Bgoal)))
glue_rU =
  let htag = eqF (ap1 Fst (dtag sK)) dgRu
      ch = pL sK
      leqCh = rebound ch (pLValueBound sK ne_sK)
      wfRedChO = trans3c (ap1 wfRed ch) (ap1 wfRed sK) O
                   (Gsym (ap1 wfRed sK) (ap1 wfRed ch) htag (addPA htag (wfRed_op_rU_imp sK ne_sK)))
                   (wfRedSK_ctx htag)
      wfFunChO = trans3c (ap1 wfFunRec ch) (ap1 wfFunRec sK) O
                   (Gsym (ap1 wfFunRec sK) (ap1 wfFunRec ch) htag (addPA htag (wfFunRec_op_rU_imp sK ne_sK)))
                   (wfFunSK_ctx htag)
      childCj = mkChildCjFull htag ch leqCh (mkWfRedFull htag ch wfRedChO wfFunChO)
      cV = ap3c (lift3 negLeaf htag PA (childV_imp ch)) childCj
      cS = ap3c (lift3 negLeaf htag PA (childS_imp ch)) childCj
      cT = ap3c (lift3 negLeaf htag PA (childT_imp ch)) childCj
      triEq = addPA htag (triF_op_U_imp sK ne_sK)
      tgtEqSK = addPA htag (tgtF_op_rU_imp sK ne_sK)
      srcEqSK = addPA htag (srcF_op_rU_imp sK ne_sK)
      factV = trans3c (ap1 wfRedFull (ap1 triF sK)) (ap1 wfRedFull (ap1 triF ch)) O
                (Gcong wfRedFull (ap1 triF sK) (ap1 triF ch) htag triEq) cV
      factS = trans3c (ap1 srcF (ap1 triF sK)) (ap1 srcF (ap1 triF ch)) (ap1 tgtF sK)
                (Gcong srcF (ap1 triF sK) (ap1 triF ch) htag triEq)
                (trans3c (ap1 srcF (ap1 triF ch)) (ap1 tgtF ch) (ap1 tgtF sK)
                  cS (Gsym (ap1 tgtF sK) (ap1 tgtF ch) htag tgtEqSK))
      devSrcEq = trans3c (ap1 devF (ap1 srcF sK)) (ap1 devF (tmAp1 cId (ap1 srcF ch))) (ap1 devF (ap1 srcF ch))
                   (Gcong devF (ap1 srcF sK) (tmAp1 cId (ap1 srcF ch)) htag srcEqSK)
                   (lift3 negLeaf htag PA (devF_ap1_u_h cId (ap1 srcF ch) hd_cId))
      factT = trans3c (ap1 tgtF (ap1 triF sK)) (ap1 tgtF (ap1 triF ch)) (ap1 devF (ap1 srcF sK))
                (Gcong tgtF (ap1 triF sK) (ap1 triF ch) htag triEq)
                (trans3c (ap1 tgtF (ap1 triF ch)) (ap1 devF (ap1 srcF ch)) (ap1 devF (ap1 srcF sK))
                  cT (Gsym (ap1 devF (ap1 srcF sK)) (ap1 devF (ap1 srcF ch)) htag devSrcEq))
  in assembleConj3 htag factV factS factT

------------------------------------------------------------------------
-- glue_rV :  triF sK = triF (pR sK) ; srcF sK = tmAp2 cProj (srcF pL) (srcF pR) ; tgtF sK = tgtF pR.

glue_rV : Deriv (imp negLeaf (imp (eqF (ap1 Fst (dtag sK)) dgRv) (imp PA Bgoal)))
glue_rV =
  let htag = eqF (ap1 Fst (dtag sK)) dgRv
      chL = pL sK
      chR = pR sK
      leqR = rebound chR (pRValueBound sK ne_sK)
      wfRedPiO = trans3c (ap2 pi (ap1 wfRed chL) (ap1 wfRed chR)) (ap1 wfRed sK) O
                   (Gsym (ap1 wfRed sK) (ap2 pi (ap1 wfRed chL) (ap1 wfRed chR)) htag
                      (addPA htag (wfRed_op_rV_imp sK ne_sK)))
                   (wfRedSK_ctx htag)
      wfFunPiO = trans3c (ap2 pi (ap1 wfFunRec chL) (ap1 wfFunRec chR)) (ap1 wfFunRec sK) O
                   (Gsym (ap1 wfFunRec sK) (ap2 pi (ap1 wfFunRec chL) (ap1 wfFunRec chR)) htag
                      (addPA htag (wfFunRec_op_rV_imp sK ne_sK)))
                   (wfFunSK_ctx htag)
      wfRedChO = ap3c (lift3 negLeaf htag PA (piZeroR_imp (ap1 wfRed chL) (ap1 wfRed chR))) wfRedPiO
      wfFunChO = ap3c (lift3 negLeaf htag PA (piZeroR_imp (ap1 wfFunRec chL) (ap1 wfFunRec chR))) wfFunPiO
      childCj = mkChildCjFull htag chR leqR (mkWfRedFull htag chR wfRedChO wfFunChO)
      cV = ap3c (lift3 negLeaf htag PA (childV_imp chR)) childCj
      cS = ap3c (lift3 negLeaf htag PA (childS_imp chR)) childCj
      cT = ap3c (lift3 negLeaf htag PA (childT_imp chR)) childCj
      triEq = addPA htag (triF_op_V_imp sK ne_sK)
      tgtEqSK = addPA htag (tgtF_op_rV_imp sK ne_sK)
      srcEqSK = addPA htag (srcF_op_rV_imp sK ne_sK)
      factV = trans3c (ap1 wfRedFull (ap1 triF sK)) (ap1 wfRedFull (ap1 triF chR)) O
                (Gcong wfRedFull (ap1 triF sK) (ap1 triF chR) htag triEq) cV
      factS = trans3c (ap1 srcF (ap1 triF sK)) (ap1 srcF (ap1 triF chR)) (ap1 tgtF sK)
                (Gcong srcF (ap1 triF sK) (ap1 triF chR) htag triEq)
                (trans3c (ap1 srcF (ap1 triF chR)) (ap1 tgtF chR) (ap1 tgtF sK)
                  cS (Gsym (ap1 tgtF sK) (ap1 tgtF chR) htag tgtEqSK))
      devSrcEq = trans3c (ap1 devF (ap1 srcF sK))
                   (ap1 devF (tmAp2 cProj (ap1 srcF chL) (ap1 srcF chR))) (ap1 devF (ap1 srcF chR))
                   (Gcong devF (ap1 srcF sK) (tmAp2 cProj (ap1 srcF chL) (ap1 srcF chR)) htag srcEqSK)
                   (lift3 negLeaf htag PA (devF_ap2_v_h cProj (ap1 srcF chL) (ap1 srcF chR) hd_cProj))
      factT = trans3c (ap1 tgtF (ap1 triF sK)) (ap1 tgtF (ap1 triF chR)) (ap1 devF (ap1 srcF sK))
                (Gcong tgtF (ap1 triF sK) (ap1 triF chR) htag triEq)
                (trans3c (ap1 tgtF (ap1 triF chR)) (ap1 devF (ap1 srcF chR)) (ap1 devF (ap1 srcF sK))
                  cT (Gsym (ap1 devF (ap1 srcF sK)) (ap1 devF (ap1 srcF chR)) htag devSrcEq))
  in assembleConj3 htag factV factS factT
