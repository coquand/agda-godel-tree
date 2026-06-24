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

open import T4.PrDerCode using ( derLeaf ; dgReflO ; dgAp1c ; dgAp2c ; dgRo ; dgRu ; dgRv ; dgRC ; dgRb ; dgRs ; ap1c )
  renaming ( ap2c to dAp2c )
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
open import T4.Thm12.ImpHelpers using ( impCong1 ; impCongL ; impCongR ; impEqTrans ; impLift )
open import BRA3.Logic using ( eqSymImp )

-- compound-glue extras
open import T4.PrCodeObj using
  ( tgAp1 ; tgAp2 ; cComp ; cRec ; cSuc
  ; compFun ; compH1 ; compH2 ; recFun ; recH1 ; recH2 ; hd_cComp ; hd_cRec ; hd_cSuc )
open import T4.PrDevByHead using
  ( gF ; h1F ; h2F ; devF_ap1_C_h ; devF_ap1_s_h
  ; devF_ap2_Rb_h ; devF_ap2_Rs_h ; devF_ap2_Rcong_h )
open import T4.PrTgtUOpaque using ( funP ; gP ; h1P ; h2P )
open import T4.PrWfFunRec using ( funValid ; wfFunRec_ap1c ; wfFunRec_ap2c )
open import T4.PrFunValid using ( funValid_C ; funValid_R )
open import T4.PrSrc using ( srcF_ap1c ; srcF_ap2c )
open import T4.PrTgt using ( tgtF_ap1c ; tgtF_ap2c )
open import T4.PrWfRed using ( wfRed_ap1c ; wfRed_ap2c )
open import T4.PrTriUOpaqueImp using ( triF_op_C_imp ; triF_op_Rb_imp ; triF_op_Rs_imp )
open import T4.PrSrcUOpaqueImp using
  ( srcF_op_rC_imp ; srcF_op_rRb_imp ; srcF_op_rRs_imp ; srcF_op_ap1c_imp ; srcF_op_ap2c_imp )
open import T4.PrTgtUOpaqueImp using
  ( tgtF_op_rC_imp ; tgtF_op_rRb_imp ; tgtF_op_rRs_imp ; tgtF_op_ap1c_imp ; tgtF_op_ap2c_imp )
open import T4.PrWfRedUOpaqueImp using
  ( wfRed_op_rC_imp ; wfRed_op_rRb_imp ; wfRed_op_rRs_imp ; wfRed_op_ap1c_imp ; wfRed_op_ap2c_imp )
open import T4.PrWfFunRecUOpaqueImp using
  ( wfFunRec_op_rC_imp ; wfFunRec_op_rRb_imp ; wfFunRec_op_rRs_imp
  ; wfFunRec_op_ap1c_imp ; wfFunRec_op_ap2c_imp )

-- reconstruction extras (rRs / ap1c-C / ap2c-cRec): deep wfFun extraction + funValid_R/C.
open import T4.PrWfFun using ( wfFun ; isF1 ; isF2 )
open import T4.PrWfFunUOpaque using ( wfFun_op_C ; wfFun_op_R )
open import T4.PrFunValidCanon using ( funValidF ; funValidF_eq )
open import T4.PrFunValid using ( recon ; recon_R ; cG ; cH1 ; cH2 )
open import T4.PrCRGlueImpU using ( eqDecO_sound_imp )
open import BRA3.Contrapositive using ( axContrapos )
open import BRA3.SubT.NatEq using ( natEqF )
open import BRA3.SubT.V2NatNeq using ( NatNeqWitness ; natEqF_at_neq ; decideNatNeq )
open import T4.AdDispatchAux using ( FstO )
open import T4.PrTriUOpaqueImp using ( triF_op_Rs_imp )
open import T4.PrSrcUOpaqueImp using ( srcF_op_rRs_imp )
open import T4.PrTgtUOpaqueImp using ( tgtF_op_rRs_imp )
open import T4.PrWfRedUOpaqueImp using ( wfRed_op_rRs_imp )
open import T4.PrDevByHead using ( devF_ap2_Rs_h )

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

------------------------------------------------------------------------
-- Cong-helper layer (for the compound glues rC / rRb / rRs / ap1c / ap2c).

private
  -- bare congruences on the term-builders tmAp1 / tmAp2.
  tmAp1FunCong : (f g Y : Term) -> Deriv (eqF f g) -> Deriv (eqF (tmAp1 f Y) (tmAp1 g Y))
  tmAp1FunCong f g Y e = congR Pair tgAp1 (congL Pair Y e)

  tmAp2Cong : (G G' A A' B B' : Term) ->
    Deriv (eqF G G') -> Deriv (eqF A A') -> Deriv (eqF B B') ->
    Deriv (eqF (tmAp2 G A B) (tmAp2 G' A' B'))
  tmAp2Cong G G' A A' B B' eG eA eB =
    congR Pair tgAp2
      (ruleTrans (congL Pair (ap2 Pair A B) eG)
                 (congR Pair G' (ruleTrans (congL Pair B eA) (congR Pair A' eB))))

  -- congCC : the cComp-component projections gF/h1F/h2F collapse to g/h1/h2.
  congCC : (g h1 h2 Y : Term) ->
    Deriv (eqF (tmAp2 (gF (cComp g h1 h2)) (tmAp1 (h1F (cComp g h1 h2)) Y) (tmAp1 (h2F (cComp g h1 h2)) Y))
               (tmAp2 g (tmAp1 h1 Y) (tmAp1 h2 Y)))
  congCC g h1 h2 Y =
    tmAp2Cong (gF (cComp g h1 h2)) g
              (tmAp1 (h1F (cComp g h1 h2)) Y) (tmAp1 h1 Y)
              (tmAp1 (h2F (cComp g h1 h2)) Y) (tmAp1 h2 Y)
              (compFun g h1 h2)
              (tmAp1FunCong (h1F (cComp g h1 h2)) h1 Y (compH1 g h1 h2))
              (tmAp1FunCong (h2F (cComp g h1 h2)) h2 Y (compH2 g h1 h2))

  congRC : (g h1 h2 Y : Term) ->
    Deriv (eqF (tmAp2 (gF (cRec g h1 h2)) (tmAp1 (h1F (cRec g h1 h2)) Y) (tmAp1 (h2F (cRec g h1 h2)) Y))
               (tmAp2 g (tmAp1 h1 Y) (tmAp1 h2 Y)))
  congRC g h1 h2 Y =
    tmAp2Cong (gF (cRec g h1 h2)) g
              (tmAp1 (h1F (cRec g h1 h2)) Y) (tmAp1 h1 Y)
              (tmAp1 (h2F (cRec g h1 h2)) Y) (tmAp1 h2 Y)
              (recFun g h1 h2)
              (tmAp1FunCong (h1F (cRec g h1 h2)) h1 Y (recH1 g h1 h2))
              (tmAp1FunCong (h2F (cRec g h1 h2)) h2 Y (recH2 g h1 h2))

  -- bare imp-form congruences for the depth-3 ctx wrappers.
  tmAp1ArgImp : (f a b : Term) -> Deriv (imp (eqF a b) (eqF (tmAp1 f a) (tmAp1 f b)))
  tmAp1ArgImp f a b =
    impCongR Pair (ap2 Pair f a) (ap2 Pair f b) tgAp1 (impCongR Pair a b f (identP (eqF a b)))

  tmAp2Arg1Imp : (g a a' b : Term) -> Deriv (imp (eqF a a') (eqF (tmAp2 g a b) (tmAp2 g a' b)))
  tmAp2Arg1Imp g a a' b =
    impCongR Pair (ap2 Pair g (ap2 Pair a b)) (ap2 Pair g (ap2 Pair a' b)) tgAp2
      (impCongR Pair (ap2 Pair a b) (ap2 Pair a' b) g (impCongL Pair a a' b (identP (eqF a a'))))

  tmAp2Arg2Imp : (g a b b' : Term) -> Deriv (imp (eqF b b') (eqF (tmAp2 g a b) (tmAp2 g a b')))
  tmAp2Arg2Imp g a b b' =
    impCongR Pair (ap2 Pair g (ap2 Pair a b)) (ap2 Pair g (ap2 Pair a b')) tgAp2
      (impCongR Pair (ap2 Pair a b) (ap2 Pair a b') g (impCongR Pair b b' a (identP (eqF b b'))))

  -- depth-3 [negLeaf, htag, PA] cong wrappers.
  GcongTmAp1 : (f a b : Term) (htag : Formula) ->
    Deriv (imp negLeaf (imp htag (imp PA (eqF a b)))) ->
    Deriv (imp negLeaf (imp htag (imp PA (eqF (tmAp1 f a) (tmAp1 f b)))))
  GcongTmAp1 f a b htag d = ap3c (lift3 negLeaf htag PA (tmAp1ArgImp f a b)) d

  GcongAp2R : (g a a' b b' : Term) (htag : Formula) ->
    Deriv (imp negLeaf (imp htag (imp PA (eqF a a')))) ->
    Deriv (imp negLeaf (imp htag (imp PA (eqF b b')))) ->
    Deriv (imp negLeaf (imp htag (imp PA (eqF (tmAp2 g a b) (tmAp2 g a' b')))))
  GcongAp2R g a a' b b' htag dA dB =
    trans3c (tmAp2 g a b) (tmAp2 g a' b) (tmAp2 g a' b')
      (ap3c (lift3 negLeaf htag PA (tmAp2Arg1Imp g a a' b)) dA)
      (ap3c (lift3 negLeaf htag PA (tmAp2Arg2Imp g a' b b')) dB)

  -- pi (X)(Y) = O from X = O and Y = O, under ctx.
  piB : (htag : Formula) (X Y : Term) ->
    Deriv (imp negLeaf (imp htag (imp PA (eqF X O)))) ->
    Deriv (imp negLeaf (imp htag (imp PA (eqF Y O)))) ->
    Deriv (imp negLeaf (imp htag (imp PA (eqF (ap2 pi X Y) O))))
  piB htag X Y dX dY = ap3c (ap3c (lift3 negLeaf htag PA (piBothO_imp X Y)) dX) dY

  -- split wfRedFull t = O into wfRed t = O / wfFunRec t = O, under ctx.
  splitL : (htag : Formula) (t : Term) ->
    Deriv (imp negLeaf (imp htag (imp PA (eqF (ap1 wfRedFull t) O)))) ->
    Deriv (imp negLeaf (imp htag (imp PA (eqF (ap1 wfRed t) O))))
  splitL htag t d =
    ap3c (lift3 negLeaf htag PA (piZeroL_imp (ap1 wfRed t) (ap1 wfFunRec t)))
      (trans3c (ap2 pi (ap1 wfRed t) (ap1 wfFunRec t)) (ap1 wfRedFull t) O
        (Gsym (ap1 wfRedFull t) (ap2 pi (ap1 wfRed t) (ap1 wfFunRec t)) htag
          (lift3 negLeaf htag PA (wfRedFull_eq t)))
        d)

  splitR : (htag : Formula) (t : Term) ->
    Deriv (imp negLeaf (imp htag (imp PA (eqF (ap1 wfRedFull t) O)))) ->
    Deriv (imp negLeaf (imp htag (imp PA (eqF (ap1 wfFunRec t) O))))
  splitR htag t d =
    ap3c (lift3 negLeaf htag PA (piZeroR_imp (ap1 wfRed t) (ap1 wfFunRec t)))
      (trans3c (ap2 pi (ap1 wfRed t) (ap1 wfFunRec t)) (ap1 wfRedFull t) O
        (Gsym (ap1 wfRedFull t) (ap2 pi (ap1 wfRed t) (ap1 wfFunRec t)) htag
          (lift3 negLeaf htag PA (wfRedFull_eq t)))
        d)

  -- FIX(C) arity/nonzero/projection helpers (shared by the compound redex glues).
  natCode8NeqO : Deriv (neg (eqF (natCode 8) O))
  natCode8NeqO = posNeqO (natCode 8) (mp (ruleInst2 0 O 1 (natCode 7) refl T78) (ruleInst 0 (natCode 7) T76))
  natCode6NeqO : Deriv (neg (eqF (natCode 6) O))
  natCode6NeqO = posNeqO (natCode 6) (mp (ruleInst2 0 O 1 (natCode 5) refl T78) (ruleInst 0 (natCode 5) T76))

  gPiL : (htag : Formula) (X Y : Term) ->
    Deriv (imp negLeaf (imp htag (imp PA (eqF (ap2 pi X Y) O)))) ->
    Deriv (imp negLeaf (imp htag (imp PA (eqF X O))))
  gPiL htag X Y d = ap3c (lift3 negLeaf htag PA (piZeroL_imp X Y)) d
  gPiR : (htag : Formula) (X Y : Term) ->
    Deriv (imp negLeaf (imp htag (imp PA (eqF (ap2 pi X Y) O)))) ->
    Deriv (imp negLeaf (imp htag (imp PA (eqF Y O))))
  gPiR htag X Y d = ap3c (lift3 negLeaf htag PA (piZeroR_imp X Y)) d

  pairKNeqO : (k : Nat) -> Deriv (neg (eqF (natCode k) O)) -> (y : Term) ->
              Deriv (neg (eqF (ap2 Pair (natCode k) y) O))
  pairKNeqO k nek y =
    let P8 : Formula
        P8 = eqF (ap2 Pair (natCode k) y) O
        impB : Deriv (imp P8 (eqF (ap1 Fst (ap2 Pair (natCode k) y)) (ap1 Fst O)))
        impB = impCong1 Fst (ap2 Pair (natCode k) y) O (identP P8)
        impBO : Deriv (imp P8 (eqF (ap1 Fst (ap2 Pair (natCode k) y)) O))
        impBO = impEqTrans (ap1 Fst (ap2 Pair (natCode k) y)) (ap1 Fst O) O impB (impLift FstO)
        imp8O : Deriv (imp P8 (eqF (natCode k) O))
        imp8O = compI impBO
                  (prependEqLeft (natCode k) (ap1 Fst (ap2 Pair (natCode k) y)) O
                     (ruleSym (axFst (natCode k) y)))
    in mp (mp (axContrapos P8 (eqF (natCode k) O)) imp8O) nek
  pair8NeqO : (y : Term) -> Deriv (neg (eqF (ap2 Pair (natCode 8) y) O))
  pair8NeqO = pairKNeqO 8 natCode8NeqO
  pair6NeqO : (y : Term) -> Deriv (neg (eqF (ap2 Pair (natCode 6) y) O))
  pair6NeqO = pairKNeqO 6 natCode6NeqO

  isF1cong : (a b : Term) -> Deriv (eqF a b) -> Deriv (eqF (isF1 a) (isF1 b))
  isF1cong a b e =
    let fe = cong1 Fst e
        e7 = congL natEqF (natCode 7) fe
        e8 = congL natEqF (natCode 8) fe
        e1 = congL natEqF (natCode 1) fe
        innerA = ap2 pi (ap2 natEqF (ap1 Fst a) (natCode 8)) (ap2 natEqF (ap1 Fst a) (natCode 1))
        innerEq = ruleTrans (congL pi (ap2 natEqF (ap1 Fst a) (natCode 1)) e8)
                            (congR pi (ap2 natEqF (ap1 Fst b) (natCode 8)) e1)
    in ruleTrans (congL pi innerA e7)
                 (congR pi (ap2 natEqF (ap1 Fst b) (natCode 7)) innerEq)
  isF2cong : (a b : Term) -> Deriv (eqF a b) -> Deriv (eqF (isF2 a) (isF2 b))
  isF2cong a b e =
    let fe = cong1 Fst e
        e3 = congL natEqF (natCode 3) fe
        e4 = congL natEqF (natCode 4) fe
        e5 = congL natEqF (natCode 5) fe
        e6 = congL natEqF (natCode 6) fe
        e1 = congL natEqF (natCode 1) fe
        inner1A = ap2 pi (ap2 natEqF (ap1 Fst a) (natCode 6)) (ap2 natEqF (ap1 Fst a) (natCode 1))
        inner1Eq = ruleTrans (congL pi (ap2 natEqF (ap1 Fst a) (natCode 1)) e6)
                             (congR pi (ap2 natEqF (ap1 Fst b) (natCode 6)) e1)
        innerA = ap2 pi (ap2 natEqF (ap1 Fst a) (natCode 5)) inner1A
        innerEq = ruleTrans (congL pi inner1A e5)
                            (congR pi (ap2 natEqF (ap1 Fst b) (natCode 5)) inner1Eq)
        midA   = ap2 pi (ap2 natEqF (ap1 Fst a) (natCode 4)) innerA
        midEq = ruleTrans (congL pi innerA e4) (congR pi (ap2 natEqF (ap1 Fst b) (natCode 4)) innerEq)
    in ruleTrans (congL pi midA e3) (congR pi (ap2 natEqF (ap1 Fst b) (natCode 3)) midEq)

------------------------------------------------------------------------
-- glue_rC :  C-redex contraction.  triF sK = ap2c g (ap1c h1 X) (ap1c h2 X),
-- X = triF (pL sK), g/h1/h2 = funP sK components.  No reconstruction.

glue_rC : Deriv (imp negLeaf (imp (eqF (ap1 Fst (dtag sK)) dgRC) (imp PA Bgoal)))
glue_rC =
  let htag = eqF (ap1 Fst (dtag sK)) dgRC
      d  = pL sK
      X  = ap1 triF d
      g  = gP sK
      h1 = h1P sK
      h2 = h2P sK
      A  = ap1c h1 X
      B  = ap1c h2 X
      cc = cComp g h1 h2
      Y  = ap1 devF (ap1 srcF d)
      leqD = rebound d (pLValueBound sK ne_sK)
      Pcc = ap2 Pair (natCode 6) (funP sK)
      -- child wfRed at d.
      wfRedD : Deriv (imp negLeaf (imp htag (imp PA (eqF (ap1 wfRed d) O))))
      wfRedD = trans3c (ap1 wfRed d) (ap1 wfRed sK) O
                 (Gsym (ap1 wfRed sK) (ap1 wfRed d) htag (addPA htag (wfRed_op_rC_imp sK ne_sK)))
                 (wfRedSK_ctx htag)
      -- extract  ap1 wfFun Pcc = O  and  wfFunRec d = O  from wfFunRec sK = O.
      wfFunPiO = trans3c (ap2 pi (ap1 wfFun Pcc) (ap1 wfFunRec d)) (ap1 wfFunRec sK) O
                   (Gsym (ap1 wfFunRec sK) (ap2 pi (ap1 wfFun Pcc) (ap1 wfFunRec d)) htag
                     (addPA htag (wfFunRec_op_rC_imp sK ne_sK)))
                   (wfFunSK_ctx htag)
      wfPccO = gPiL htag (ap1 wfFun Pcc) (ap1 wfFunRec d) wfFunPiO
      wfFunD = gPiR htag (ap1 wfFun Pcc) (ap1 wfFunRec d) wfFunPiO
      -- deep arity+validity components via wfFun_op_C.
      h6 = axFst (natCode 6) (funP sK)
      ne6 = pair6NeqO (funP sK)
      nl6 = ruleTrans (congL natEqF (natCode 1) h6) (natEqF_at_neq 6 1 (decideNatNeq 6 1 (\ ())))
      wfCOp = wfFun_op_C Pcc ne6 nl6 h6
      tail2C = ap2 pi (ap1 wfFun (pL Pcc)) (ap1 wfFun (pR Pcc))
      tail3C = ap2 pi (ap1 wfFun (dtag Pcc)) tail2C
      tail4C = ap2 pi (isF1 (pR Pcc)) tail3C
      tail5C = ap2 pi (isF1 (pL Pcc)) tail4C
      tail6C = ap2 pi (isF2 (dtag Pcc)) tail5C
      pi7C = ap2 pi (ap1 funValidF Pcc) tail6C
      pi7CO = trans3c pi7C (ap1 wfFun Pcc) O
                (Gsym (ap1 wfFun Pcc) pi7C htag (lift3 negLeaf htag PA wfCOp)) wfPccO
      rest6 = gPiR htag (ap1 funValidF Pcc) tail6C pi7CO
      isF2dtagO = gPiL htag (isF2 (dtag Pcc)) tail5C rest6
      rest5 = gPiR htag (isF2 (dtag Pcc)) tail5C rest6
      isF1pLO = gPiL htag (isF1 (pL Pcc)) tail4C rest5
      rest4 = gPiR htag (isF1 (pL Pcc)) tail4C rest5
      isF1pRO = gPiL htag (isF1 (pR Pcc)) tail3C rest4
      rest3 = gPiR htag (isF1 (pR Pcc)) tail3C rest4
      wfdtagO = gPiL htag (ap1 wfFun (dtag Pcc)) tail2C rest3
      rest2 = gPiR htag (ap1 wfFun (dtag Pcc)) tail2C rest3
      wfpLO = gPiL htag (ap1 wfFun (pL Pcc)) (ap1 wfFun (pR Pcc)) rest2
      wfpRO = gPiR htag (ap1 wfFun (pL Pcc)) (ap1 wfFun (pR Pcc)) rest2
      -- rewrite dtag/pL/pR Pcc -> g/h1/h2.
      sndPcc = axSnd (natCode 6) (funP sK)
      dtagPcc_eq = cong1 Fst sndPcc
      pLPcc_eq = cong1 Fst (cong1 Snd sndPcc)
      pRPcc_eq = cong1 Snd (cong1 Snd sndPcc)
      isF2g = ap3c (lift3 negLeaf htag PA (prependEqLeft (isF2 g) (isF2 (dtag Pcc)) O (isF2cong g (dtag Pcc) (ruleSym dtagPcc_eq)))) isF2dtagO
      isF1h1 = ap3c (lift3 negLeaf htag PA (prependEqLeft (isF1 h1) (isF1 (pL Pcc)) O (isF1cong h1 (pL Pcc) (ruleSym pLPcc_eq)))) isF1pLO
      isF1h2 = ap3c (lift3 negLeaf htag PA (prependEqLeft (isF1 h2) (isF1 (pR Pcc)) O (isF1cong h2 (pR Pcc) (ruleSym pRPcc_eq)))) isF1pRO
      fvg = ap3c (lift3 negLeaf htag PA (prependEqLeft (ap1 wfFun g) (ap1 wfFun (dtag Pcc)) O (cong1 wfFun (ruleSym dtagPcc_eq)))) wfdtagO
      fvh1 = ap3c (lift3 negLeaf htag PA (prependEqLeft (ap1 wfFun h1) (ap1 wfFun (pL Pcc)) O (cong1 wfFun (ruleSym pLPcc_eq)))) wfpLO
      fvh2 = ap3c (lift3 negLeaf htag PA (prependEqLeft (ap1 wfFun h2) (ap1 wfFun (pR Pcc)) O (cong1 wfFun (ruleSym pRPcc_eq)))) wfpRO
      childCj = mkChildCjFull htag d leqD (mkWfRedFull htag d wfRedD wfFunD)
      cV = ap3c (lift3 negLeaf htag PA (childV_imp d)) childCj
      cS = ap3c (lift3 negLeaf htag PA (childS_imp d)) childCj
      cT = ap3c (lift3 negLeaf htag PA (childT_imp d)) childCj
      cVwfRed = splitL htag X cV
      cVwfFun = splitR htag X cV
      -- opaque eqs.
      triEq = addPA htag (triF_op_C_imp sK ne_sK)
      srcEqSK = addPA htag (srcF_op_rC_imp sK ne_sK)
      tgtEqSK = addPA htag (tgtF_op_rC_imp sK ne_sK)
      -- V-fact.
      wfRedAO = trans3c (ap1 wfRed A) (ap1 wfRed X) O (lift3 negLeaf htag PA (wfRed_ap1c h1 X)) cVwfRed
      wfRedBO = trans3c (ap1 wfRed B) (ap1 wfRed X) O (lift3 negLeaf htag PA (wfRed_ap1c h2 X)) cVwfRed
      wfRedAp2cO = trans3c (ap1 wfRed (dAp2c g A B)) (ap2 pi (ap1 wfRed A) (ap1 wfRed B)) O
                     (lift3 negLeaf htag PA (wfRed_ap2c g A B))
                     (piB htag (ap1 wfRed A) (ap1 wfRed B) wfRedAO wfRedBO)
      wfRedTriSK = trans3c (ap1 wfRed (ap1 triF sK)) (ap1 wfRed (dAp2c g A B)) O
                     (Gcong wfRed (ap1 triF sK) (dAp2c g A B) htag triEq) wfRedAp2cO
      wfFunAO = trans3c (ap1 wfFunRec A) (ap2 pi (isF1 h1) (ap2 pi (funValid h1) (ap1 wfFunRec X))) O
                  (lift3 negLeaf htag PA (wfFunRec_ap1c h1 X))
                  (piB htag (isF1 h1) (ap2 pi (funValid h1) (ap1 wfFunRec X)) isF1h1
                    (piB htag (funValid h1) (ap1 wfFunRec X) fvh1 cVwfFun))
      wfFunBO = trans3c (ap1 wfFunRec B) (ap2 pi (isF1 h2) (ap2 pi (funValid h2) (ap1 wfFunRec X))) O
                  (lift3 negLeaf htag PA (wfFunRec_ap1c h2 X))
                  (piB htag (isF1 h2) (ap2 pi (funValid h2) (ap1 wfFunRec X)) isF1h2
                    (piB htag (funValid h2) (ap1 wfFunRec X) fvh2 cVwfFun))
      wfFunAp2cO = trans3c (ap1 wfFunRec (dAp2c g A B))
                     (ap2 pi (isF2 g) (ap2 pi (funValid g) (ap2 pi (ap1 wfFunRec A) (ap1 wfFunRec B)))) O
                     (lift3 negLeaf htag PA (wfFunRec_ap2c g A B))
                     (piB htag (isF2 g) (ap2 pi (funValid g) (ap2 pi (ap1 wfFunRec A) (ap1 wfFunRec B))) isF2g
                       (piB htag (funValid g) (ap2 pi (ap1 wfFunRec A) (ap1 wfFunRec B)) fvg
                         (piB htag (ap1 wfFunRec A) (ap1 wfFunRec B) wfFunAO wfFunBO)))
      wfFunTriSK = trans3c (ap1 wfFunRec (ap1 triF sK)) (ap1 wfFunRec (dAp2c g A B)) O
                     (Gcong wfFunRec (ap1 triF sK) (dAp2c g A B) htag triEq) wfFunAp2cO
      factV = mkWfRedFull htag (ap1 triF sK) wfRedTriSK wfFunTriSK
      -- S-fact.
      srcAeq = trans3c (ap1 srcF A) (tmAp1 h1 (ap1 srcF X)) (tmAp1 h1 (ap1 tgtF d))
                 (lift3 negLeaf htag PA (srcF_ap1c h1 X))
                 (GcongTmAp1 h1 (ap1 srcF X) (ap1 tgtF d) htag cS)
      srcBeq = trans3c (ap1 srcF B) (tmAp1 h2 (ap1 srcF X)) (tmAp1 h2 (ap1 tgtF d))
                 (lift3 negLeaf htag PA (srcF_ap1c h2 X))
                 (GcongTmAp1 h2 (ap1 srcF X) (ap1 tgtF d) htag cS)
      srcTriEq = trans3c (ap1 srcF (ap1 triF sK)) (ap1 srcF (dAp2c g A B))
                   (tmAp2 g (tmAp1 h1 (ap1 tgtF d)) (tmAp1 h2 (ap1 tgtF d)))
                   (Gcong srcF (ap1 triF sK) (dAp2c g A B) htag triEq)
                   (trans3c (ap1 srcF (dAp2c g A B)) (tmAp2 g (ap1 srcF A) (ap1 srcF B))
                     (tmAp2 g (tmAp1 h1 (ap1 tgtF d)) (tmAp1 h2 (ap1 tgtF d)))
                     (lift3 negLeaf htag PA (srcF_ap2c g A B))
                     (GcongAp2R g (ap1 srcF A) (tmAp1 h1 (ap1 tgtF d)) (ap1 srcF B) (tmAp1 h2 (ap1 tgtF d))
                       htag srcAeq srcBeq))
      factS = trans3c (ap1 srcF (ap1 triF sK))
                (tmAp2 g (tmAp1 h1 (ap1 tgtF d)) (tmAp1 h2 (ap1 tgtF d))) (ap1 tgtF sK)
                srcTriEq
                (Gsym (ap1 tgtF sK) (tmAp2 g (tmAp1 h1 (ap1 tgtF d)) (tmAp1 h2 (ap1 tgtF d))) htag tgtEqSK)
      -- T-fact.
      tgtAeq = trans3c (ap1 tgtF A) (tmAp1 h1 (ap1 tgtF X)) (tmAp1 h1 Y)
                 (lift3 negLeaf htag PA (tgtF_ap1c h1 X))
                 (GcongTmAp1 h1 (ap1 tgtF X) Y htag cT)
      tgtBeq = trans3c (ap1 tgtF B) (tmAp1 h2 (ap1 tgtF X)) (tmAp1 h2 Y)
                 (lift3 negLeaf htag PA (tgtF_ap1c h2 X))
                 (GcongTmAp1 h2 (ap1 tgtF X) Y htag cT)
      tgtTriEq = trans3c (ap1 tgtF (ap1 triF sK)) (ap1 tgtF (dAp2c g A B))
                   (tmAp2 g (tmAp1 h1 Y) (tmAp1 h2 Y))
                   (Gcong tgtF (ap1 triF sK) (dAp2c g A B) htag triEq)
                   (trans3c (ap1 tgtF (dAp2c g A B)) (tmAp2 g (ap1 tgtF A) (ap1 tgtF B))
                     (tmAp2 g (tmAp1 h1 Y) (tmAp1 h2 Y))
                     (lift3 negLeaf htag PA (tgtF_ap2c g A B))
                     (GcongAp2R g (ap1 tgtF A) (tmAp1 h1 Y) (ap1 tgtF B) (tmAp1 h2 Y) htag tgtAeq tgtBeq))
      devSrcEq = trans3c (ap1 devF (ap1 srcF sK)) (ap1 devF (tmAp1 cc (ap1 srcF d)))
                   (tmAp2 g (tmAp1 h1 Y) (tmAp1 h2 Y))
                   (Gcong devF (ap1 srcF sK) (tmAp1 cc (ap1 srcF d)) htag srcEqSK)
                   (trans3c (ap1 devF (tmAp1 cc (ap1 srcF d)))
                     (tmAp2 (gF cc) (tmAp1 (h1F cc) Y) (tmAp1 (h2F cc) Y))
                     (tmAp2 g (tmAp1 h1 Y) (tmAp1 h2 Y))
                     (lift3 negLeaf htag PA (devF_ap1_C_h cc (ap1 srcF d) (hd_cComp g h1 h2)))
                     (lift3 negLeaf htag PA (congCC g h1 h2 Y)))
      factT = trans3c (ap1 tgtF (ap1 triF sK)) (tmAp2 g (tmAp1 h1 Y) (tmAp1 h2 Y))
                (ap1 devF (ap1 srcF sK))
                tgtTriEq
                (Gsym (ap1 devF (ap1 srcF sK)) (tmAp2 g (tmAp1 h1 Y) (tmAp1 h2 Y)) htag devSrcEq)
  in assembleConj3 htag factV factS factT

------------------------------------------------------------------------
-- glue_rRb :  R-base redex.  triF sK = ap1c g (triF (pL sK)) ; g = funP sK head.
--   srcF sK = tmAp2 (cRec g h1 h2) (srcF d) tmO ;  tgtF sK = tmAp1 g (tgtF d).

glue_rRb : Deriv (imp negLeaf (imp (eqF (ap1 Fst (dtag sK)) dgRb) (imp PA Bgoal)))
glue_rRb =
  let htag = eqF (ap1 Fst (dtag sK)) dgRb
      d  = pL sK
      X  = ap1 triF d
      g  = gP sK
      h1 = h1P sK
      h2 = h2P sK
      cr = cRec g h1 h2
      Y  = ap1 devF (ap1 srcF d)
      leqD = rebound d (pLValueBound sK ne_sK)
      Prr = ap2 Pair (natCode 8) (funP sK)
      wfRedD : Deriv (imp negLeaf (imp htag (imp PA (eqF (ap1 wfRed d) O))))
      wfRedD = trans3c (ap1 wfRed d) (ap1 wfRed sK) O
                 (Gsym (ap1 wfRed sK) (ap1 wfRed d) htag (addPA htag (wfRed_op_rRb_imp sK ne_sK)))
                 (wfRedSK_ctx htag)
      wfFunPiO = trans3c (ap2 pi (ap1 wfFun Prr) (ap1 wfFunRec d)) (ap1 wfFunRec sK) O
                   (Gsym (ap1 wfFunRec sK) (ap2 pi (ap1 wfFun Prr) (ap1 wfFunRec d)) htag
                     (addPA htag (wfFunRec_op_rRb_imp sK ne_sK)))
                   (wfFunSK_ctx htag)
      wfPrrO = gPiL htag (ap1 wfFun Prr) (ap1 wfFunRec d) wfFunPiO
      wfFunD = gPiR htag (ap1 wfFun Prr) (ap1 wfFunRec d) wfFunPiO
      h8 = axFst (natCode 8) (funP sK)
      ne8 = pair8NeqO (funP sK)
      nl8 = ruleTrans (congL natEqF (natCode 1) h8) (natEqF_at_neq 8 1 (decideNatNeq 8 1 (\ ())))
      wfROp = wfFun_op_R Prr ne8 nl8 h8
      tail2R = ap2 pi (ap1 wfFun (pL Prr)) (ap1 wfFun (pR Prr))
      tail3R = ap2 pi (ap1 wfFun (dtag Prr)) tail2R
      tail4R = ap2 pi (isF2 (pR Prr)) tail3R
      tail5R = ap2 pi (isF2 (pL Prr)) tail4R
      tail6R = ap2 pi (isF1 (dtag Prr)) tail5R
      pi7R = ap2 pi (ap1 funValidF Prr) tail6R
      pi7RO = trans3c pi7R (ap1 wfFun Prr) O
                (Gsym (ap1 wfFun Prr) pi7R htag (lift3 negLeaf htag PA wfROp)) wfPrrO
      rest6 = gPiR htag (ap1 funValidF Prr) tail6R pi7RO
      isF1dtagO = gPiL htag (isF1 (dtag Prr)) tail5R rest6
      rest5 = gPiR htag (isF1 (dtag Prr)) tail5R rest6
      rest4 = gPiR htag (isF2 (pL Prr)) tail4R rest5
      rest3 = gPiR htag (isF2 (pR Prr)) tail3R rest4
      wfdtagO = gPiL htag (ap1 wfFun (dtag Prr)) tail2R rest3
      sndPrr = axSnd (natCode 8) (funP sK)
      dtagPrr_eq = cong1 Fst sndPrr
      isF1g = ap3c (lift3 negLeaf htag PA (prependEqLeft (isF1 g) (isF1 (dtag Prr)) O (isF1cong g (dtag Prr) (ruleSym dtagPrr_eq)))) isF1dtagO
      fvg = ap3c (lift3 negLeaf htag PA (prependEqLeft (ap1 wfFun g) (ap1 wfFun (dtag Prr)) O (cong1 wfFun (ruleSym dtagPrr_eq)))) wfdtagO
      childCj = mkChildCjFull htag d leqD (mkWfRedFull htag d wfRedD wfFunD)
      cV = ap3c (lift3 negLeaf htag PA (childV_imp d)) childCj
      cS = ap3c (lift3 negLeaf htag PA (childS_imp d)) childCj
      cT = ap3c (lift3 negLeaf htag PA (childT_imp d)) childCj
      cVwfRed = splitL htag X cV
      cVwfFun = splitR htag X cV
      triEq = addPA htag (triF_op_Rb_imp sK ne_sK)
      srcEqSK = addPA htag (srcF_op_rRb_imp sK ne_sK)
      tgtEqSK = addPA htag (tgtF_op_rRb_imp sK ne_sK)
      -- V-fact : wfRedFull (ap1c g X) = O.
      wfRedTriSK = trans3c (ap1 wfRed (ap1 triF sK)) (ap1 wfRed (ap1c g X)) O
                     (Gcong wfRed (ap1 triF sK) (ap1c g X) htag triEq)
                     (trans3c (ap1 wfRed (ap1c g X)) (ap1 wfRed X) O
                       (lift3 negLeaf htag PA (wfRed_ap1c g X)) cVwfRed)
      wfFunTriSK = trans3c (ap1 wfFunRec (ap1 triF sK)) (ap1 wfFunRec (ap1c g X)) O
                     (Gcong wfFunRec (ap1 triF sK) (ap1c g X) htag triEq)
                     (trans3c (ap1 wfFunRec (ap1c g X)) (ap2 pi (isF1 g) (ap2 pi (funValid g) (ap1 wfFunRec X))) O
                       (lift3 negLeaf htag PA (wfFunRec_ap1c g X))
                       (piB htag (isF1 g) (ap2 pi (funValid g) (ap1 wfFunRec X)) isF1g
                         (piB htag (funValid g) (ap1 wfFunRec X) fvg cVwfFun)))
      factV = mkWfRedFull htag (ap1 triF sK) wfRedTriSK wfFunTriSK
      -- S-fact : srcF (ap1c g X) = tmAp1 g (srcF X) = tmAp1 g (tgtF d) = tgtF sK.
      srcTriEq = trans3c (ap1 srcF (ap1 triF sK)) (ap1 srcF (ap1c g X)) (tmAp1 g (ap1 tgtF d))
                   (Gcong srcF (ap1 triF sK) (ap1c g X) htag triEq)
                   (trans3c (ap1 srcF (ap1c g X)) (tmAp1 g (ap1 srcF X)) (tmAp1 g (ap1 tgtF d))
                     (lift3 negLeaf htag PA (srcF_ap1c g X))
                     (GcongTmAp1 g (ap1 srcF X) (ap1 tgtF d) htag cS))
      factS = trans3c (ap1 srcF (ap1 triF sK)) (tmAp1 g (ap1 tgtF d)) (ap1 tgtF sK)
                srcTriEq (Gsym (ap1 tgtF sK) (tmAp1 g (ap1 tgtF d)) htag tgtEqSK)
      -- T-fact : tgtF (ap1c g X) = tmAp1 g (tgtF X) = tmAp1 g Y = devF (srcF sK).
      tgtTriEq = trans3c (ap1 tgtF (ap1 triF sK)) (ap1 tgtF (ap1c g X)) (tmAp1 g Y)
                   (Gcong tgtF (ap1 triF sK) (ap1c g X) htag triEq)
                   (trans3c (ap1 tgtF (ap1c g X)) (tmAp1 g (ap1 tgtF X)) (tmAp1 g Y)
                     (lift3 negLeaf htag PA (tgtF_ap1c g X))
                     (GcongTmAp1 g (ap1 tgtF X) Y htag cT))
      devSrcEq = trans3c (ap1 devF (ap1 srcF sK)) (ap1 devF (tmAp2 cr (ap1 srcF d) tmO)) (tmAp1 g Y)
                   (Gcong devF (ap1 srcF sK) (tmAp2 cr (ap1 srcF d) tmO) htag srcEqSK)
                   (trans3c (ap1 devF (tmAp2 cr (ap1 srcF d) tmO)) (tmAp1 (gF cr) Y) (tmAp1 g Y)
                     (lift3 negLeaf htag PA (devF_ap2_Rb_h cr (ap1 srcF d) (hd_cRec g h1 h2)))
                     (lift3 negLeaf htag PA (tmAp1FunCong (gF cr) g Y (recFun g h1 h2))))
      factT = trans3c (ap1 tgtF (ap1 triF sK)) (tmAp1 g Y) (ap1 devF (ap1 srcF sK))
                tgtTriEq (Gsym (ap1 devF (ap1 srcF sK)) (tmAp1 g Y) htag devSrcEq)
  in assembleConj3 htag factV factS factT

------------------------------------------------------------------------
-- Reconstruction helpers for the compound carried-fun glues (rRs / ap1c-C / ap2c-cRec).

private
  -- imp-form funValid_R : from the SHALLOW self-reassembly check eqDecO f (recon f) = O
  -- and Fst f = natCode 8 conclude f = cRec (cG f)(cH1 f)(cH2 f).
  funValid_R_imp : (f : Term) -> Deriv (eqF (ap1 Fst f) (natCode 8)) ->
    Deriv (imp (eqF (eqDecO f (ap1 recon f)) O) (eqF f (cRec (cG f) (cH1 f) (cH2 f))))
  funValid_R_imp f h8 =
    impEqTrans f (ap1 recon f) (cRec (cG f) (cH1 f) (cH2 f))
      (eqDecO_sound_imp f (ap1 recon f))
      (impLift (recon_R f h8))

  -- bare head-congruence on tmAp2 (rewrite the function head).
  tmAp2HeadImp : (Gh Gh' a b : Term) ->
    Deriv (imp (eqF Gh Gh') (eqF (tmAp2 Gh a b) (tmAp2 Gh' a b)))
  tmAp2HeadImp Gh Gh' a b =
    impCongR Pair (ap2 Pair Gh (ap2 Pair a b)) (ap2 Pair Gh' (ap2 Pair a b)) tgAp2
      (impCongL Pair Gh Gh' (ap2 Pair a b) (identP (eqF Gh Gh')))

  GcongAp2Head : (Gh Gh' a b : Term) (htag : Formula) ->
    Deriv (imp negLeaf (imp htag (imp PA (eqF Gh Gh')))) ->
    Deriv (imp negLeaf (imp htag (imp PA (eqF (tmAp2 Gh a b) (tmAp2 Gh' a b)))))
  GcongAp2Head Gh Gh' a b htag d = ap3c (lift3 negLeaf htag PA (tmAp2HeadImp Gh Gh' a b)) d

  -- bare devF-Rs residual collapse:
  --   devF_ap2_Rs_h output  (with g = cRec g h1 h2)  ==  tmAp2 h1 (tmAp2 h2 DA DB)(tmAp2 (cRec g h1 h2) DA DB).
  congRsDev : (g h1 h2 DA DB : Term) ->
    Deriv (eqF (tmAp2 (h1F (cRec g h1 h2)) (tmAp2 (h2F (cRec g h1 h2)) DA DB)
                       (tmAp2 (cRec (gF (cRec g h1 h2)) (h1F (cRec g h1 h2)) (h2F (cRec g h1 h2))) DA DB))
               (tmAp2 h1 (tmAp2 h2 DA DB) (tmAp2 (cRec g h1 h2) DA DB)))
  congRsDev g h1 h2 DA DB =
    let G = cRec g h1 h2
        cRecHeadEq : Deriv (eqF (cRec (gF G) (h1F G) (h2F G)) (cRec g h1 h2))
        cRecHeadEq = congR Pair (natCode 8)
                       (ruleTrans (congL Pair (ap2 Pair (h1F G) (h2F G)) (recFun g h1 h2))
                         (congR Pair g (ruleTrans (congL Pair (h2F G) (recH1 g h1 h2))
                                          (congR Pair h1 (recH2 g h1 h2)))))
    in tmAp2Cong (h1F G) h1
         (tmAp2 (h2F G) DA DB) (tmAp2 h2 DA DB)
         (tmAp2 (cRec (gF G) (h1F G) (h2F G)) DA DB) (tmAp2 (cRec g h1 h2) DA DB)
         (recH1 g h1 h2)
         (tmAp2Cong (h2F G) h2 DA DA DB DB (recH2 g h1 h2) (axRefl DA) (axRefl DB))
         (tmAp2Cong (cRec (gF G) (h1F G) (h2F G)) (cRec g h1 h2) DA DA DB DB cRecHeadEq (axRefl DA) (axRefl DB))

------------------------------------------------------------------------
-- glue_rRs :  full R-step (derRs).  triF sK = ap2c h1 (ap2c h2 X1 X2)(ap2c (Pair 8 funP) X1 X2),
--   reconstruction Pair 8 funP = cRec g h1 h2 supplied by deep wfFun (FIX(B)).

glue_rRs : Deriv (imp negLeaf (imp (eqF (ap1 Fst (dtag sK)) dgRs) (imp PA Bgoal)))
glue_rRs =
  let htag = eqF (ap1 Fst (dtag sK)) dgRs
      chL = pL sK
      chR = pR sK
      X1 = ap1 triF chL
      X2 = ap1 triF chR
      g  = gP sK
      h1 = h1P sK
      h2 = h2P sK
      Praw = ap2 Pair (natCode 8) (funP sK)
      Rrec = cRec g h1 h2
      M = dAp2c h2 X1 X2
      N = dAp2c Praw X1 X2
      DA = ap1 devF (ap1 srcF chL)
      DB = ap1 devF (ap1 srcF chR)
      leqL = rebound chL (pLValueBound sK ne_sK)
      leqR = rebound chR (pRValueBound sK ne_sK)
      -- child wfRed
      wfRedPiO = trans3c (ap2 pi (ap1 wfRed chL) (ap1 wfRed chR)) (ap1 wfRed sK) O
                   (Gsym (ap1 wfRed sK) (ap2 pi (ap1 wfRed chL) (ap1 wfRed chR)) htag
                      (addPA htag (wfRed_op_rRs_imp sK ne_sK)))
                   (wfRedSK_ctx htag)
      wfRedChLO = ap3c (lift3 negLeaf htag PA (piZeroL_imp (ap1 wfRed chL) (ap1 wfRed chR))) wfRedPiO
      wfRedChRO = ap3c (lift3 negLeaf htag PA (piZeroR_imp (ap1 wfRed chL) (ap1 wfRed chR))) wfRedPiO
      -- child wfFunRec + ap1 wfFun Praw
      wfFunPiO = trans3c (ap2 pi (ap1 wfFun Praw) (ap2 pi (ap1 wfFunRec chL) (ap1 wfFunRec chR))) (ap1 wfFunRec sK) O
                   (Gsym (ap1 wfFunRec sK) (ap2 pi (ap1 wfFun Praw) (ap2 pi (ap1 wfFunRec chL) (ap1 wfFunRec chR))) htag
                      (addPA htag (wfFunRec_op_rRs_imp sK ne_sK)))
                   (wfFunSK_ctx htag)
      wfPrawO = ap3c (lift3 negLeaf htag PA (piZeroL_imp (ap1 wfFun Praw) (ap2 pi (ap1 wfFunRec chL) (ap1 wfFunRec chR)))) wfFunPiO
      wfFunChildren = ap3c (lift3 negLeaf htag PA (piZeroR_imp (ap1 wfFun Praw) (ap2 pi (ap1 wfFunRec chL) (ap1 wfFunRec chR)))) wfFunPiO
      wfFunChLO = ap3c (lift3 negLeaf htag PA (piZeroL_imp (ap1 wfFunRec chL) (ap1 wfFunRec chR))) wfFunChildren
      wfFunChRO = ap3c (lift3 negLeaf htag PA (piZeroR_imp (ap1 wfFunRec chL) (ap1 wfFunRec chR))) wfFunChildren
      childCjL = mkChildCjFull htag chL leqL (mkWfRedFull htag chL wfRedChLO wfFunChLO)
      childCjR = mkChildCjFull htag chR leqR (mkWfRedFull htag chR wfRedChRO wfFunChRO)
      cVL = ap3c (lift3 negLeaf htag PA (childV_imp chL)) childCjL
      cSL = ap3c (lift3 negLeaf htag PA (childS_imp chL)) childCjL
      cTL = ap3c (lift3 negLeaf htag PA (childT_imp chL)) childCjL
      cVR = ap3c (lift3 negLeaf htag PA (childV_imp chR)) childCjR
      cSR = ap3c (lift3 negLeaf htag PA (childS_imp chR)) childCjR
      cTR = ap3c (lift3 negLeaf htag PA (childT_imp chR)) childCjR
      cVLwfRed = splitL htag X1 cVL
      cVLwfFun = splitR htag X1 cVL
      cVRwfRed = splitL htag X2 cVR
      cVRwfFun = splitR htag X2 cVR
      -- deep wfFun extraction on Praw.
      h8 = axFst (natCode 8) (funP sK)
      ne8 = pair8NeqO (funP sK)
      nl8 = ruleTrans (congL natEqF (natCode 1) h8) (natEqF_at_neq 8 1 (decideNatNeq 8 1 (\ ())))
      wfROp = wfFun_op_R Praw ne8 nl8 h8
      tail2 = ap2 pi (ap1 wfFun (pL Praw)) (ap1 wfFun (pR Praw))
      tail3 = ap2 pi (ap1 wfFun (dtag Praw)) tail2
      tail4 = ap2 pi (isF2 (pR Praw)) tail3
      tail5 = ap2 pi (isF2 (pL Praw)) tail4
      tail6 = ap2 pi (isF1 (dtag Praw)) tail5
      pi7 = ap2 pi (ap1 funValidF Praw) tail6
      pi7O = trans3c pi7 (ap1 wfFun Praw) O
               (Gsym (ap1 wfFun Praw) pi7 htag (lift3 negLeaf htag PA wfROp)) wfPrawO
      fvfPrawO = gPiL htag (ap1 funValidF Praw) tail6 pi7O
      rest6 = gPiR htag (ap1 funValidF Praw) tail6 pi7O
      rest5 = gPiR htag (isF1 (dtag Praw)) tail5 rest6
      isF2pLO = gPiL htag (isF2 (pL Praw)) tail4 rest5
      rest4 = gPiR htag (isF2 (pL Praw)) tail4 rest5
      isF2pRO = gPiL htag (isF2 (pR Praw)) tail3 rest4
      rest3 = gPiR htag (isF2 (pR Praw)) tail3 rest4
      rest2 = gPiR htag (ap1 wfFun (dtag Praw)) tail2 rest3
      wfFunPLO = gPiL htag (ap1 wfFun (pL Praw)) (ap1 wfFun (pR Praw)) rest2
      wfFunPRO = gPiR htag (ap1 wfFun (pL Praw)) (ap1 wfFun (pR Praw)) rest2
      sndPraw = axSnd (natCode 8) (funP sK)
      pLPraw_eq = cong1 Fst (cong1 Snd sndPraw)
      pRPraw_eq = cong1 Snd (cong1 Snd sndPraw)
      isF2h1 = ap3c (lift3 negLeaf htag PA (prependEqLeft (isF2 h1) (isF2 (pL Praw)) O (isF2cong h1 (pL Praw) (ruleSym pLPraw_eq)))) isF2pLO
      isF2h2 = ap3c (lift3 negLeaf htag PA (prependEqLeft (isF2 h2) (isF2 (pR Praw)) O (isF2cong h2 (pR Praw) (ruleSym pRPraw_eq)))) isF2pRO
      fvh1 = ap3c (lift3 negLeaf htag PA
               (prependEqLeft (ap1 wfFun h1) (ap1 wfFun (pL Praw)) O (cong1 wfFun (ruleSym pLPraw_eq)))) wfFunPLO
      fvh2 = ap3c (lift3 negLeaf htag PA
               (prependEqLeft (ap1 wfFun h2) (ap1 wfFun (pR Praw)) O (cong1 wfFun (ruleSym pRPraw_eq)))) wfFunPRO
      -- isF2 Praw = O  (Praw = Pair 8 funP, a Fun2 head).
      n8k : (k : Nat) -> ((Eq 8 k) -> Empty) -> Deriv (eqF (ap2 natEqF (ap1 Fst Praw) (natCode k)) O)
      n8k k w = ruleTrans (congL natEqF (natCode k) h8) (natEqF_at_neq 8 k (decideNatNeq 8 k w))
      isF2PrawBare = piBothO (ap2 natEqF (ap1 Fst Praw) (natCode 3))
                       (ap2 pi (ap2 natEqF (ap1 Fst Praw) (natCode 4))
                         (ap2 pi (ap2 natEqF (ap1 Fst Praw) (natCode 5))
                           (ap2 pi (ap2 natEqF (ap1 Fst Praw) (natCode 6)) (ap2 natEqF (ap1 Fst Praw) (natCode 1)))))
                       (n8k 3 (\ ()))
                       (piBothO (ap2 natEqF (ap1 Fst Praw) (natCode 4))
                         (ap2 pi (ap2 natEqF (ap1 Fst Praw) (natCode 5))
                           (ap2 pi (ap2 natEqF (ap1 Fst Praw) (natCode 6)) (ap2 natEqF (ap1 Fst Praw) (natCode 1))))
                         (n8k 4 (\ ()))
                         (piBothO (ap2 natEqF (ap1 Fst Praw) (natCode 5))
                           (ap2 pi (ap2 natEqF (ap1 Fst Praw) (natCode 6)) (ap2 natEqF (ap1 Fst Praw) (natCode 1)))
                           (n8k 5 (\ ()))
                           (piBothO (ap2 natEqF (ap1 Fst Praw) (natCode 6)) (ap2 natEqF (ap1 Fst Praw) (natCode 1))
                             (n8k 6 (\ ())) (n8k 1 (\ ())))))
      isF2Praw = lift3 negLeaf htag PA isF2PrawBare
      -- reconstruction Praw = Rrec.
      shallowO = ap3c (lift3 negLeaf htag PA
                   (prependEqLeft (eqDecO Praw (ap1 recon Praw)) (ap1 funValidF Praw) O
                      (ruleSym (funValidF_eq Praw)))) fvfPrawO
      reconRaw = ap3c (lift3 negLeaf htag PA (funValid_R_imp Praw h8)) shallowO
      cGeq = cong1 Fst sndPraw
      cH1eq = cong1 Fst (cong1 Snd sndPraw)
      cH2eq = cong1 Snd (cong1 Snd sndPraw)
      cRecArgsEq = congR Pair (natCode 8)
                     (ruleTrans (congL Pair (ap2 Pair (cH1 Praw) (cH2 Praw)) cGeq)
                       (congR Pair g (ruleTrans (congL Pair (cH2 Praw) cH1eq)
                                        (congR Pair h1 cH2eq))))
      reconEq = trans3c Praw (cRec (cG Praw) (cH1 Praw) (cH2 Praw)) Rrec
                  reconRaw (lift3 negLeaf htag PA cRecArgsEq)
      -- opaque eqs.
      triEq = addPA htag (triF_op_Rs_imp sK ne_sK)
      srcEqSK = addPA htag (srcF_op_rRs_imp sK ne_sK)
      tgtEqSK = addPA htag (tgtF_op_rRs_imp sK ne_sK)
      -- V-fact.
      wfRedM = trans3c (ap1 wfRed M) (ap2 pi (ap1 wfRed X1) (ap1 wfRed X2)) O
                 (lift3 negLeaf htag PA (wfRed_ap2c h2 X1 X2))
                 (piB htag (ap1 wfRed X1) (ap1 wfRed X2) cVLwfRed cVRwfRed)
      wfRedN = trans3c (ap1 wfRed N) (ap2 pi (ap1 wfRed X1) (ap1 wfRed X2)) O
                 (lift3 negLeaf htag PA (wfRed_ap2c Praw X1 X2))
                 (piB htag (ap1 wfRed X1) (ap1 wfRed X2) cVLwfRed cVRwfRed)
      wfRedTriSK = trans3c (ap1 wfRed (ap1 triF sK)) (ap1 wfRed (dAp2c h1 M N)) O
                     (Gcong wfRed (ap1 triF sK) (dAp2c h1 M N) htag triEq)
                     (trans3c (ap1 wfRed (dAp2c h1 M N)) (ap2 pi (ap1 wfRed M) (ap1 wfRed N)) O
                        (lift3 negLeaf htag PA (wfRed_ap2c h1 M N))
                        (piB htag (ap1 wfRed M) (ap1 wfRed N) wfRedM wfRedN))
      wfFunM = trans3c (ap1 wfFunRec M)
                 (ap2 pi (isF2 h2) (ap2 pi (funValid h2) (ap2 pi (ap1 wfFunRec X1) (ap1 wfFunRec X2)))) O
                 (lift3 negLeaf htag PA (wfFunRec_ap2c h2 X1 X2))
                 (piB htag (isF2 h2) (ap2 pi (funValid h2) (ap2 pi (ap1 wfFunRec X1) (ap1 wfFunRec X2))) isF2h2
                   (piB htag (funValid h2) (ap2 pi (ap1 wfFunRec X1) (ap1 wfFunRec X2)) fvh2
                      (piB htag (ap1 wfFunRec X1) (ap1 wfFunRec X2) cVLwfFun cVRwfFun)))
      wfFunN = trans3c (ap1 wfFunRec N)
                 (ap2 pi (isF2 Praw) (ap2 pi (funValid Praw) (ap2 pi (ap1 wfFunRec X1) (ap1 wfFunRec X2)))) O
                 (lift3 negLeaf htag PA (wfFunRec_ap2c Praw X1 X2))
                 (piB htag (isF2 Praw) (ap2 pi (funValid Praw) (ap2 pi (ap1 wfFunRec X1) (ap1 wfFunRec X2))) isF2Praw
                   (piB htag (funValid Praw) (ap2 pi (ap1 wfFunRec X1) (ap1 wfFunRec X2)) wfPrawO
                      (piB htag (ap1 wfFunRec X1) (ap1 wfFunRec X2) cVLwfFun cVRwfFun)))
      wfFunTriSK = trans3c (ap1 wfFunRec (ap1 triF sK)) (ap1 wfFunRec (dAp2c h1 M N)) O
                     (Gcong wfFunRec (ap1 triF sK) (dAp2c h1 M N) htag triEq)
                     (trans3c (ap1 wfFunRec (dAp2c h1 M N))
                        (ap2 pi (isF2 h1) (ap2 pi (funValid h1) (ap2 pi (ap1 wfFunRec M) (ap1 wfFunRec N)))) O
                        (lift3 negLeaf htag PA (wfFunRec_ap2c h1 M N))
                        (piB htag (isF2 h1) (ap2 pi (funValid h1) (ap2 pi (ap1 wfFunRec M) (ap1 wfFunRec N))) isF2h1
                          (piB htag (funValid h1) (ap2 pi (ap1 wfFunRec M) (ap1 wfFunRec N)) fvh1
                             (piB htag (ap1 wfFunRec M) (ap1 wfFunRec N) wfFunM wfFunN))))
      factV = mkWfRedFull htag (ap1 triF sK) wfRedTriSK wfFunTriSK
      -- S-fact.
      srcMeq = trans3c (ap1 srcF M) (tmAp2 h2 (ap1 srcF X1) (ap1 srcF X2)) (tmAp2 h2 (ap1 tgtF chL) (ap1 tgtF chR))
                 (lift3 negLeaf htag PA (srcF_ap2c h2 X1 X2))
                 (GcongAp2R h2 (ap1 srcF X1) (ap1 tgtF chL) (ap1 srcF X2) (ap1 tgtF chR) htag cSL cSR)
      srcNeq = trans3c (ap1 srcF N) (tmAp2 Praw (ap1 tgtF chL) (ap1 tgtF chR)) (tmAp2 Rrec (ap1 tgtF chL) (ap1 tgtF chR))
                 (trans3c (ap1 srcF N) (tmAp2 Praw (ap1 srcF X1) (ap1 srcF X2)) (tmAp2 Praw (ap1 tgtF chL) (ap1 tgtF chR))
                    (lift3 negLeaf htag PA (srcF_ap2c Praw X1 X2))
                    (GcongAp2R Praw (ap1 srcF X1) (ap1 tgtF chL) (ap1 srcF X2) (ap1 tgtF chR) htag cSL cSR))
                 (GcongAp2Head Praw Rrec (ap1 tgtF chL) (ap1 tgtF chR) htag reconEq)
      srcTriEq = trans3c (ap1 srcF (ap1 triF sK)) (ap1 srcF (dAp2c h1 M N))
                   (tmAp2 h1 (tmAp2 h2 (ap1 tgtF chL) (ap1 tgtF chR)) (tmAp2 Rrec (ap1 tgtF chL) (ap1 tgtF chR)))
                   (Gcong srcF (ap1 triF sK) (dAp2c h1 M N) htag triEq)
                   (trans3c (ap1 srcF (dAp2c h1 M N)) (tmAp2 h1 (ap1 srcF M) (ap1 srcF N))
                      (tmAp2 h1 (tmAp2 h2 (ap1 tgtF chL) (ap1 tgtF chR)) (tmAp2 Rrec (ap1 tgtF chL) (ap1 tgtF chR)))
                      (lift3 negLeaf htag PA (srcF_ap2c h1 M N))
                      (GcongAp2R h1 (ap1 srcF M) (tmAp2 h2 (ap1 tgtF chL) (ap1 tgtF chR))
                                    (ap1 srcF N) (tmAp2 Rrec (ap1 tgtF chL) (ap1 tgtF chR)) htag srcMeq srcNeq))
      factS = trans3c (ap1 srcF (ap1 triF sK))
                (tmAp2 h1 (tmAp2 h2 (ap1 tgtF chL) (ap1 tgtF chR)) (tmAp2 Rrec (ap1 tgtF chL) (ap1 tgtF chR)))
                (ap1 tgtF sK)
                srcTriEq
                (Gsym (ap1 tgtF sK)
                   (tmAp2 h1 (tmAp2 h2 (ap1 tgtF chL) (ap1 tgtF chR)) (tmAp2 Rrec (ap1 tgtF chL) (ap1 tgtF chR)))
                   htag tgtEqSK)
      -- T-fact.
      tgtMeq = trans3c (ap1 tgtF M) (tmAp2 h2 (ap1 tgtF X1) (ap1 tgtF X2)) (tmAp2 h2 DA DB)
                 (lift3 negLeaf htag PA (tgtF_ap2c h2 X1 X2))
                 (GcongAp2R h2 (ap1 tgtF X1) DA (ap1 tgtF X2) DB htag cTL cTR)
      tgtNeq = trans3c (ap1 tgtF N) (tmAp2 Praw DA DB) (tmAp2 Rrec DA DB)
                 (trans3c (ap1 tgtF N) (tmAp2 Praw (ap1 tgtF X1) (ap1 tgtF X2)) (tmAp2 Praw DA DB)
                    (lift3 negLeaf htag PA (tgtF_ap2c Praw X1 X2))
                    (GcongAp2R Praw (ap1 tgtF X1) DA (ap1 tgtF X2) DB htag cTL cTR))
                 (GcongAp2Head Praw Rrec DA DB htag reconEq)
      tgtTriEq = trans3c (ap1 tgtF (ap1 triF sK)) (ap1 tgtF (dAp2c h1 M N))
                   (tmAp2 h1 (tmAp2 h2 DA DB) (tmAp2 Rrec DA DB))
                   (Gcong tgtF (ap1 triF sK) (dAp2c h1 M N) htag triEq)
                   (trans3c (ap1 tgtF (dAp2c h1 M N)) (tmAp2 h1 (ap1 tgtF M) (ap1 tgtF N))
                      (tmAp2 h1 (tmAp2 h2 DA DB) (tmAp2 Rrec DA DB))
                      (lift3 negLeaf htag PA (tgtF_ap2c h1 M N))
                      (GcongAp2R h1 (ap1 tgtF M) (tmAp2 h2 DA DB) (ap1 tgtF N) (tmAp2 Rrec DA DB) htag tgtMeq tgtNeq))
      devSrcEq = trans3c (ap1 devF (ap1 srcF sK))
                   (ap1 devF (tmAp2 Rrec (ap1 srcF chL) (tmAp1 cSuc (ap1 srcF chR))))
                   (tmAp2 h1 (tmAp2 h2 DA DB) (tmAp2 Rrec DA DB))
                   (Gcong devF (ap1 srcF sK) (tmAp2 Rrec (ap1 srcF chL) (tmAp1 cSuc (ap1 srcF chR))) htag srcEqSK)
                   (trans3c (ap1 devF (tmAp2 Rrec (ap1 srcF chL) (tmAp1 cSuc (ap1 srcF chR))))
                      (tmAp2 (h1F Rrec) (tmAp2 (h2F Rrec) DA DB)
                             (tmAp2 (cRec (gF Rrec) (h1F Rrec) (h2F Rrec)) DA DB))
                      (tmAp2 h1 (tmAp2 h2 DA DB) (tmAp2 Rrec DA DB))
                      (lift3 negLeaf htag PA (devF_ap2_Rs_h Rrec (ap1 srcF chL) (ap1 srcF chR) (hd_cRec g h1 h2)))
                      (lift3 negLeaf htag PA (congRsDev g h1 h2 DA DB)))
      factT = trans3c (ap1 tgtF (ap1 triF sK)) (tmAp2 h1 (tmAp2 h2 DA DB) (tmAp2 Rrec DA DB)) (ap1 devF (ap1 srcF sK))
                tgtTriEq
                (Gsym (ap1 devF (ap1 srcF sK)) (tmAp2 h1 (tmAp2 h2 DA DB) (tmAp2 Rrec DA DB)) htag devSrcEq)
  in assembleConj3 htag factV factS factT
