{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.WfRedExtractHtag -- the IMP-FORM child extractions carrying BOTH the tag
-- premise (htag) and the validity premise (A = wfRedSized p = O) as antecedents:
--
--   imp htag (imp (wfRedSized p = O) (wfRedSized child = O))
--
-- needed by the object tag dispatch, where caseElim exposes  dtag p = dgK  as a
-- hypothesis.  Same opaque harness + lookup as T4.WfRedExtract(Imp), but the
-- wfStep cascade fires are the imp-form ones (T4.ForkImp) and the validity is
-- threaded in the depth-2 context [htag, A] (T4.CtxKit).
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.WfRedExtractHtag where

open import T4.Base

open import T4.DerCodeS using ( dtag ; pArg ; pL ; pR )
open import T4.DerCode  using ( dgSu ; dgAd ; dgRO ; dgRS )
open import T4.WfRedSized
  using ( wfRedSized ; wfStep ; unaryCell ; binaryCell ; chkU ; chkB ; argIdx
        ; wfRestSu ; wfRestAd ; wfRestRO ; wfRestRS ; w10 ; w20 ; w30 ; w40 )
open import T4.WfRedExtract
  using ( opkg ; opUnfold ; op_nIdx ; op_argIdx ; op_pL ; op_pR
        ; argValueBound ; pLValueBound ; pRValueBound )
open import T4.OpaqueLookup using ( lookup_op )
open import T4.FoldRec using ( lookupAt )
open import T4.BinTree using ( nIdx ; lIdx ; rIdx )

open import T4.DerSrc using ( testEq ; w21 ; w31 ; w32 ; w41 ; w42 ; w43 )
open import T4.ForkImp
  using ( testEq_fire_imp ; testEq_skip_imp
        ; fork_true_to_fst_imp ; fork_false_to_snd_imp )
open import T4.CtxKit
  using ( lift2 ; get2b ; ap2c ; trans2c )

open import BRA3.Church      using ( sigma ; predecessor )
open import T4.SigmaZeroN    using ( sigmaZeroL ; sigmaZeroR )
open import BRA3.Logic       using ( prependEqLeft ; eqSymImp )
open import BRA3.Contrapositive using ( compI )
open import T4.Thm12.ImpHelpers using ( impLift ; impEqTrans )

------------------------------------------------------------------------
-- The recovered-label premise, carried under htag = (dtag p = dgK).

private
  nieqH : (p : Term) -> Deriv (neg (eqF p O)) -> (dgK : Term) ->
    Deriv (imp (eqF (dtag p) dgK) (eqF (ap1 nIdx (opkg p)) dgK))
  nieqH p ne dgK = prependEqLeft (ap1 nIdx (opkg p)) (dtag p) dgK (op_nIdx p ne)

------------------------------------------------------------------------
-- Unary cell child extraction (imp-form over [htag, A]), given the cascade.

private
  childU_H : (p : Term) (H : Formula) -> Deriv (neg (eqF p O)) ->
    Deriv (imp H (eqF (ap1 wfStep (opkg p)) (ap1 unaryCell (opkg p)))) ->
    Deriv (imp H (imp (eqF (ap1 wfRedSized p) O) (eqF (ap1 wfRedSized (pArg p)) O)))
  childU_H p H ne cfH =
    let opk : Term
        opk = opkg p
        A : Formula
        A = eqF (ap1 wfRedSized p) O
        lookupT : Term
        lookupT = ap1 (lookupAt argIdx) opk
        sigT : Term
        sigT = ap2 sigma (ap1 chkU opk) lookupT
        UE : Deriv (imp H (eqF (ap1 wfRedSized p) sigT))
        UE = impEqTrans (ap1 wfRedSized p) (ap1 wfStep opk) sigT
               (impLift {H} (opUnfold p ne))
               (impEqTrans (ap1 wfStep opk) (ap1 unaryCell opk) sigT
                 cfH (impLift {H} (ax_C sigma chkU (lookupAt argIdx) opk)))
        UE2 : Deriv (imp H (imp A (eqF (ap1 wfRedSized p) sigT)))
        UE2 = compI UE (axK (eqF (ap1 wfRedSized p) sigT) A)
        UE2flip : Deriv (imp H (imp A (eqF sigT (ap1 wfRedSized p))))
        UE2flip = ap2c (lift2 H A (eqSymImp (ap1 wfRedSized p) sigT)) UE2
        sig0 : Deriv (imp H (imp A (eqF sigT O)))
        sig0 = trans2c sigT (ap1 wfRedSized p) O UE2flip (get2b H A)
        lookupO : Deriv (imp H (imp A (eqF lookupT O)))
        lookupO = ap2c (lift2 H A (sigmaZeroR (ap1 chkU opk) lookupT)) sig0
        recArg : Deriv (eqF lookupT (ap1 wfRedSized (pArg p)))
        recArg = lookup_op Z wfStep argIdx (ap1 predecessor p) (pArg p)
                   (op_argIdx p ne) (argValueBound p ne)
    in trans2c (ap1 wfRedSized (pArg p)) lookupT O
         (lift2 H A (ruleSym recArg)) lookupO

  -- inner sigma for a binary cell, over [htag, A].
  binInnerSig_H : (p : Term) (H : Formula) -> Deriv (neg (eqF p O)) ->
    Deriv (imp H (eqF (ap1 wfStep (opkg p)) (ap1 binaryCell (opkg p)))) ->
    Deriv (imp H (imp (eqF (ap1 wfRedSized p) O)
                      (eqF (ap2 sigma (ap1 (lookupAt lIdx) (opkg p))
                                      (ap1 (lookupAt rIdx) (opkg p))) O)))
  binInnerSig_H p H ne cfH =
    let opk : Term
        opk = opkg p
        A : Formula
        A = eqF (ap1 wfRedSized p) O
        innerT : Term
        innerT = ap1 (C sigma (lookupAt lIdx) (lookupAt rIdx)) opk
        sigLR : Term
        sigLR = ap2 sigma (ap1 (lookupAt lIdx) opk) (ap1 (lookupAt rIdx) opk)
        sigT : Term
        sigT = ap2 sigma (ap1 chkB opk) innerT
        UE : Deriv (imp H (eqF (ap1 wfRedSized p) sigT))
        UE = impEqTrans (ap1 wfRedSized p) (ap1 wfStep opk) sigT
               (impLift {H} (opUnfold p ne))
               (impEqTrans (ap1 wfStep opk) (ap1 binaryCell opk) sigT
                 cfH (impLift {H} (ax_C sigma chkB (C sigma (lookupAt lIdx) (lookupAt rIdx)) opk)))
        UE2 : Deriv (imp H (imp A (eqF (ap1 wfRedSized p) sigT)))
        UE2 = compI UE (axK (eqF (ap1 wfRedSized p) sigT) A)
        UE2flip : Deriv (imp H (imp A (eqF sigT (ap1 wfRedSized p))))
        UE2flip = ap2c (lift2 H A (eqSymImp (ap1 wfRedSized p) sigT)) UE2
        sig0 : Deriv (imp H (imp A (eqF sigT O)))
        sig0 = trans2c sigT (ap1 wfRedSized p) O UE2flip (get2b H A)
        innerO : Deriv (imp H (imp A (eqF innerT O)))
        innerO = ap2c (lift2 H A (sigmaZeroR (ap1 chkB opk) innerT)) sig0
    in trans2c sigLR innerT O
         (lift2 H A (ruleSym (ax_C sigma (lookupAt lIdx) (lookupAt rIdx) opk))) innerO

  binChildL_H : (p : Term) (H : Formula) -> Deriv (neg (eqF p O)) ->
    Deriv (imp H (eqF (ap1 wfStep (opkg p)) (ap1 binaryCell (opkg p)))) ->
    Deriv (imp H (imp (eqF (ap1 wfRedSized p) O) (eqF (ap1 wfRedSized (pL p)) O)))
  binChildL_H p H ne cfH =
    let opk : Term
        opk = opkg p
        A : Formula
        A = eqF (ap1 wfRedSized p) O
        lookupL : Term
        lookupL = ap1 (lookupAt lIdx) opk
        eL : Deriv (imp H (imp A (eqF lookupL O)))
        eL = ap2c (lift2 H A (sigmaZeroL lookupL (ap1 (lookupAt rIdx) opk)))
               (binInnerSig_H p H ne cfH)
        recL : Deriv (eqF lookupL (ap1 wfRedSized (pL p)))
        recL = lookup_op Z wfStep lIdx (ap1 predecessor p) (pL p)
                 (op_pL p ne) (pLValueBound p ne)
    in trans2c (ap1 wfRedSized (pL p)) lookupL O (lift2 H A (ruleSym recL)) eL

  binChildR_H : (p : Term) (H : Formula) -> Deriv (neg (eqF p O)) ->
    Deriv (imp H (eqF (ap1 wfStep (opkg p)) (ap1 binaryCell (opkg p)))) ->
    Deriv (imp H (imp (eqF (ap1 wfRedSized p) O) (eqF (ap1 wfRedSized (pR p)) O)))
  binChildR_H p H ne cfH =
    let opk : Term
        opk = opkg p
        A : Formula
        A = eqF (ap1 wfRedSized p) O
        lookupR : Term
        lookupR = ap1 (lookupAt rIdx) opk
        eR : Deriv (imp H (imp A (eqF lookupR O)))
        eR = ap2c (lift2 H A (sigmaZeroR (ap1 (lookupAt lIdx) opk) lookupR))
               (binInnerSig_H p H ne cfH)
        recR : Deriv (eqF lookupR (ap1 wfRedSized (pR p)))
        recR = lookup_op Z wfStep rIdx (ap1 predecessor p) (pR p)
                 (op_pR p ne) (pRValueBound p ne)
    in trans2c (ap1 wfRedSized (pR p)) lookupR O (lift2 H A (ruleSym recR)) eR

------------------------------------------------------------------------
-- The tag-keyed cascades (imp-form over htag) and the extractions.

private
  cascadeSu_H : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (imp (eqF (dtag p) dgSu) (eqF (ap1 wfStep (opkg p)) (ap1 unaryCell (opkg p))))
  cascadeSu_H p ne =
    let H : Formula
        H = eqF (dtag p) dgSu
        opk : Term
        opk = opkg p
        nieq : Deriv (imp H (eqF (ap1 nIdx opk) dgSu))
        nieq = nieqH p ne dgSu
    in impEqTrans (ap1 wfStep opk) (ap1 wfRestSu opk) (ap1 unaryCell opk)
         (fork_false_to_snd_imp H Z wfRestSu (testEq 0) opk (testEq_skip_imp H 1 0 opk w10 nieq))
         (fork_true_to_fst_imp H unaryCell wfRestAd (testEq 1) opk (testEq_fire_imp H 1 opk nieq))

  cascadeRO_H : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (imp (eqF (dtag p) dgRO) (eqF (ap1 wfStep (opkg p)) (ap1 unaryCell (opkg p))))
  cascadeRO_H p ne =
    let H : Formula
        H = eqF (dtag p) dgRO
        opk : Term
        opk = opkg p
        nieq : Deriv (imp H (eqF (ap1 nIdx opk) dgRO))
        nieq = nieqH p ne dgRO
    in impEqTrans (ap1 wfStep opk) (ap1 wfRestSu opk) (ap1 unaryCell opk)
         (fork_false_to_snd_imp H Z wfRestSu (testEq 0) opk (testEq_skip_imp H 3 0 opk w30 nieq))
         (impEqTrans (ap1 wfRestSu opk) (ap1 wfRestAd opk) (ap1 unaryCell opk)
           (fork_false_to_snd_imp H unaryCell wfRestAd (testEq 1) opk (testEq_skip_imp H 3 1 opk w31 nieq))
           (impEqTrans (ap1 wfRestAd opk) (ap1 wfRestRO opk) (ap1 unaryCell opk)
             (fork_false_to_snd_imp H binaryCell wfRestRO (testEq 2) opk (testEq_skip_imp H 3 2 opk w32 nieq))
             (fork_true_to_fst_imp H unaryCell wfRestRS (testEq 3) opk (testEq_fire_imp H 3 opk nieq))))

  cascadeAd_H : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (imp (eqF (dtag p) dgAd) (eqF (ap1 wfStep (opkg p)) (ap1 binaryCell (opkg p))))
  cascadeAd_H p ne =
    let H : Formula
        H = eqF (dtag p) dgAd
        opk : Term
        opk = opkg p
        nieq : Deriv (imp H (eqF (ap1 nIdx opk) dgAd))
        nieq = nieqH p ne dgAd
    in impEqTrans (ap1 wfStep opk) (ap1 wfRestSu opk) (ap1 binaryCell opk)
         (fork_false_to_snd_imp H Z wfRestSu (testEq 0) opk (testEq_skip_imp H 2 0 opk w20 nieq))
         (impEqTrans (ap1 wfRestSu opk) (ap1 wfRestAd opk) (ap1 binaryCell opk)
           (fork_false_to_snd_imp H unaryCell wfRestAd (testEq 1) opk (testEq_skip_imp H 2 1 opk w21 nieq))
           (fork_true_to_fst_imp H binaryCell wfRestRO (testEq 2) opk (testEq_fire_imp H 2 opk nieq)))

  cascadeRS_H : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (imp (eqF (dtag p) dgRS) (eqF (ap1 wfStep (opkg p)) (ap1 binaryCell (opkg p))))
  cascadeRS_H p ne =
    let H : Formula
        H = eqF (dtag p) dgRS
        opk : Term
        opk = opkg p
        nieq : Deriv (imp H (eqF (ap1 nIdx opk) dgRS))
        nieq = nieqH p ne dgRS
    in impEqTrans (ap1 wfStep opk) (ap1 wfRestSu opk) (ap1 binaryCell opk)
         (fork_false_to_snd_imp H Z wfRestSu (testEq 0) opk (testEq_skip_imp H 4 0 opk w40 nieq))
         (impEqTrans (ap1 wfRestSu opk) (ap1 wfRestAd opk) (ap1 binaryCell opk)
           (fork_false_to_snd_imp H unaryCell wfRestAd (testEq 1) opk (testEq_skip_imp H 4 1 opk w41 nieq))
           (impEqTrans (ap1 wfRestAd opk) (ap1 wfRestRO opk) (ap1 binaryCell opk)
             (fork_false_to_snd_imp H binaryCell wfRestRO (testEq 2) opk (testEq_skip_imp H 4 2 opk w42 nieq))
             (impEqTrans (ap1 wfRestRO opk) (ap1 wfRestRS opk) (ap1 binaryCell opk)
               (fork_false_to_snd_imp H unaryCell wfRestRS (testEq 3) opk (testEq_skip_imp H 4 3 opk w43 nieq))
               (fork_true_to_fst_imp H binaryCell (constN 1) (testEq 4) opk (testEq_fire_imp H 4 opk nieq)))))

------------------------------------------------------------------------
-- Public extractions:  imp htag (imp A (wfRedSized child = O)) .

extractChild_Su_H : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (eqF (dtag p) dgSu)
             (imp (eqF (ap1 wfRedSized p) O) (eqF (ap1 wfRedSized (pArg p)) O)))
extractChild_Su_H p ne = childU_H p (eqF (dtag p) dgSu) ne (cascadeSu_H p ne)

extractChild_RO_H : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (eqF (dtag p) dgRO)
             (imp (eqF (ap1 wfRedSized p) O) (eqF (ap1 wfRedSized (pArg p)) O)))
extractChild_RO_H p ne = childU_H p (eqF (dtag p) dgRO) ne (cascadeRO_H p ne)

extractChild_Ad_L_H : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (eqF (dtag p) dgAd)
             (imp (eqF (ap1 wfRedSized p) O) (eqF (ap1 wfRedSized (pL p)) O)))
extractChild_Ad_L_H p ne = binChildL_H p (eqF (dtag p) dgAd) ne (cascadeAd_H p ne)

extractChild_Ad_R_H : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (eqF (dtag p) dgAd)
             (imp (eqF (ap1 wfRedSized p) O) (eqF (ap1 wfRedSized (pR p)) O)))
extractChild_Ad_R_H p ne = binChildR_H p (eqF (dtag p) dgAd) ne (cascadeAd_H p ne)

extractChild_RS_L_H : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (eqF (dtag p) dgRS)
             (imp (eqF (ap1 wfRedSized p) O) (eqF (ap1 wfRedSized (pL p)) O)))
extractChild_RS_L_H p ne = binChildL_H p (eqF (dtag p) dgRS) ne (cascadeRS_H p ne)

extractChild_RS_R_H : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (eqF (dtag p) dgRS)
             (imp (eqF (ap1 wfRedSized p) O) (eqF (ap1 wfRedSized (pR p)) O)))
extractChild_RS_R_H p ne = binChildR_H p (eqF (dtag p) dgRS) ne (cascadeRS_H p ne)
