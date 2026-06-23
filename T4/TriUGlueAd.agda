{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.TriUGlueAd -- the Ad-tag GLUE of the unsized bundled CR dispatch:
--   glue_Ad : imp negLeaf (imp (dtag sK = dgAd) (imp PA Bgoal))
-- a sub-dispatch on the LEFT child  pL sK  (leaf / Su / else), the else case
-- further 3-way on the left tag {Ad,RO,RS} (so srcF (pL sK) is ad#-headed and
-- devF_ad_ad applies for the target endpoint), with the junk-tag reject closed by
-- validity (wfRed (pL sK) = O  +  wfRed O = s O  =>  pL sK is well-tagged).
-- Mirrors T4.DerTriPres src_tri / tgt_tri  mAd  clauses, built over one Cnj
-- context (T4.GammaCtx) and assembled with the imp-form helpers (T4.CRGlueImpU).
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.TriUGlueAd where

open import T4.Base

open import T4.DerCode using ( derZe ; derSu ; derAd ; derRO ; derRS ; dgZe ; dgSu ; dgAd ; dgRO ; dgRS )
open import T4.DerCodeS using ( dtag ; pL ; pR )
open import T4.WfRed using ( wfRed )
  renaming ( wfRed_derRO to wfRedDRO ; wfRed_derAd to wfRedDAd ; wfRed_derSu to wfRedDSu
           ; wfRed_derRS to wfRedDRS )
open import T4.DerTri using ( triF )
open import T4.DerSrc using ( srcF )
  renaming ( srcF_derRO to srcFDRO ; srcF_derAd to srcFDAd ; srcF_derRS to srcFDRS )
open import T4.DerTgt using ( tgtF )
  renaming ( tgtF_derRO to tgtFDRO ; tgtF_derAd to tgtFDAd ; tgtF_derRS to tgtFDRS )
open import T4.DerDev using ( devF ; devF_ad_ze ; devF_ad_su ; devF_ad_ad )
open import T4.QCheckU using ( conj3 ; qcheckU )
open import T4.QCheckProjU using ( PhiKU ; QofChildU )
open import T4.CRGlueU using ( conj3_unfold )
open import T4.CRGlueImpU
  using ( childV_imp ; childS_imp ; childT_imp ; eqDecO_complete_imp
        ; sigmaBothO_imp ; piBothO_imp ; piZeroL_imp ; piZeroR_imp )
open import T4.EqDecO using ( eqDecO )

open import T4.DerTriUOpaqueImp using ( triF_op_Ze_imp )
open import T4.DerTriUOpaqueAdImp using ( triF_op_Ad_Ze_imp ; triF_op_Ad_Su_imp ; triF_op_Ad_else_imp )
open import T4.DerSrcUOpaqueImp using ( srcF_op_Ad_imp )
open import T4.DerTgtUOpaqueImp using ( tgtF_op_Ad_imp )
open import T4.WfRedUOpaqueImp using ( wfRed_op_Ad_imp )
open import T4.WfRedUOpaque using () renaming ( wfRed_O to wfRedO )
open import T4.DerUOpaqueGam
  using ( srcF_op_Ze_gam ; tgtF_op_Ze_gam ; srcF_op_Su_gam ; tgtF_op_Su_gam ; wfRed_op_Su_gam
        ; srcF_op_Ad_gam ; srcF_op_RO_gam ; srcF_op_RS_gam ; wfRed_op_reject_gam
        ; neLeaf_imp ; neTag_imp )
open import BRA3.ChurchCM using ( caseElim )
open import T4.CountingObj using ( swapImp )

open import T4.SndDescent using ( sndLe )
open import T4.LeqMono using ( leq_trans )
open import T4.DescSndImp using ( neSucc )

open import T4.TriUGlue using ( sK ; bigK ; PA ; Bgoal ; negLeaf ; ne_sK ; pa2a ; pa2phik ; rebound )

open import T4.WfRedExtract using ( pLValueBound ; pRValueBound )
open import T4.TauRowBase using ( fstLe )
open import T4.NatEqReflect using ( natEqF_complete )
open import T4.TrsCodeObj using ( ze# ; su# ; ad# )

open import BRA3.Church using ( pi ; sigma )
open import BRA3.SubT.NatEq using ( natEqF )
open import BRA3.ChurchLeq using ( leq )
open import BRA3.Logic using ( eqSymImp )
open import BRA3.Contrapositive using ( compI ; liftP ; identP ; axExFalso )
open import T4.Counting using ( impFalseToNeg_imp )
open import T4.Code using ( falseF )
open import T4.Thm12.ImpHelpers using ( impCong1 ; impCongL ; impCongR ; impEqTrans )
open import T4.TrsCodeObj using ( tagAd ; tagSu )
open import T4.GammaCtx
  using ( Cnj ; cnjL ; cnjR ; cnjPair ; cnjUncurry ; cnjCurry ; gWeak ; gMp ; gApply ; gTrans ; gCong )

------------------------------------------------------------------------
-- Shorthands.

htagA : Formula
htagA = eqF (dtag sK) dgAd

cL : Term
cL = pL sK
cR : Term
cR = pR sK

leqL : Deriv (leq cL (var 0))
leqL = rebound cL (pLValueBound sK ne_sK)
leqR : Deriv (leq cR (var 0))
leqR = rebound cR (pRValueBound sK ne_sK)

-- The base context  Gam0 = ((negLeaf /\ htagA) /\ PA) .
Gam0 : Formula
Gam0 = Cnj (Cnj negLeaf htagA) PA

------------------------------------------------------------------------
-- A sub-case context  Gam = Gam0 /\ cond  with all projections + the conj3
-- assembly + child facts.

module Sub (cond : Formula) where
  Gam : Formula
  Gam = Cnj Gam0 cond

  p0 : Deriv (imp Gam Gam0)
  p0 = cnjL Gam0 cond
  pCond : Deriv (imp Gam cond)
  pCond = cnjR Gam0 cond
  pNH : Deriv (imp Gam (Cnj negLeaf htagA))
  pNH = compI p0 (cnjL (Cnj negLeaf htagA) PA)
  pPA : Deriv (imp Gam PA)
  pPA = compI p0 (cnjR (Cnj negLeaf htagA) PA)
  pNegLeaf : Deriv (imp Gam negLeaf)
  pNegLeaf = compI pNH (cnjL negLeaf htagA)
  pHtag : Deriv (imp Gam htagA)
  pHtag = compI pNH (cnjR negLeaf htagA)
  gPhiK : Deriv (imp Gam PhiKU)
  gPhiK = compI pPA pa2phik
  gA : Deriv (imp Gam (eqF (ap1 wfRed sK) O))
  gA = compI pPA pa2a

  -- the outer Ad validity unfold, under Gam.
  gWfEq : Deriv (imp Gam (eqF (ap1 wfRed sK) (ap2 pi (ap1 wfRed cL) (ap1 wfRed cR))))
  gWfEq = gApply (cnjUncurry (wfRed_op_Ad_imp sK ne_sK)) pNH
  gPiO : Deriv (imp Gam (eqF (ap2 pi (ap1 wfRed cL) (ap1 wfRed cR)) O))
  gPiO = gTrans (ap2 pi (ap1 wfRed cL) (ap1 wfRed cR)) (ap1 wfRed sK) O
           (gApply (eqSymImp (ap1 wfRed sK) (ap2 pi (ap1 wfRed cL) (ap1 wfRed cR))) gWfEq) gA
  gWfL : Deriv (imp Gam (eqF (ap1 wfRed cL) O))
  gWfL = gApply (piZeroL_imp (ap1 wfRed cL) (ap1 wfRed cR)) gPiO
  gWfR : Deriv (imp Gam (eqF (ap1 wfRed cR) O))
  gWfR = gApply (piZeroR_imp (ap1 wfRed cL) (ap1 wfRed cR)) gPiO

  -- conj3 of a child  c  (<= var 0) given its validity, via the IH.
  childCj : (c : Term) -> Deriv (leq c (var 0)) ->
    Deriv (imp Gam (eqF (ap1 wfRed c) O)) -> Deriv (imp Gam (eqF (ap1 conj3 c) O))
  childCj c leqc gWfc = gMp (gApply (QofChildU c leqc) gPhiK) gWfc

  -- ne from validity:  wfRed c = O  /\  wfRed O = s O  =>  c /= O .
  neFromWf : (c : Term) -> Deriv (imp Gam (eqF (ap1 wfRed c) O)) -> Deriv (imp Gam (neg (eqF c O)))
  neFromWf c gWfc =
    let G2 : Formula
        G2 = Cnj Gam (eqF c O)
        f1 : Deriv (imp G2 (eqF (ap1 wfRed c) O))
        f1 = compI (cnjL Gam (eqF c O)) gWfc
        fcO : Deriv (imp G2 (eqF c O))
        fcO = cnjR Gam (eqF c O)
        f3 : Deriv (imp G2 (eqF (ap1 wfRed c) (ap1 wfRed O)))
        f3 = gCong wfRed c O fcO
        f4 : Deriv (imp G2 (eqF (ap1 wfRed c) (ap1 s O)))
        f4 = gTrans (ap1 wfRed c) (ap1 wfRed O) (ap1 s O) f3 (gWeak G2 wfRedO)
        f5 : Deriv (imp G2 (eqF (ap1 s O) O))
        f5 = gTrans (ap1 s O) (ap1 wfRed c) O
               (gApply (eqSymImp (ap1 wfRed c) (ap1 s O)) f4) f1
        f6 : Deriv (imp G2 falseF)
        f6 = gApply (eqSymImp (ap1 s O) O) f5
    in gApply (impFalseToNeg_imp (eqF c O)) (cnjCurry f6)

  -- assemble  conj3 sK = O  from the three facts, under Gam.
  assembleG :
    Deriv (imp Gam (eqF (ap1 wfRed (ap1 triF sK)) O)) ->
    Deriv (imp Gam (eqF (ap1 srcF (ap1 triF sK)) (ap1 tgtF sK))) ->
    Deriv (imp Gam (eqF (ap1 tgtF (ap1 triF sK)) (ap1 devF (ap1 srcF sK)))) ->
    Deriv (imp Gam Bgoal)
  assembleG factV factS factT =
    let eqS : Term
        eqS = eqDecO (ap1 srcF (ap1 triF sK)) (ap1 tgtF sK)
        eqT : Term
        eqT = eqDecO (ap1 tgtF (ap1 triF sK)) (ap1 devF (ap1 srcF sK))
        sO : Deriv (imp Gam (eqF eqS O))
        sO = gApply (eqDecO_complete_imp (ap1 srcF (ap1 triF sK)) (ap1 tgtF sK)) factS
        tO : Deriv (imp Gam (eqF eqT O))
        tO = gApply (eqDecO_complete_imp (ap1 tgtF (ap1 triF sK)) (ap1 devF (ap1 srcF sK))) factT
        innerSig : Deriv (imp Gam (eqF (ap2 sigma eqS eqT) O))
        innerSig = gMp (gApply (sigmaBothO_imp eqS eqT) sO) tO
        outerSig : Deriv (imp Gam (eqF (ap2 sigma (ap1 wfRed (ap1 triF sK)) (ap2 sigma eqS eqT)) O))
        outerSig = gMp (gApply (sigmaBothO_imp (ap1 wfRed (ap1 triF sK)) (ap2 sigma eqS eqT)) factV)
                       innerSig
    in gTrans (ap1 conj3 sK) (ap2 sigma (ap1 wfRed (ap1 triF sK)) (ap2 sigma eqS eqT)) O
         (gWeak Gam (conj3_unfold sK)) outerSig

  -- the outer Ad src / tgt equations under Gam (ne_sK bare).
  gSrcSK : Deriv (imp Gam (eqF (ap1 srcF sK) (ad# (ap1 srcF cL) (ap1 srcF cR))))
  gSrcSK = gApply (cnjUncurry (srcF_op_Ad_imp sK ne_sK)) pNH
  gTgtSK : Deriv (imp Gam (eqF (ap1 tgtF sK) (ad# (ap1 tgtF cL) (ap1 tgtF cR))))
  gTgtSK = gApply (cnjUncurry (tgtF_op_Ad_imp sK ne_sK)) pNH

  -- ad# congruences:  ad# A B = pi tagAd (pi A B) .
  gAdR2 : (z a b : Term) -> Deriv (imp Gam (eqF a b)) ->
    Deriv (imp Gam (eqF (ad# z a) (ad# z b)))
  gAdR2 z a b d =
    impCongR pi (ap2 pi z a) (ap2 pi z b) tagAd (impCongR pi a b z d)
  gAdL2 : (a b z : Term) -> Deriv (imp Gam (eqF a b)) ->
    Deriv (imp Gam (eqF (ad# a z) (ad# b z)))
  gAdL2 a b z d =
    impCongR pi (ap2 pi a z) (ap2 pi b z) tagAd (impCongL pi a b z d)
  -- ad# congruence on BOTH args.
  gAdR2x : (a a' b b' : Term) -> Deriv (imp Gam (eqF a a')) -> Deriv (imp Gam (eqF b b')) ->
    Deriv (imp Gam (eqF (ad# a b) (ad# a' b')))
  gAdR2x a a' b b' da db =
    gTrans (ad# a b) (ad# a' b) (ad# a' b') (gAdL2 a a' b da) (gAdR2 a' b b' db)
  -- su# congruence:  su# A = Pair tagSu A .
  gSu : (a b : Term) -> Deriv (imp Gam (eqF a b)) -> Deriv (imp Gam (eqF (su# a) (su# b)))
  gSu a b d = impCongR Pair a b tagSu d

  -- project  (negLeaf /\ htagA) /\ X  from Gam , given  imp Gam X .
  projNHX : (X : Formula) -> Deriv (imp Gam X) ->
    Deriv (imp Gam (Cnj (Cnj negLeaf htagA) X))
  projNHX X gX = gMp (gApply (cnjPair (Cnj negLeaf htagA) X) pNH) gX

------------------------------------------------------------------------
-- Ad_Ze :  left child a leaf  =>  triF sK = derRO (triF cR) .

LL : Formula
LL = eqF (ap1 Fst cL) (natCode 1)

glueAdZe : Deriv (imp (Cnj Gam0 LL) Bgoal)
glueAdZe =
  let open Sub LL
      cjR : Deriv (imp Gam (eqF (ap1 conj3 cR) O))
      cjR = childCj cR leqR gWfR
      cVR = gApply (childV_imp cR) cjR
      cSR = gApply (childS_imp cR) cjR
      cTR = gApply (childT_imp cR) cjR
      gNeL : Deriv (imp Gam (neg (eqF cL O)))
      gNeL = compI pCond (neLeaf_imp cL)
      gSrcL : Deriv (imp Gam (eqF (ap1 srcF cL) ze#))
      gSrcL = srcF_op_Ze_gam Gam cL gNeL pCond
      gTgtL : Deriv (imp Gam (eqF (ap1 tgtF cL) ze#))
      gTgtL = tgtF_op_Ze_gam Gam cL gNeL pCond
      triEq : Deriv (imp Gam (eqF (ap1 triF sK) (derRO (ap1 triF cR))))
      triEq = gApply (cnjUncurry (cnjUncurry (triF_op_Ad_Ze_imp sK ne_sK))) (projNHX LL pCond)
      factV : Deriv (imp Gam (eqF (ap1 wfRed (ap1 triF sK)) O))
      factV = gTrans (ap1 wfRed (ap1 triF sK)) (ap1 wfRed (ap1 triF cR)) O
                (gTrans (ap1 wfRed (ap1 triF sK)) (ap1 wfRed (derRO (ap1 triF cR))) (ap1 wfRed (ap1 triF cR))
                   (gCong wfRed (ap1 triF sK) (derRO (ap1 triF cR)) triEq)
                   (gWeak Gam (wfRedDRO (ap1 triF cR))))
                cVR
      factS : Deriv (imp Gam (eqF (ap1 srcF (ap1 triF sK)) (ap1 tgtF sK)))
      factS =
        let lhs : Deriv (imp Gam (eqF (ap1 srcF (ap1 triF sK)) (ad# ze# (ap1 tgtF cR))))
            lhs = gTrans (ap1 srcF (ap1 triF sK)) (ad# ze# (ap1 srcF (ap1 triF cR))) (ad# ze# (ap1 tgtF cR))
                    (gTrans (ap1 srcF (ap1 triF sK)) (ap1 srcF (derRO (ap1 triF cR))) (ad# ze# (ap1 srcF (ap1 triF cR)))
                       (gCong srcF (ap1 triF sK) (derRO (ap1 triF cR)) triEq)
                       (gWeak Gam (srcFDRO (ap1 triF cR))))
                    (gAdR2 ze# (ap1 srcF (ap1 triF cR)) (ap1 tgtF cR) cSR)
            rhs : Deriv (imp Gam (eqF (ap1 tgtF sK) (ad# ze# (ap1 tgtF cR))))
            rhs = gTrans (ap1 tgtF sK) (ad# (ap1 tgtF cL) (ap1 tgtF cR)) (ad# ze# (ap1 tgtF cR))
                    gTgtSK (gAdL2 (ap1 tgtF cL) ze# (ap1 tgtF cR) gTgtL)
        in gTrans (ap1 srcF (ap1 triF sK)) (ad# ze# (ap1 tgtF cR)) (ap1 tgtF sK)
             lhs (gApply (eqSymImp (ap1 tgtF sK) (ad# ze# (ap1 tgtF cR))) rhs)
      factT : Deriv (imp Gam (eqF (ap1 tgtF (ap1 triF sK)) (ap1 devF (ap1 srcF sK))))
      factT =
        let lhs : Deriv (imp Gam (eqF (ap1 tgtF (ap1 triF sK)) (ap1 devF (ap1 srcF cR))))
            lhs = gTrans (ap1 tgtF (ap1 triF sK)) (ap1 tgtF (ap1 triF cR)) (ap1 devF (ap1 srcF cR))
                    (gTrans (ap1 tgtF (ap1 triF sK)) (ap1 tgtF (derRO (ap1 triF cR))) (ap1 tgtF (ap1 triF cR))
                       (gCong tgtF (ap1 triF sK) (derRO (ap1 triF cR)) triEq)
                       (gWeak Gam (tgtFDRO (ap1 triF cR))))
                    cTR
            rhs : Deriv (imp Gam (eqF (ap1 devF (ap1 srcF sK)) (ap1 devF (ap1 srcF cR))))
            rhs = gTrans (ap1 devF (ap1 srcF sK)) (ap1 devF (ad# ze# (ap1 srcF cR))) (ap1 devF (ap1 srcF cR))
                    (gTrans (ap1 devF (ap1 srcF sK)) (ap1 devF (ad# (ap1 srcF cL) (ap1 srcF cR))) (ap1 devF (ad# ze# (ap1 srcF cR)))
                       (gCong devF (ap1 srcF sK) (ad# (ap1 srcF cL) (ap1 srcF cR)) gSrcSK)
                       (gCong devF (ad# (ap1 srcF cL) (ap1 srcF cR)) (ad# ze# (ap1 srcF cR))
                          (gAdL2 (ap1 srcF cL) ze# (ap1 srcF cR) gSrcL)))
                    (gWeak Gam (devF_ad_ze (ap1 srcF cR)))
        in gTrans (ap1 tgtF (ap1 triF sK)) (ap1 devF (ap1 srcF cR)) (ap1 devF (ap1 srcF sK))
             lhs (gApply (eqSymImp (ap1 devF (ap1 srcF sK)) (ap1 devF (ap1 srcF cR))) rhs)
  in assembleG factV factS factT

------------------------------------------------------------------------
-- Ad_Su :  left child a Su node  =>  triF sK = derRS (triF (pL cL)) (triF cR) .
-- Context  Gam0 /\ (neg LL /\ htagLL) , htagLL = (dtag cL = dgSu) .

htagLL : Formula
htagLL = eqF (dtag cL) dgSu

glueAdSu : Deriv (imp (Cnj Gam0 (Cnj (neg LL) htagLL)) Bgoal)
glueAdSu =
  let cond : Formula
      cond = Cnj (neg LL) htagLL
      open Sub cond
      pNegLL : Deriv (imp Gam (neg LL))
      pNegLL = compI pCond (cnjL (neg LL) htagLL)
      pHtagLL : Deriv (imp Gam htagLL)
      pHtagLL = compI pCond (cnjR (neg LL) htagLL)
      gg : Term
      gg = pL cL
      -- ne / nl / htag of cL as Gam-facts.
      gNeL : Deriv (imp Gam (neg (eqF cL O)))
      gNeL = compI pHtagLL (neTag_imp cL 0)
      gNlL : Deriv (imp Gam (eqF (ap2 natEqF (ap1 Fst cL) (natCode 1)) O))
      gNlL = compI pNegLL (natEqF_complete (ap1 Fst cL) (natCode 1))
      -- grandchild validity  wfRed gg = O  (cL is Su: wfRed cL = wfRed gg).
      gWfSuEq : Deriv (imp Gam (eqF (ap1 wfRed cL) (ap1 wfRed gg)))
      gWfSuEq = wfRed_op_Su_gam Gam cL gNeL gNlL pHtagLL
      gWfG : Deriv (imp Gam (eqF (ap1 wfRed gg) O))
      gWfG = gTrans (ap1 wfRed gg) (ap1 wfRed cL) O
               (gApply (eqSymImp (ap1 wfRed cL) (ap1 wfRed gg)) gWfSuEq) gWfL
      -- grandchild leq bound (bare):  gg = Fst(Snd(Snd cL)) <= ... <= cL <= var 0.
      leqG : Deriv (leq gg (var 0))
      leqG = leq_trans gg (ap1 Snd (ap1 Snd cL)) (var 0)
               (fstLe (ap1 Snd (ap1 Snd cL)))
               (leq_trans (ap1 Snd (ap1 Snd cL)) (ap1 Snd cL) (var 0)
                  (sndLe (ap1 Snd cL))
                  (leq_trans (ap1 Snd cL) cL (var 0) (sndLe cL) leqL))
      -- child conj3 facts (grandchild gg, right cR).
      cjG = childCj gg leqG gWfG
      cVG = gApply (childV_imp gg) cjG
      cSG = gApply (childS_imp gg) cjG
      cTG = gApply (childT_imp gg) cjG
      cjR = childCj cR leqR gWfR
      cVR = gApply (childV_imp cR) cjR
      cSR = gApply (childS_imp cR) cjR
      cTR = gApply (childT_imp cR) cjR
      -- srcF cL = su# (srcF gg) , tgtF cL = su# (tgtF gg) .
      gSrcL : Deriv (imp Gam (eqF (ap1 srcF cL) (su# (ap1 srcF gg))))
      gSrcL = srcF_op_Su_gam Gam cL gNeL gNlL pHtagLL
      gTgtL : Deriv (imp Gam (eqF (ap1 tgtF cL) (su# (ap1 tgtF gg))))
      gTgtL = tgtF_op_Su_gam Gam cL gNeL gNlL pHtagLL
      -- triF sK = derRS (triF gg) (triF cR) .
      triEq : Deriv (imp Gam (eqF (ap1 triF sK) (derRS (ap1 triF gg) (ap1 triF cR))))
      triEq = gApply (cnjUncurry (cnjUncurry (cnjUncurry (triF_op_Ad_Su_imp sK ne_sK))))
                (gMp (gApply (cnjPair (Cnj (Cnj negLeaf htagA) (neg LL)) htagLL)
                        (gMp (gApply (cnjPair (Cnj negLeaf htagA) (neg LL)) pNH) pNegLL))
                     pHtagLL)
      tg : Term
      tg = ap1 triF gg
      tR : Term
      tR = ap1 triF cR
      factV : Deriv (imp Gam (eqF (ap1 wfRed (ap1 triF sK)) O))
      factV = gTrans (ap1 wfRed (ap1 triF sK)) (ap2 pi (ap1 wfRed tg) (ap1 wfRed tR)) O
                (gTrans (ap1 wfRed (ap1 triF sK)) (ap1 wfRed (derRS tg tR)) (ap2 pi (ap1 wfRed tg) (ap1 wfRed tR))
                   (gCong wfRed (ap1 triF sK) (derRS tg tR) triEq)
                   (gWeak Gam (wfRedDRS tg tR)))
                (gMp (gApply (piBothO_imp (ap1 wfRed tg) (ap1 wfRed tR)) cVG) cVR)
      -- S:  srcF (triF sK) = ad# (su# (tgtF gg)) (tgtF cR) = tgtF sK .
      factS : Deriv (imp Gam (eqF (ap1 srcF (ap1 triF sK)) (ap1 tgtF sK)))
      factS =
        let mid : Term
            mid = ad# (su# (ap1 tgtF gg)) (ap1 tgtF cR)
            lhs : Deriv (imp Gam (eqF (ap1 srcF (ap1 triF sK)) mid))
            lhs = gTrans (ap1 srcF (ap1 triF sK)) (ad# (su# (ap1 srcF tg)) (ap1 srcF tR)) mid
                    (gTrans (ap1 srcF (ap1 triF sK)) (ap1 srcF (derRS tg tR)) (ad# (su# (ap1 srcF tg)) (ap1 srcF tR))
                       (gCong srcF (ap1 triF sK) (derRS tg tR) triEq)
                       (gWeak Gam (srcFDRS tg tR)))
                    (gAdR2x (su# (ap1 srcF tg)) (su# (ap1 tgtF gg)) (ap1 srcF tR) (ap1 tgtF cR)
                       (gSu (ap1 srcF tg) (ap1 tgtF gg) cSG) cSR)
            rhs : Deriv (imp Gam (eqF (ap1 tgtF sK) mid))
            rhs = gTrans (ap1 tgtF sK) (ad# (ap1 tgtF cL) (ap1 tgtF cR)) mid
                    gTgtSK (gAdL2 (ap1 tgtF cL) (su# (ap1 tgtF gg)) (ap1 tgtF cR) gTgtL)
        in gTrans (ap1 srcF (ap1 triF sK)) mid (ap1 tgtF sK)
             lhs (gApply (eqSymImp (ap1 tgtF sK) mid) rhs)
      -- T:  tgtF (triF sK) = su# (ad# (devF (srcF gg)) (devF (srcF cR))) = devF (srcF sK) .
      factT : Deriv (imp Gam (eqF (ap1 tgtF (ap1 triF sK)) (ap1 devF (ap1 srcF sK))))
      factT =
        let mid : Term
            mid = su# (ad# (ap1 devF (ap1 srcF gg)) (ap1 devF (ap1 srcF cR)))
            lhs : Deriv (imp Gam (eqF (ap1 tgtF (ap1 triF sK)) mid))
            lhs = gTrans (ap1 tgtF (ap1 triF sK)) (su# (ad# (ap1 tgtF tg) (ap1 tgtF tR))) mid
                    (gTrans (ap1 tgtF (ap1 triF sK)) (ap1 tgtF (derRS tg tR)) (su# (ad# (ap1 tgtF tg) (ap1 tgtF tR)))
                       (gCong tgtF (ap1 triF sK) (derRS tg tR) triEq)
                       (gWeak Gam (tgtFDRS tg tR)))
                    (gSu (ad# (ap1 tgtF tg) (ap1 tgtF tR)) (ad# (ap1 devF (ap1 srcF gg)) (ap1 devF (ap1 srcF cR)))
                       (gAdR2x (ap1 tgtF tg) (ap1 devF (ap1 srcF gg)) (ap1 tgtF tR) (ap1 devF (ap1 srcF cR)) cTG cTR))
            rhs : Deriv (imp Gam (eqF (ap1 devF (ap1 srcF sK)) mid))
            rhs = gTrans (ap1 devF (ap1 srcF sK)) (ap1 devF (ad# (su# (ap1 srcF gg)) (ap1 srcF cR))) mid
                    (gCong devF (ap1 srcF sK) (ad# (su# (ap1 srcF gg)) (ap1 srcF cR))
                       (gTrans (ap1 srcF sK) (ad# (ap1 srcF cL) (ap1 srcF cR)) (ad# (su# (ap1 srcF gg)) (ap1 srcF cR))
                          gSrcSK (gAdL2 (ap1 srcF cL) (su# (ap1 srcF gg)) (ap1 srcF cR) gSrcL)))
                    (gWeak Gam (devF_ad_su (ap1 srcF gg) (ap1 srcF cR)))
        in gTrans (ap1 tgtF (ap1 triF sK)) mid (ap1 devF (ap1 srcF sK))
             lhs (gApply (eqSymImp (ap1 devF (ap1 srcF sK)) mid) rhs)
  in assembleG factV factS factT

------------------------------------------------------------------------
-- Ad_else :  left child a non-leaf, non-Su node  =>
--   triF sK = derAd (triF cL) (triF cR) .  Context  Gam0 /\ (neg LL /\ neg htagLL) .
-- V and S are uniform; the T endpoint needs  srcF cL  ad#-headed, so its RHS does
-- a further 3-way on dtag cL in {Ad,RO,RS} (devF_ad_ad), with the junk-tag branch
-- closed by validity (wfRed_op_reject_gam contradicts  wfRed cL = O ).

-- ad# left-arg congruence, polymorphic in the context.
adL2P : (G : Formula) (a b z : Term) -> Deriv (imp G (eqF a b)) ->
  Deriv (imp G (eqF (ad# a z) (ad# b z)))
adL2P G a b z d = impCongR pi (ap2 pi a z) (ap2 pi b z) tagAd (impCongL pi a b z d)

private
  -- the T-endpoint RHS development over a context K, given srcF cL = ad# P Q.
  devSrcOf : (K : Formula) (P Q : Term) ->
    Deriv (imp K (eqF (ap1 srcF sK) (ad# (ap1 srcF cL) (ap1 srcF cR)))) ->
    Deriv (imp K (eqF (ap1 srcF cL) (ad# P Q))) ->
    Deriv (imp K (eqF (ap1 devF (ap1 srcF sK))
                      (ad# (ap1 devF (ap1 srcF cL)) (ap1 devF (ap1 srcF cR)))))
  devSrcOf K P Q gSrc srcA =
    gTrans (ap1 devF (ap1 srcF sK)) (ap1 devF (ad# (ad# P Q) (ap1 srcF cR)))
           (ad# (ap1 devF (ap1 srcF cL)) (ap1 devF (ap1 srcF cR)))
      (gTrans (ap1 devF (ap1 srcF sK)) (ap1 devF (ad# (ap1 srcF cL) (ap1 srcF cR)))
              (ap1 devF (ad# (ad# P Q) (ap1 srcF cR)))
         (gCong devF (ap1 srcF sK) (ad# (ap1 srcF cL) (ap1 srcF cR)) gSrc)
         (gCong devF (ad# (ap1 srcF cL) (ap1 srcF cR)) (ad# (ad# P Q) (ap1 srcF cR))
            (adL2P K (ap1 srcF cL) (ad# P Q) (ap1 srcF cR) srcA)))
      (gTrans (ap1 devF (ad# (ad# P Q) (ap1 srcF cR)))
              (ad# (ap1 devF (ad# P Q)) (ap1 devF (ap1 srcF cR)))
              (ad# (ap1 devF (ap1 srcF cL)) (ap1 devF (ap1 srcF cR)))
         (gWeak K (devF_ad_ad P Q (ap1 srcF cR)))
         (adL2P K (ap1 devF (ad# P Q)) (ap1 devF (ap1 srcF cL)) (ap1 devF (ap1 srcF cR))
            (gCong devF (ad# P Q) (ap1 srcF cL) (gApply (eqSymImp (ap1 srcF cL) (ad# P Q)) srcA))))

A2 A3 A4 : Formula
A2 = eqF (dtag cL) dgAd
A3 = eqF (dtag cL) dgRO
A4 = eqF (dtag cL) dgRS

glueAdElse : Deriv (imp (Cnj Gam0 (Cnj (neg LL) (neg htagLL))) Bgoal)
glueAdElse =
  let cond : Formula
      cond = Cnj (neg LL) (neg htagLL)
      open Sub cond
      pNegLL : Deriv (imp Gam (neg LL))
      pNegLL = compI pCond (cnjL (neg LL) (neg htagLL))
      pNegHtag : Deriv (imp Gam (neg htagLL))
      pNegHtag = compI pCond (cnjR (neg LL) (neg htagLL))
      gNeL : Deriv (imp Gam (neg (eqF cL O)))
      gNeL = neFromWf cL gWfL
      gNlL : Deriv (imp Gam (eqF (ap2 natEqF (ap1 Fst cL) (natCode 1)) O))
      gNlL = compI pNegLL (natEqF_complete (ap1 Fst cL) (natCode 1))
      -- D : the T-endpoint RHS development goal.
      Dgoal : Formula
      Dgoal = eqF (ap1 devF (ap1 srcF sK))
                  (ad# (ap1 devF (ap1 srcF cL)) (ap1 devF (ap1 srcF cR)))
      -- branch cores (over Cnj Gam <tag>), then folded by caseElim.
      adCore : Deriv (imp (Cnj Gam A2) Dgoal)
      adCore =
        let K = Cnj Gam A2
            lift : {X : Formula} -> Deriv (imp Gam X) -> Deriv (imp K X)
            lift d = compI (cnjL Gam A2) d
            gH : Deriv (imp K A2)
            gH = cnjR Gam A2
            srcA = srcF_op_Ad_gam K cL (lift gNeL) (lift gNlL) gH
        in devSrcOf K (ap1 srcF (pL cL)) (ap1 srcF (pR cL)) (lift gSrcSK) srcA
      roCore : Deriv (imp (Cnj Gam A3) Dgoal)
      roCore =
        let K = Cnj Gam A3
            lift : {X : Formula} -> Deriv (imp Gam X) -> Deriv (imp K X)
            lift d = compI (cnjL Gam A3) d
            gH : Deriv (imp K A3)
            gH = cnjR Gam A3
            srcA = srcF_op_RO_gam K cL (lift gNeL) (lift gNlL) gH
        in devSrcOf K ze# (ap1 srcF (pL cL)) (lift gSrcSK) srcA
      rsCore : Deriv (imp (Cnj Gam A4) Dgoal)
      rsCore =
        let K = Cnj Gam A4
            lift : {X : Formula} -> Deriv (imp Gam X) -> Deriv (imp K X)
            lift d = compI (cnjL Gam A4) d
            gH : Deriv (imp K A4)
            gH = cnjR Gam A4
            srcA = srcF_op_RS_gam K cL (lift gNeL) (lift gNlL) gH
        in devSrcOf K (su# (ap1 srcF (pL cL))) (ap1 srcF (pR cL)) (lift gSrcSK) srcA
      -- reject : under neg A2, neg A3, neg A4 (and Gam) : exfalso.
      rejCore : Deriv (imp (Cnj (Cnj (Cnj Gam (neg A2)) (neg A3)) (neg A4)) Dgoal)
      rejCore =
        let K = Cnj (Cnj (Cnj Gam (neg A2)) (neg A3)) (neg A4)
            gGam : Deriv (imp K Gam)
            gGam = compI (cnjL (Cnj (Cnj Gam (neg A2)) (neg A3)) (neg A4))
                     (compI (cnjL (Cnj Gam (neg A2)) (neg A3)) (cnjL Gam (neg A2)))
            gnA2 : Deriv (imp K (neg A2))
            gnA2 = compI (cnjL (Cnj (Cnj Gam (neg A2)) (neg A3)) (neg A4))
                     (compI (cnjL (Cnj Gam (neg A2)) (neg A3)) (cnjR Gam (neg A2)))
            gnA3 : Deriv (imp K (neg A3))
            gnA3 = compI (cnjL (Cnj (Cnj Gam (neg A2)) (neg A3)) (neg A4))
                     (cnjR (Cnj Gam (neg A2)) (neg A3))
            gnA4 : Deriv (imp K (neg A4))
            gnA4 = cnjR (Cnj (Cnj Gam (neg A2)) (neg A3)) (neg A4)
            gn1 : Deriv (imp K (neg (eqF (dtag cL) (natCode 1))))
            gn1 = compI gGam pNegHtag
            wfReject : Deriv (imp K (eqF (ap1 wfRed cL) (ap1 s O)))
            wfReject = wfRed_op_reject_gam K cL (compI gGam gNeL) (compI gGam gNlL)
                         gn1 gnA2 gnA3 gnA4
            soO : Deriv (imp K (eqF (ap1 s O) O))
            soO = gTrans (ap1 s O) (ap1 wfRed cL) O
                    (gApply (eqSymImp (ap1 wfRed cL) (ap1 s O)) wfReject)
                    (compI gGam gWfL)
        in gMp (gApply (axExFalso (eqF (ap1 s O) O) Dgoal) soO) (gWeak K (neSucc O))
      -- reassociate a core over  Cnj Gam TA  to  Cnj BigCtx TA  (BigCtx -> Gam).
      reassocTo : (BigCtx TA : Formula) -> Deriv (imp BigCtx Gam) ->
        Deriv (imp (Cnj Gam TA) Dgoal) -> Deriv (imp (Cnj BigCtx TA) Dgoal)
      reassocTo BigCtx TA projGam core =
        compI (gMp (gApply (cnjPair Gam TA) (compI (cnjL BigCtx TA) projGam))
                   (cnjR BigCtx TA))
              core
      -- fold the 3-way + reject into  imp Gam Dgoal .
      e3 : Deriv (imp (Cnj (Cnj Gam (neg A2)) (neg A3)) Dgoal)
      e3 = caseElim {X = A4} {Y = neg A4} {Rf = imp (Cnj (Cnj Gam (neg A2)) (neg A3)) Dgoal}
             (identP (neg A4))
             (swapImp (cnjCurry (reassocTo (Cnj (Cnj Gam (neg A2)) (neg A3)) A4
                        (compI (cnjL (Cnj Gam (neg A2)) (neg A3)) (cnjL Gam (neg A2))) rsCore)))
             (swapImp (cnjCurry rejCore))
      e2 : Deriv (imp (Cnj Gam (neg A2)) Dgoal)
      e2 = caseElim {X = A3} {Y = neg A3} {Rf = imp (Cnj Gam (neg A2)) Dgoal}
             (identP (neg A3))
             (swapImp (cnjCurry (reassocTo (Cnj Gam (neg A2)) A3 (cnjL Gam (neg A2)) roCore)))
             (swapImp (cnjCurry e3))
      rhsDev : Deriv (imp Gam Dgoal)
      rhsDev = caseElim {X = A2} {Y = neg A2} {Rf = imp Gam Dgoal}
                 (identP (neg A2)) (swapImp (cnjCurry adCore)) (swapImp (cnjCurry e2))
      -- triF sK = derAd (triF cL) (triF cR).
      triEq : Deriv (imp Gam (eqF (ap1 triF sK) (derAd (ap1 triF cL) (ap1 triF cR))))
      triEq = gApply (cnjUncurry (cnjUncurry (cnjUncurry (triF_op_Ad_else_imp sK ne_sK))))
                (gMp (gApply (cnjPair (Cnj (Cnj negLeaf htagA) (neg LL)) (neg htagLL))
                        (gMp (gApply (cnjPair (Cnj negLeaf htagA) (neg LL)) pNH) pNegLL))
                     pNegHtag)
      cjL = childCj cL leqL gWfL
      cjR = childCj cR leqR gWfR
      cVL = gApply (childV_imp cL) cjL ; cSL = gApply (childS_imp cL) cjL ; cTL = gApply (childT_imp cL) cjL
      cVR = gApply (childV_imp cR) cjR ; cSR = gApply (childS_imp cR) cjR ; cTR = gApply (childT_imp cR) cjR
      factV : Deriv (imp Gam (eqF (ap1 wfRed (ap1 triF sK)) O))
      factV = gTrans (ap1 wfRed (ap1 triF sK)) (ap2 pi (ap1 wfRed (ap1 triF cL)) (ap1 wfRed (ap1 triF cR))) O
                (gTrans (ap1 wfRed (ap1 triF sK)) (ap1 wfRed (derAd (ap1 triF cL) (ap1 triF cR)))
                        (ap2 pi (ap1 wfRed (ap1 triF cL)) (ap1 wfRed (ap1 triF cR)))
                   (gCong wfRed (ap1 triF sK) (derAd (ap1 triF cL) (ap1 triF cR)) triEq)
                   (gWeak Gam (wfRedDAd (ap1 triF cL) (ap1 triF cR))))
                (gMp (gApply (piBothO_imp (ap1 wfRed (ap1 triF cL)) (ap1 wfRed (ap1 triF cR))) cVL) cVR)
      factS : Deriv (imp Gam (eqF (ap1 srcF (ap1 triF sK)) (ap1 tgtF sK)))
      factS =
        let mid : Term
            mid = ad# (ap1 tgtF cL) (ap1 tgtF cR)
            lhs = gTrans (ap1 srcF (ap1 triF sK)) (ad# (ap1 srcF (ap1 triF cL)) (ap1 srcF (ap1 triF cR))) mid
                    (gTrans (ap1 srcF (ap1 triF sK)) (ap1 srcF (derAd (ap1 triF cL) (ap1 triF cR)))
                            (ad# (ap1 srcF (ap1 triF cL)) (ap1 srcF (ap1 triF cR)))
                       (gCong srcF (ap1 triF sK) (derAd (ap1 triF cL) (ap1 triF cR)) triEq)
                       (gWeak Gam (srcFDAd (ap1 triF cL) (ap1 triF cR))))
                    (gAdR2x (ap1 srcF (ap1 triF cL)) (ap1 tgtF cL) (ap1 srcF (ap1 triF cR)) (ap1 tgtF cR) cSL cSR)
        in gTrans (ap1 srcF (ap1 triF sK)) mid (ap1 tgtF sK) lhs
             (gApply (eqSymImp (ap1 tgtF sK) mid) gTgtSK)
      factT : Deriv (imp Gam (eqF (ap1 tgtF (ap1 triF sK)) (ap1 devF (ap1 srcF sK))))
      factT =
        let mid : Term
            mid = ad# (ap1 devF (ap1 srcF cL)) (ap1 devF (ap1 srcF cR))
            lhs = gTrans (ap1 tgtF (ap1 triF sK)) (ad# (ap1 tgtF (ap1 triF cL)) (ap1 tgtF (ap1 triF cR))) mid
                    (gTrans (ap1 tgtF (ap1 triF sK)) (ap1 tgtF (derAd (ap1 triF cL) (ap1 triF cR)))
                            (ad# (ap1 tgtF (ap1 triF cL)) (ap1 tgtF (ap1 triF cR)))
                       (gCong tgtF (ap1 triF sK) (derAd (ap1 triF cL) (ap1 triF cR)) triEq)
                       (gWeak Gam (tgtFDAd (ap1 triF cL) (ap1 triF cR))))
                    (gAdR2x (ap1 tgtF (ap1 triF cL)) (ap1 devF (ap1 srcF cL)) (ap1 tgtF (ap1 triF cR)) (ap1 devF (ap1 srcF cR)) cTL cTR)
        in gTrans (ap1 tgtF (ap1 triF sK)) mid (ap1 devF (ap1 srcF sK)) lhs
             (gApply (eqSymImp (ap1 devF (ap1 srcF sK)) mid) rhsDev)
  in assembleG factV factS factT

------------------------------------------------------------------------
-- Assemble glue_Ad from the three sub-cases via nested caseElim on the left
-- child (leaf / Su / else), then cnjCurry to the standard nested-imp shape.

-- reassociate  (A /\ B) /\ Cf  ->  A /\ (B /\ Cf) .
reassoc3 : (A B Cf : Formula) -> Deriv (imp (Cnj (Cnj A B) Cf) (Cnj A (Cnj B Cf)))
reassoc3 A B Cf =
  let K : Formula
      K = Cnj (Cnj A B) Cf
      getA : Deriv (imp K A)
      getA = compI (cnjL (Cnj A B) Cf) (cnjL A B)
      getB : Deriv (imp K B)
      getB = compI (cnjL (Cnj A B) Cf) (cnjR A B)
      getC : Deriv (imp K Cf)
      getC = cnjR (Cnj A B) Cf
      bc : Deriv (imp K (Cnj B Cf))
      bc = gMp (gApply (cnjPair B Cf) getB) getC
  in gMp (gApply (cnjPair A (Cnj B Cf)) getA) bc

private
  resultG0 : Deriv (imp Gam0 Bgoal)
  resultG0 =
    let zeB : Deriv (imp LL (imp Gam0 Bgoal))
        zeB = swapImp (cnjCurry glueAdZe)
        -- reassociated Su / else cores over  (Gam0 /\ neg LL) /\ tag .
        glueAdSu' : Deriv (imp (Cnj (Cnj Gam0 (neg LL)) htagLL) Bgoal)
        glueAdSu' = compI (reassoc3 Gam0 (neg LL) htagLL) glueAdSu
        glueAdElse' : Deriv (imp (Cnj (Cnj Gam0 (neg LL)) (neg htagLL)) Bgoal)
        glueAdElse' = compI (reassoc3 Gam0 (neg LL) (neg htagLL)) glueAdElse
        elseG : Deriv (imp (Cnj Gam0 (neg LL)) Bgoal)
        elseG =
          caseElim {X = htagLL} {Y = neg htagLL} {Rf = imp (Cnj Gam0 (neg LL)) Bgoal}
            (identP (neg htagLL))
            (swapImp (cnjCurry glueAdSu'))
            (swapImp (cnjCurry glueAdElse'))
        elseB : Deriv (imp (neg LL) (imp Gam0 Bgoal))
        elseB = swapImp (cnjCurry elseG)
    in caseElim {X = LL} {Y = neg LL} {Rf = imp Gam0 Bgoal}
         (identP (neg LL)) zeB elseB

glue_Ad : Deriv (imp negLeaf (imp htagA (imp PA Bgoal)))
glue_Ad = cnjCurry (cnjCurry resultG0)
