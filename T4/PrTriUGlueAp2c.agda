{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.PrTriUGlueAp2c -- the ap2c-congruence sub-glues for the full-PR CR dispatch,
-- written as THIN INSTANCES of the signature-generic T4.TriUNodeKit.nodeGlue:
-- each rule supplies only its residual N and the five per-node facts
-- (triEq, wrN, wfN, srcN, tgtN); all plumbing lives in TriUNodeKit.
--
-- Funhead sub-dispatch on Fst(funP sK):  7 (v=cProj, leaf) -> derV residual ;
-- 8 (cRec) -> R-base (Rb, derRb residual) / R-step (Rs) / Rcong (ap2c residual).
--
-- No holes, no postulates, no termination warnings (only the benign
-- RuleInst3:328 unreachable-clauses warning); --safe --without-K --exact-split.

module T4.PrTriUGlueAp2c where

open import T4.Base

open import T4.PrTriUGlue using ( sK ; PA ; negLeaf ; Bgoal ; ne_sK ; rebound )
open import T4.DerCodeS using ( dtag ; pL ; pR )
open import T4.PrDerCode using ( derV ; dgAp2c ; derRb ; bun3 ; derLeaf )
open import T4.BinTree using ( binNode )
open import T4.PrCodeObj
  using ( tmO ; tmAp1 ; tmAp2 ; cProj ; hd_cProj ; cRec ; hd_cRec ; recFun )
open import T4.GammaCtx using ( Cnj ; cnjL ; cnjR )
open import T4.PrWfRed using ( wfRed ; wfRed_rV ; wfRed_rRb )
open import T4.PrWfFunRec using ( wfFunRec ; funValid ; wfFunRec_rV ; wfFunRec_rRb )
open import T4.PrWfFun using ( wfFun ; isF2 )
open import T4.PrTri using ( triF )
open import T4.PrSrc using ( srcF ; srcF_rV ; srcF_rRb )
open import T4.PrTgt using ( tgtF ; tgtF_rV ; tgtF_rRb )
open import T4.PrDev using ( devF )

open import T4.PrTriUOpaqueImp using ( triF_op_ap2c_v_imp )
open import T4.PrTriUOpaque2Imp using ( triF_op_ap2c_Rb_imp )
open import T4.PrSrcUOpaqueImp using ( srcF_op_ap2c_imp )
open import T4.PrTgtUOpaqueImp using ( tgtF_op_ap2c_imp )
open import T4.PrWfRedUOpaqueImp using ( wfRed_op_ap2c_imp )
open import T4.PrWfFunRecUOpaqueImp using ( wfFunRec_op_ap2c_imp )
open import T4.PrDevByHead using ( devF_ap2_v_h ; devF_ap2_Rb_h ; devF_ap2_Rcong_imp ; gF ; h1F ; h2F )
open import T4.PrLeafReflOImp using ( srcF_reflO_himp ; tgtF_reflO_himp )
open import T4.PrSrcHeadImp
  using ( srcF_ap1c_himp ; srcChildArg ; srcChildArgL ; srcChildArgR
        ; srcF_rO_himp ; srcF_rU_himp ; srcF_rV_himp ; srcF_rC_himp ; srcF_rRb_himp ; srcF_rRs_himp
        ; bR_rC ; bR_rRb ; bR_rRs ; bridge_rC ; bridge_rRb ; bridge_rRs ; mbHead_rC ; mbHead_rRb ; mbHead_rRs )
open import T4.PrTriUOpaque2Imp using ( triF_op_ap2c_Rcong_notAp1c_imp )
open import T4.PrCodeObj using ( cZero ; cId ; hd_tmAp2 )
open import T4.PrSrc using ( srcF_ap2c ; srcL )
open import T4.PrTgt using ( tgtF_ap2c )
open import T4.PrWfRed using ( wfRed_ap2c )
open import T4.PrWfFunRec using ( wfFunRec_ap2c )
open import T4.PrCodeObj using ( hd_tmAp1 ; tgAp1 ; tgAp2 ; recH1 ; recH2 )
open import T4.PrTriUOpaque2Imp using ( triF_op_ap2c_Rcong_ap1cNotSuc_imp )
open import T4.PrDerCode using () renaming ( ap2c to dAp2c )
open import T4.GammaCtx using ( gMp ; gWeak )

open import T4.PrTgtUOpaque using ( funP )
open import T4.PrFunValidCanon using ( funValidF ; congRec )
open import T4.PrFunValid using ( recon ; cG ; cH1 ; cH2 )
open import T4.PrWfFunLeafImp
  using ( wfFun_op_v_himp ; funValid_v_imp ; wfFun_op_R_head_himp ; funValid_R_imp ; restRval )

open import T4.WfRedExtract using ( pLValueBound ; pRValueBound )
open import BRA3.Contrapositive using ( compI ; identP )
open import BRA3.Logic using ( prependEqLeft )
open import T4.Thm12.ImpHelpers using ( impCongR ; impCongL )
open import T4.PrQCheckU using ( conj3 )
open import T4.PrCRGlueImpU using ( childV_imp ; childS_imp ; childT_imp )
open import T4.CtxKit using ( lift2 ; ap2c ; lift4 ; ap4c )
open import BRA3.Church using ( pi )

htagA2 : Formula
htagA2 = eqF (ap1 Fst (dtag sK)) dgAp2c

open import T4.TriUNodeKit htagA2

------------------------------------------------------------------------
-- Shared ap2c validity extraction.  The wfFunRec node cell is
--   wfFunRec sK = pi (isF2 fp) (pi (funValid fp) (pi (wfFunRec dL) (wfFunRec dR)))
-- and  wfRed sK = pi (wfRed dL) (wfRed dR) .  Project out the pieces.

private
  dL dR fp : Term
  dL = pL sK
  dR = pR sK
  fp = funP sK

  tail2 tail1 : Term
  tail2 = ap2 pi (ap1 wfFunRec dL) (ap1 wfFunRec dR)
  tail1 = ap2 pi (funValid fp) tail2

  -- wfFun fp = O  and the children's qcheck conjuncts (valid sub-derivations).
  wfFunFpO : (fh : Formula) -> Deriv (Ctx fh (eqF (ap1 wfFun fp) O))
  wfFunFpO fh =
    let cellO = G4trans (ap2 pi (isF2 fp) tail1) (ap1 wfFunRec sK) O fh
                  (G4sym (ap1 wfFunRec sK) (ap2 pi (isF2 fp) tail1) fh (addFunPA4 fh (wfFunRec_op_ap2c_imp sK ne_sK)))
                  (wfFunSK4 fh)
    in gPiL4 fh (funValid fp) tail2 (gPiR4 fh (isF2 fp) tail1 cellO)
  wfFunRecChildren : (fh : Formula) -> Deriv (Ctx fh (eqF tail2 O))
  wfFunRecChildren fh =
    let cellO = G4trans (ap2 pi (isF2 fp) tail1) (ap1 wfFunRec sK) O fh
                  (G4sym (ap1 wfFunRec sK) (ap2 pi (isF2 fp) tail1) fh (addFunPA4 fh (wfFunRec_op_ap2c_imp sK ne_sK)))
                  (wfFunSK4 fh)
    in gPiR4 fh (funValid fp) tail2 (gPiR4 fh (isF2 fp) tail1 cellO)
  wfRedChildren : (fh : Formula) -> Deriv (Ctx fh (eqF (ap2 pi (ap1 wfRed dL) (ap1 wfRed dR)) O))
  wfRedChildren fh =
    G4trans (ap2 pi (ap1 wfRed dL) (ap1 wfRed dR)) (ap1 wfRed sK) O fh
      (G4sym (ap1 wfRed sK) (ap2 pi (ap1 wfRed dL) (ap1 wfRed dR)) fh (addFunPA4 fh (wfRed_op_ap2c_imp sK ne_sK)))
      (wfRedSK4 fh)

  -- the child qcheck conjuncts (validity of triF children).
  cjL : (fh : Formula) -> Deriv (Ctx fh (eqF (ap1 conj3 dL) O))
  cjL fh = childCj fh dL (rebound dL (pLValueBound sK ne_sK))
             (gPiL4 fh (ap1 wfRed dL) (ap1 wfRed dR) (wfRedChildren fh))
             (gPiL4 fh (ap1 wfFunRec dL) (ap1 wfFunRec dR) (wfFunRecChildren fh))
  cjR : (fh : Formula) -> Deriv (Ctx fh (eqF (ap1 conj3 dR) O))
  cjR fh = childCj fh dR (rebound dR (pRValueBound sK ne_sK))
             (gPiR4 fh (ap1 wfRed dL) (ap1 wfRed dR) (wfRedChildren fh))
             (gPiR4 fh (ap1 wfFunRec dL) (ap1 wfFunRec dR) (wfFunRecChildren fh))

------------------------------------------------------------------------
-- glue_ap2c_v :  funhead = 7 (cProj).  N = derV (triF dL) (triF dR).

glue_ap2c_v : Deriv (Ctx (eqF (ap1 Fst (funP sK)) (natCode 7)) Bgoal)
glue_ap2c_v =
  let fh = eqF (ap1 Fst fp) (natCode 7)
      X1 = ap1 triF dL
      X2 = ap1 triF dR
      Y2 = ap1 devF (ap1 srcF dR)
      Dv = derV X1 X2
      cjLf = cjL fh
      cjRf = cjR fh
      cVL = ap4c (l4 fh (childV_imp dL)) cjLf
      cSL = ap4c (l4 fh (childS_imp dL)) cjLf
      cVR = ap4c (l4 fh (childV_imp dR)) cjRf
      cSR = ap4c (l4 fh (childS_imp dR)) cjRf
      cTR = ap4c (l4 fh (childT_imp dR)) cjRf
      cVLwfRed = splitL4 fh X1 cVL ; cVLwfFun = splitR4 fh X1 cVL
      cVRwfRed = splitL4 fh X2 cVR ; cVRwfFun = splitR4 fh X2 cVR
      -- recon fp = cProj (leaf: wfFun_op_v_himp gives wfFun fp = funValidF fp directly).
      fvfO = G4trans (ap1 funValidF fp) (ap1 wfFun fp) O fh
               (G4sym (ap1 wfFun fp) (ap1 funValidF fp) fh (fromFh fh (wfFun_op_v_himp fp))) (wfFunFpO fh)
      reconEqV = reconstruct fh fp cProj fvfO (funValid_v_imp fp)
      srcEqSK = addFunPA4 fh (srcF_op_ap2c_imp sK ne_sK)
      tgtEqSK = addFunPA4 fh (tgtF_op_ap2c_imp sK ne_sK)
      triEq = addPA4 fh (triF_op_ap2c_v_imp sK ne_sK)
      wrN = G4trans (ap1 wfRed Dv) (ap2 pi (ap1 wfRed X1) (ap1 wfRed X2)) O fh
              (l4 fh (wfRed_rV X1 X2)) (piB4 fh (ap1 wfRed X1) (ap1 wfRed X2) cVLwfRed cVRwfRed)
      wfN = G4trans (ap1 wfFunRec Dv) (ap2 pi (ap1 wfFunRec X1) (ap1 wfFunRec X2)) O fh
              (l4 fh (wfFunRec_rV X1 X2)) (piB4 fh (ap1 wfFunRec X1) (ap1 wfFunRec X2) cVLwfFun cVRwfFun)
      tgtEqSKp = G4trans (ap1 tgtF sK) (tmAp2 fp (ap1 tgtF dL) (ap1 tgtF dR))
                   (tmAp2 cProj (ap1 tgtF dL) (ap1 tgtF dR)) fh
                   tgtEqSK (G4Ap2Head fp cProj (ap1 tgtF dL) (ap1 tgtF dR) fh reconEqV)
      srcN = G4trans (ap1 srcF Dv) (tmAp2 cProj (ap1 tgtF dL) (ap1 tgtF dR)) (ap1 tgtF sK) fh
               (G4trans (ap1 srcF Dv) (tmAp2 cProj (ap1 srcF X1) (ap1 srcF X2)) (tmAp2 cProj (ap1 tgtF dL) (ap1 tgtF dR)) fh
                 (l4 fh (srcF_rV X1 X2))
                 (G4Ap2R cProj (ap1 srcF X1) (ap1 tgtF dL) (ap1 srcF X2) (ap1 tgtF dR) fh cSL cSR))
               (G4sym (ap1 tgtF sK) (tmAp2 cProj (ap1 tgtF dL) (ap1 tgtF dR)) fh tgtEqSKp)
      srcEqSKp = G4trans (ap1 srcF sK) (tmAp2 fp (ap1 srcF dL) (ap1 srcF dR))
                   (tmAp2 cProj (ap1 srcF dL) (ap1 srcF dR)) fh
                   srcEqSK (G4Ap2Head fp cProj (ap1 srcF dL) (ap1 srcF dR) fh reconEqV)
      devSrcEq = G4trans (ap1 devF (ap1 srcF sK)) (ap1 devF (tmAp2 cProj (ap1 srcF dL) (ap1 srcF dR))) Y2 fh
                   (G4cong devF (ap1 srcF sK) (tmAp2 cProj (ap1 srcF dL) (ap1 srcF dR)) fh srcEqSKp)
                   (l4 fh (devF_ap2_v_h cProj (ap1 srcF dL) (ap1 srcF dR) hd_cProj))
      tgtN = G4trans (ap1 tgtF Dv) Y2 (ap1 devF (ap1 srcF sK)) fh
               (G4trans (ap1 tgtF Dv) (ap1 tgtF X2) Y2 fh (l4 fh (tgtF_rV X1 X2)) cTR)
               (G4sym (ap1 devF (ap1 srcF sK)) Y2 fh devSrcEq)
  in nodeGlue fh Dv triEq wrN wfN srcN tgtN

------------------------------------------------------------------------
-- glue_ap2c_Rb :  funhead = 8 (cRec), pR head = 1 (reflO base).
-- N = derRb g h1 h2 (triF dL)  (after recon fp = cRec g h1 h2).  Folds the two
-- funhead conditions into  fh = Cnj funhead8 pRhead1 .

glue_ap2c_Rb : Deriv (Ctx (Cnj (eqF (ap1 Fst (funP sK)) (natCode 8)) (eqF (ap1 Fst (pR sK)) (natCode 1))) Bgoal)
glue_ap2c_Rb =
  let funhead8 = eqF (ap1 Fst fp) (natCode 8)
      pRhead1 = eqF (ap1 Fst dR) (natCode 1)
      fh = Cnj funhead8 pRhead1
      X1 = ap1 triF dL
      g = cG fp ; h1 = cH1 fp ; h2 = cH2 fp
      cc = cRec g h1 h2
      Y = ap1 devF (ap1 srcF dL)
      Drb = derRb g h1 h2 X1
      cjLf = cjL fh
      cVL = ap4c (l4 fh (childV_imp dL)) cjLf
      cSL = ap4c (l4 fh (childS_imp dL)) cjLf
      cTL = ap4c (l4 fh (childT_imp dL)) cjLf
      cVLwfRed = splitL4 fh X1 cVL ; cVLwfFun = splitR4 fh X1 cVL
      -- recon fp = cRec (compound: head extraction exposes funValidF fp).
      fvfO = funValidFfromWfFun fh fp (restRval fp)
               (compI (cnjL funhead8 pRhead1) (wfFun_op_R_head_himp fp)) (wfFunFpO fh)
      reconEqR = reconstruct fh fp cc fvfO (compI (cnjL funhead8 pRhead1) (funValid_R_imp fp))
      -- reflO facts for dR.
      srcDRtmO = fromFh fh (compI (cnjR funhead8 pRhead1) (srcF_reflO_himp dR))
      tgtDRtmO = fromFh fh (compI (cnjR funhead8 pRhead1) (tgtF_reflO_himp dR))
      srcEqSK = addFunPA4 fh (srcF_op_ap2c_imp sK ne_sK)
      tgtEqSK = addFunPA4 fh (tgtF_op_ap2c_imp sK ne_sK)
      -- triF sK = binNode (Pair 7 (Snd fp)) X1 derLeaf -> derRb (rewrite Snd fp = bun3).
      triRaw = addPA4 fh (fold2 funhead8 pRhead1
                 (eqF (ap1 triF sK) (binNode (ap2 Pair (natCode 7) (ap1 Snd fp)) X1 derLeaf))
                 (triF_op_ap2c_Rb_imp sK ne_sK))
      sndFpEq = G4trans (ap1 Snd fp) (ap1 Snd cc) (bun3 g h1 h2) fh
                  (G4cong Snd fp cc fh reconEqR) (l4 fh (axSnd (natCode 8) (bun3 g h1 h2)))
      BIGa = ap2 Pair (ap2 Pair (natCode 7) (ap1 Snd fp)) (ap2 Pair X1 derLeaf)
      BIGb = ap2 Pair (ap2 Pair (natCode 7) (bun3 g h1 h2)) (ap2 Pair X1 derLeaf)
      labConvImp = impCongR Pair BIGa BIGb (natCode 2)
                     (impCongL Pair (ap2 Pair (natCode 7) (ap1 Snd fp)) (ap2 Pair (natCode 7) (bun3 g h1 h2)) (ap2 Pair X1 derLeaf)
                       (impCongR Pair (ap1 Snd fp) (bun3 g h1 h2) (natCode 7) (identP (eqF (ap1 Snd fp) (bun3 g h1 h2)))))
      triEq = G4trans (ap1 triF sK) (binNode (ap2 Pair (natCode 7) (ap1 Snd fp)) X1 derLeaf) Drb fh
                triRaw (ap4c (l4 fh labConvImp) sndFpEq)
      wfFunccO = G4trans (ap1 wfFun cc) (ap1 wfFun fp) O fh
                   (G4cong wfFun cc fp fh (G4sym fp cc fh reconEqR)) (wfFunFpO fh)
      wrN = G4trans (ap1 wfRed Drb) (ap1 wfRed X1) O fh (l4 fh (wfRed_rRb g h1 h2 X1)) cVLwfRed
      wfN = G4trans (ap1 wfFunRec Drb) (ap2 pi (ap1 wfFun cc) (ap1 wfFunRec X1)) O fh
              (l4 fh (wfFunRec_rRb g h1 h2 X1)) (piB4 fh (ap1 wfFun cc) (ap1 wfFunRec X1) wfFunccO cVLwfFun)
      tgtEqSKr = G4trans (ap1 tgtF sK) (tmAp2 fp (ap1 tgtF dL) (ap1 tgtF dR)) (tmAp2 cc (ap1 tgtF dL) tmO) fh
                   tgtEqSK
                   (G4trans (tmAp2 fp (ap1 tgtF dL) (ap1 tgtF dR)) (tmAp2 cc (ap1 tgtF dL) (ap1 tgtF dR)) (tmAp2 cc (ap1 tgtF dL) tmO) fh
                     (G4Ap2Head fp cc (ap1 tgtF dL) (ap1 tgtF dR) fh reconEqR)
                     (G4Ap2Arg2 cc (ap1 tgtF dL) (ap1 tgtF dR) tmO fh tgtDRtmO))
      srcN = G4trans (ap1 srcF Drb) (tmAp2 cc (ap1 tgtF dL) tmO) (ap1 tgtF sK) fh
               (G4trans (ap1 srcF Drb) (tmAp2 cc (ap1 srcF X1) tmO) (tmAp2 cc (ap1 tgtF dL) tmO) fh
                 (l4 fh (srcF_rRb g h1 h2 X1)) (G4Ap2Arg1 cc (ap1 srcF X1) (ap1 tgtF dL) tmO fh cSL))
               (G4sym (ap1 tgtF sK) (tmAp2 cc (ap1 tgtF dL) tmO) fh tgtEqSKr)
      srcEqSKr = G4trans (ap1 srcF sK) (tmAp2 fp (ap1 srcF dL) (ap1 srcF dR)) (tmAp2 cc (ap1 srcF dL) tmO) fh
                   srcEqSK
                   (G4trans (tmAp2 fp (ap1 srcF dL) (ap1 srcF dR)) (tmAp2 cc (ap1 srcF dL) (ap1 srcF dR)) (tmAp2 cc (ap1 srcF dL) tmO) fh
                     (G4Ap2Head fp cc (ap1 srcF dL) (ap1 srcF dR) fh reconEqR)
                     (G4Ap2Arg2 cc (ap1 srcF dL) (ap1 srcF dR) tmO fh srcDRtmO))
      devSrcEq = G4trans (ap1 devF (ap1 srcF sK)) (ap1 devF (tmAp2 cc (ap1 srcF dL) tmO)) (tmAp1 g Y) fh
                   (G4cong devF (ap1 srcF sK) (tmAp2 cc (ap1 srcF dL) tmO) fh srcEqSKr)
                   (G4trans (ap1 devF (tmAp2 cc (ap1 srcF dL) tmO)) (tmAp1 (gF cc) Y) (tmAp1 g Y) fh
                     (l4 fh (devF_ap2_Rb_h cc (ap1 srcF dL) (hd_cRec g h1 h2)))
                     (G4TmAp1Head (gF cc) g Y fh (l4 fh (recFun g h1 h2))))
      tgtN = G4trans (ap1 tgtF Drb) (tmAp1 g Y) (ap1 devF (ap1 srcF sK)) fh
               (G4trans (ap1 tgtF Drb) (tmAp1 g (ap1 tgtF X1)) (tmAp1 g Y) fh
                 (l4 fh (tgtF_rRb g h1 h2 X1)) (G4TmAp1 g (ap1 tgtF X1) Y fh cTL))
               (G4sym (ap1 devF (ap1 srcF sK)) (tmAp1 g Y) fh devSrcEq)
  in nodeGlue fh Drb triEq wrN wfN srcN tgtN

------------------------------------------------------------------------
-- glue_ap2c_Rcong_ap1cNotSuc :  funhead = 8 (cRec), pR is an ap1c node whose
-- carried fun head m != 3 (not cSuc).  N = ap2c fp (triF dL) (triF dR)  (a plain
-- congruence; the cRec is NOT a redex because srcF dR is neither tmO nor s-headed).
-- Folds the four funhead conditions into  fh .

glue_ap2c_Rcong_ap1cNotSuc : (m : Nat) -> ((Eq m 3) -> Empty) ->
  Deriv (Ctx (Cnj (Cnj (Cnj (eqF (ap1 Fst (funP sK)) (natCode 8)) (eqF (ap1 Fst (pR sK)) (natCode 2)))
                        (eqF (ap1 Fst (ap1 Fst (ap1 Snd (pR sK)))) (natCode 1)))
                  (eqF (ap1 Fst (ap1 Snd (ap1 Fst (ap1 Snd (pR sK))))) (natCode m))) Bgoal)
glue_ap2c_Rcong_ap1cNotSuc m m3 =
  let funhead8 = eqF (ap1 Fst fp) (natCode 8)
      condPR2 = eqF (ap1 Fst dR) (natCode 2)
      condLabTag = eqF (ap1 Fst (ap1 Fst (ap1 Snd dR))) (natCode 1)
      condFunM = eqF (ap1 Fst (ap1 Snd (ap1 Fst (ap1 Snd dR)))) (natCode m)
      L1 = Cnj funhead8 condPR2
      L2 = Cnj L1 condLabTag
      fh = Cnj L2 condFunM
      X1 = ap1 triF dL
      X2 = ap1 triF dR
      g = cG fp ; h1 = cH1 fp ; h2 = cH2 fp
      cc = cRec g h1 h2
      N = dAp2c fp X1 X2
      eqR = eqF (ap1 triF sK) N
      -- fold the opaque triF eq into fh.
      fold_a = fold2 funhead8 condPR2 (imp condLabTag (imp condFunM eqR)) (triF_op_ap2c_Rcong_ap1cNotSuc_imp sK ne_sK m m3)
      fold_b = fold2 L1 condLabTag (imp condFunM eqR) fold_a
      fold_c = fold2 L2 condFunM eqR fold_b
      triEq = addPA4 fh fold_c
      -- condition projections (imp fh cond).
      fhFunhead8 = compI (cnjL L2 condFunM) (compI (cnjL L1 condLabTag) (cnjL funhead8 condPR2))
      fhCondPR2 = compI (cnjL L2 condFunM) (compI (cnjL L1 condLabTag) (cnjR funhead8 condPR2))
      fhCondLabTag = compI (cnjL L2 condFunM) (cnjR L1 condLabTag)
      fhCondFunM = cnjR L2 condFunM
      -- children validity.
      cjLf = cjL fh ; cjRf = cjR fh
      cVL = ap4c (l4 fh (childV_imp dL)) cjLf
      cSL = ap4c (l4 fh (childS_imp dL)) cjLf
      cTL = ap4c (l4 fh (childT_imp dL)) cjLf
      cVR = ap4c (l4 fh (childV_imp dR)) cjRf
      cSR = ap4c (l4 fh (childS_imp dR)) cjRf
      cTR = ap4c (l4 fh (childT_imp dR)) cjRf
      cVLwfRed = splitL4 fh X1 cVL ; cVLwfFun = splitR4 fh X1 cVL
      cVRwfRed = splitL4 fh X2 cVR ; cVRwfFun = splitR4 fh X2 cVR
      -- isF2 fp = O  (first conjunct of wfFunRec sK ap2c cell).
      isF2FpO = gPiL4 fh (isF2 fp) tail1
                  (G4trans (ap2 pi (isF2 fp) tail1) (ap1 wfFunRec sK) O fh
                    (G4sym (ap1 wfFunRec sK) (ap2 pi (isF2 fp) tail1) fh (addFunPA4 fh (wfFunRec_op_ap2c_imp sK ne_sK)))
                    (wfFunSK4 fh))
      -- recon fp = cc.
      fvfO = funValidFfromWfFun fh fp (restRval fp)
               (compI fhFunhead8 (wfFun_op_R_head_himp fp)) (wfFunFpO fh)
      reconEqR = reconstruct fh fp cc fvfO (compI fhFunhead8 (funValid_R_imp fp))
      -- opaque src/tgt.
      srcEqSK = addFunPA4 fh (srcF_op_ap2c_imp sK ne_sK)
      tgtEqSK = addFunPA4 fh (tgtF_op_ap2c_imp sK ne_sK)
      -- srcF dR = tmAp1 (funP dR)(srcChildArg dR).
      bR = tmAp1 (funP dR) (srcChildArg dR)
      srcFdR = fromFh fh (gMp (compI fhCondPR2 (srcF_ap1c_himp dR)) fhCondLabTag)
      -- V-fact.
      wrN = G4trans (ap1 wfRed N) (ap2 pi (ap1 wfRed X1) (ap1 wfRed X2)) O fh
              (l4 fh (wfRed_ap2c fp X1 X2)) (piB4 fh (ap1 wfRed X1) (ap1 wfRed X2) cVLwfRed cVRwfRed)
      wfN = G4trans (ap1 wfFunRec N) (ap2 pi (isF2 fp) (ap2 pi (funValid fp) (ap2 pi (ap1 wfFunRec X1) (ap1 wfFunRec X2)))) O fh
              (l4 fh (wfFunRec_ap2c fp X1 X2))
              (piB4 fh (isF2 fp) (ap2 pi (funValid fp) (ap2 pi (ap1 wfFunRec X1) (ap1 wfFunRec X2))) isF2FpO
                (piB4 fh (funValid fp) (ap2 pi (ap1 wfFunRec X1) (ap1 wfFunRec X2)) (wfFunFpO fh)
                  (piB4 fh (ap1 wfFunRec X1) (ap1 wfFunRec X2) cVLwfFun cVRwfFun)))
      -- S-fact.
      srcN = G4trans (ap1 srcF N) (tmAp2 fp (ap1 tgtF dL) (ap1 tgtF dR)) (ap1 tgtF sK) fh
               (G4trans (ap1 srcF N) (tmAp2 fp (ap1 srcF X1) (ap1 srcF X2)) (tmAp2 fp (ap1 tgtF dL) (ap1 tgtF dR)) fh
                 (l4 fh (srcF_ap2c fp X1 X2))
                 (G4Ap2R fp (ap1 srcF X1) (ap1 tgtF dL) (ap1 srcF X2) (ap1 tgtF dR) fh cSL cSR))
               (G4sym (ap1 tgtF sK) (tmAp2 fp (ap1 tgtF dL) (ap1 tgtF dR)) fh tgtEqSK)
      -- T-fact:  tgtF N = tmAp2 fp (devF(srcF dL))(devF(srcF dR)) ; devF(srcF sK) = same.
      Ya = ap1 devF (ap1 srcF dL)
      Yb = ap1 devF (ap1 srcF dR)
      tgtNleft = G4trans (ap1 tgtF N) (tmAp2 fp (ap1 tgtF X1) (ap1 tgtF X2)) (tmAp2 fp Ya Yb) fh
                   (l4 fh (tgtF_ap2c fp X1 X2))
                   (G4Ap2R fp (ap1 tgtF X1) Ya (ap1 tgtF X2) Yb fh cTL cTR)
      -- devF chain:  srcF sK -> tmAp2 cc (srcF dL) bR ;  devF of it via devF_ap2_Rcong_imp.
      srcSKrw = G4trans (ap1 srcF sK) (tmAp2 fp (ap1 srcF dL) (ap1 srcF dR)) (tmAp2 cc (ap1 srcF dL) bR) fh
                  srcEqSK
                  (G4trans (tmAp2 fp (ap1 srcF dL) (ap1 srcF dR)) (tmAp2 cc (ap1 srcF dL) (ap1 srcF dR)) (tmAp2 cc (ap1 srcF dL) bR) fh
                    (G4Ap2Head fp cc (ap1 srcF dL) (ap1 srcF dR) fh reconEqR)
                    (G4Ap2Arg2 cc (ap1 srcF dL) (ap1 srcF dR) bR fh srcFdR))
      bridge1 = cong1 Fst (ruleTrans (cong1 Fst (axSnd tgAp1 (ap2 Pair (funP dR) (srcChildArg dR))))
                                      (axFst (funP dR) (srcChildArg dR)))
      hbfAnt = compI fhCondFunM (prependEqLeft (ap1 Fst (ap1 Fst (ap1 Snd bR))) (ap1 Fst (funP dR)) (natCode m) bridge1)
      devRcong = fromFh fh (compI hbfAnt
                   (devF_ap2_Rcong_imp cc (ap1 srcF dL) bR (hd_cRec g h1 h2) 1 m
                     (hd_tmAp1 (funP dR) (srcChildArg dR)) (\ ()) m3))
      -- collapse cRec(gF cc)... = fp  and  devF bR = devF(srcF dR) = Yb.
      ccCollapse = G4Ap2Head (cRec (gF cc) (h1F cc) (h2F cc)) fp Ya (ap1 devF bR) fh
                     (G4trans (cRec (gF cc) (h1F cc) (h2F cc)) cc fp fh
                       (l4 fh (congRec' g h1 h2)) (G4sym fp cc fh reconEqR))
      devbRcollapse = G4Ap2Arg2 fp Ya (ap1 devF bR) Yb fh
                        (G4cong devF bR (ap1 srcF dR) fh (G4sym (ap1 srcF dR) bR fh srcFdR))
      devSK = G4trans (ap1 devF (ap1 srcF sK)) (ap1 devF (tmAp2 cc (ap1 srcF dL) bR)) (tmAp2 fp Ya Yb) fh
                (G4cong devF (ap1 srcF sK) (tmAp2 cc (ap1 srcF dL) bR) fh srcSKrw)
                (G4trans (ap1 devF (tmAp2 cc (ap1 srcF dL) bR)) (tmAp2 (cRec (gF cc) (h1F cc) (h2F cc)) Ya (ap1 devF bR)) (tmAp2 fp Ya Yb) fh
                  devRcong
                  (G4trans (tmAp2 (cRec (gF cc) (h1F cc) (h2F cc)) Ya (ap1 devF bR)) (tmAp2 fp Ya (ap1 devF bR)) (tmAp2 fp Ya Yb) fh
                    ccCollapse devbRcollapse))
      tgtN = G4trans (ap1 tgtF N) (tmAp2 fp Ya Yb) (ap1 devF (ap1 srcF sK)) fh
               tgtNleft (G4sym (ap1 devF (ap1 srcF sK)) (tmAp2 fp Ya Yb) fh devSK)
  in nodeGlue fh N triEq wrN wfN srcN tgtN
  where
    congRec' : (g h1 h2 : Term) -> Deriv (eqF (cRec (gF (cRec g h1 h2)) (h1F (cRec g h1 h2)) (h2F (cRec g h1 h2))) (cRec g h1 h2))
    congRec' g h1 h2 = congRec (gF (cRec g h1 h2)) g (h1F (cRec g h1 h2)) h1 (h2F (cRec g h1 h2)) h2
                         (recFun g h1 h2) (recH1 g h1 h2) (recH2 g h1 h2)

------------------------------------------------------------------------
-- glue_ap2c_Rcong_rO :  funhead = 8 (cRec), pR is an o-redex (dtag=dgRo).
-- Same shape as ap1cNotSuc but srcF dR = tmAp1 cZero (..)  (concrete fun,
-- inner head 4 != 3), so the devF Rcong development applies with mf=4 BARE.

glue_ap2c_Rcong_rO :
  Deriv (Ctx (Cnj (Cnj (eqF (ap1 Fst (funP sK)) (natCode 8)) (eqF (ap1 Fst (pR sK)) (natCode 2)))
                  (eqF (ap1 Fst (ap1 Fst (ap1 Snd (pR sK)))) (natCode 3))) Bgoal)
glue_ap2c_Rcong_rO =
  let funhead8 = eqF (ap1 Fst fp) (natCode 8)
      condPR2 = eqF (ap1 Fst dR) (natCode 2)
      condDtag3 = eqF (ap1 Fst (ap1 Fst (ap1 Snd dR))) (natCode 3)
      L1 = Cnj funhead8 condPR2
      fh = Cnj L1 condDtag3
      X1 = ap1 triF dL
      X2 = ap1 triF dR
      g = cG fp ; h1 = cH1 fp ; h2 = cH2 fp
      cc = cRec g h1 h2
      N = dAp2c fp X1 X2
      eqR = eqF (ap1 triF sK) N
      fold_a = fold2 funhead8 condPR2 (imp condDtag3 eqR) (triF_op_ap2c_Rcong_notAp1c_imp sK ne_sK 3 (\ ()))
      fold_b = fold2 L1 condDtag3 eqR fold_a
      triEq = addPA4 fh fold_b
      fhFunhead8 = compI (cnjL L1 condDtag3) (cnjL funhead8 condPR2)
      fhCondPR2 = compI (cnjL L1 condDtag3) (cnjR funhead8 condPR2)
      fhCondDtag3 = cnjR L1 condDtag3
      cjLf = cjL fh ; cjRf = cjR fh
      cVL = ap4c (l4 fh (childV_imp dL)) cjLf
      cSL = ap4c (l4 fh (childS_imp dL)) cjLf
      cTL = ap4c (l4 fh (childT_imp dL)) cjLf
      cVR = ap4c (l4 fh (childV_imp dR)) cjRf
      cSR = ap4c (l4 fh (childS_imp dR)) cjRf
      cTR = ap4c (l4 fh (childT_imp dR)) cjRf
      cVLwfRed = splitL4 fh X1 cVL ; cVLwfFun = splitR4 fh X1 cVL
      cVRwfRed = splitL4 fh X2 cVR ; cVRwfFun = splitR4 fh X2 cVR
      isF2FpO = gPiL4 fh (isF2 fp) tail1
                  (G4trans (ap2 pi (isF2 fp) tail1) (ap1 wfFunRec sK) O fh
                    (G4sym (ap1 wfFunRec sK) (ap2 pi (isF2 fp) tail1) fh (addFunPA4 fh (wfFunRec_op_ap2c_imp sK ne_sK)))
                    (wfFunSK4 fh))
      fvfO = funValidFfromWfFun fh fp (restRval fp)
               (compI fhFunhead8 (wfFun_op_R_head_himp fp)) (wfFunFpO fh)
      reconEqR = reconstruct fh fp cc fvfO (compI fhFunhead8 (funValid_R_imp fp))
      srcEqSK = addFunPA4 fh (srcF_op_ap2c_imp sK ne_sK)
      tgtEqSK = addFunPA4 fh (tgtF_op_ap2c_imp sK ne_sK)
      bR = tmAp1 cZero (srcChildArg dR)
      srcFdR = fromFh fh (gMp (compI fhCondPR2 (srcF_rO_himp dR)) fhCondDtag3)
      wrN = G4trans (ap1 wfRed N) (ap2 pi (ap1 wfRed X1) (ap1 wfRed X2)) O fh
              (l4 fh (wfRed_ap2c fp X1 X2)) (piB4 fh (ap1 wfRed X1) (ap1 wfRed X2) cVLwfRed cVRwfRed)
      wfN = G4trans (ap1 wfFunRec N) (ap2 pi (isF2 fp) (ap2 pi (funValid fp) (ap2 pi (ap1 wfFunRec X1) (ap1 wfFunRec X2)))) O fh
              (l4 fh (wfFunRec_ap2c fp X1 X2))
              (piB4 fh (isF2 fp) (ap2 pi (funValid fp) (ap2 pi (ap1 wfFunRec X1) (ap1 wfFunRec X2))) isF2FpO
                (piB4 fh (funValid fp) (ap2 pi (ap1 wfFunRec X1) (ap1 wfFunRec X2)) (wfFunFpO fh)
                  (piB4 fh (ap1 wfFunRec X1) (ap1 wfFunRec X2) cVLwfFun cVRwfFun)))
      srcN = G4trans (ap1 srcF N) (tmAp2 fp (ap1 tgtF dL) (ap1 tgtF dR)) (ap1 tgtF sK) fh
               (G4trans (ap1 srcF N) (tmAp2 fp (ap1 srcF X1) (ap1 srcF X2)) (tmAp2 fp (ap1 tgtF dL) (ap1 tgtF dR)) fh
                 (l4 fh (srcF_ap2c fp X1 X2))
                 (G4Ap2R fp (ap1 srcF X1) (ap1 tgtF dL) (ap1 srcF X2) (ap1 tgtF dR) fh cSL cSR))
               (G4sym (ap1 tgtF sK) (tmAp2 fp (ap1 tgtF dL) (ap1 tgtF dR)) fh tgtEqSK)
      Ya = ap1 devF (ap1 srcF dL)
      Yb = ap1 devF (ap1 srcF dR)
      tgtNleft = G4trans (ap1 tgtF N) (tmAp2 fp (ap1 tgtF X1) (ap1 tgtF X2)) (tmAp2 fp Ya Yb) fh
                   (l4 fh (tgtF_ap2c fp X1 X2))
                   (G4Ap2R fp (ap1 tgtF X1) Ya (ap1 tgtF X2) Yb fh cTL cTR)
      srcSKrw = G4trans (ap1 srcF sK) (tmAp2 fp (ap1 srcF dL) (ap1 srcF dR)) (tmAp2 cc (ap1 srcF dL) bR) fh
                  srcEqSK
                  (G4trans (tmAp2 fp (ap1 srcF dL) (ap1 srcF dR)) (tmAp2 cc (ap1 srcF dL) (ap1 srcF dR)) (tmAp2 cc (ap1 srcF dL) bR) fh
                    (G4Ap2Head fp cc (ap1 srcF dL) (ap1 srcF dR) fh reconEqR)
                    (G4Ap2Arg2 cc (ap1 srcF dL) (ap1 srcF dR) bR fh srcFdR))
      bridge = ruleTrans (cong1 Fst (ruleTrans (cong1 Fst (axSnd tgAp1 (ap2 Pair cZero (srcChildArg dR)))) (axFst cZero (srcChildArg dR)))) (axFst (natCode 4) O)
      devRcong = l4 fh (mp (devF_ap2_Rcong_imp cc (ap1 srcF dL) bR (hd_cRec g h1 h2) 1 4
                             (hd_tmAp1 cZero (srcChildArg dR)) (\ ()) (\ ())) bridge)
      ccCollapse = G4Ap2Head (cRec (gF cc) (h1F cc) (h2F cc)) fp Ya (ap1 devF bR) fh
                     (G4trans (cRec (gF cc) (h1F cc) (h2F cc)) cc fp fh
                       (l4 fh (congRec' g h1 h2)) (G4sym fp cc fh reconEqR))
      devbRcollapse = G4Ap2Arg2 fp Ya (ap1 devF bR) Yb fh
                        (G4cong devF bR (ap1 srcF dR) fh (G4sym (ap1 srcF dR) bR fh srcFdR))
      devSK = G4trans (ap1 devF (ap1 srcF sK)) (ap1 devF (tmAp2 cc (ap1 srcF dL) bR)) (tmAp2 fp Ya Yb) fh
                (G4cong devF (ap1 srcF sK) (tmAp2 cc (ap1 srcF dL) bR) fh srcSKrw)
                (G4trans (ap1 devF (tmAp2 cc (ap1 srcF dL) bR)) (tmAp2 (cRec (gF cc) (h1F cc) (h2F cc)) Ya (ap1 devF bR)) (tmAp2 fp Ya Yb) fh
                  devRcong
                  (G4trans (tmAp2 (cRec (gF cc) (h1F cc) (h2F cc)) Ya (ap1 devF bR)) (tmAp2 fp Ya (ap1 devF bR)) (tmAp2 fp Ya Yb) fh
                    ccCollapse devbRcollapse))
      tgtN = G4trans (ap1 tgtF N) (tmAp2 fp Ya Yb) (ap1 devF (ap1 srcF sK)) fh
               tgtNleft (G4sym (ap1 devF (ap1 srcF sK)) (tmAp2 fp Ya Yb) fh devSK)
  in nodeGlue fh N triEq wrN wfN srcN tgtN
  where
    congRec' : (g h1 h2 : Term) -> Deriv (eqF (cRec (gF (cRec g h1 h2)) (h1F (cRec g h1 h2)) (h2F (cRec g h1 h2))) (cRec g h1 h2))
    congRec' g h1 h2 = congRec (gF (cRec g h1 h2)) g (h1F (cRec g h1 h2)) h1 (h2F (cRec g h1 h2)) h2
                         (recFun g h1 h2) (recH1 g h1 h2) (recH2 g h1 h2)

------------------------------------------------------------------------
-- Shared assembler for the ap2c-congruence (Rcong) glues: given fh, the residual
-- triEq, the rewritten child source bR (= srcF dR), the reconstruction fp = cc,
-- and the devF-Rcong development, build the goal.  Every Rcong sub-case differs
-- ONLY in (fh, triEq, bR, srcFdR, reconEqR, devRcong).

private
  ccA : Term
  ccA = cRec (cG fp) (cH1 fp) (cH2 fp)
  congRecA : Deriv (eqF (cRec (gF ccA) (h1F ccA) (h2F ccA)) ccA)
  congRecA = congRec (gF ccA) (cG fp) (h1F ccA) (cH1 fp) (h2F ccA) (cH2 fp)
               (recFun (cG fp) (cH1 fp) (cH2 fp)) (recH1 (cG fp) (cH1 fp) (cH2 fp)) (recH2 (cG fp) (cH1 fp) (cH2 fp))

  ap2cCongGlue : (fh : Formula) (bR : Term) ->
    Deriv (Ctx fh (eqF (ap1 triF sK) (dAp2c fp (ap1 triF dL) (ap1 triF dR)))) ->
    Deriv (Ctx fh (eqF (ap1 srcF dR) bR)) ->
    Deriv (Ctx fh (eqF fp ccA)) ->
    Deriv (Ctx fh (eqF (ap1 devF (tmAp2 ccA (ap1 srcF dL) bR))
                       (tmAp2 (cRec (gF ccA) (h1F ccA) (h2F ccA)) (ap1 devF (ap1 srcF dL)) (ap1 devF bR)))) ->
    Deriv (Ctx fh Bgoal)
  ap2cCongGlue fh bR triEq srcFdR reconEqR devRcong =
    let X1 = ap1 triF dL ; X2 = ap1 triF dR ; N = dAp2c fp X1 X2 ; cc = ccA
        Ya = ap1 devF (ap1 srcF dL) ; Yb = ap1 devF (ap1 srcF dR)
        cjLf = cjL fh ; cjRf = cjR fh
        cVL = ap4c (l4 fh (childV_imp dL)) cjLf
        cSL = ap4c (l4 fh (childS_imp dL)) cjLf
        cTL = ap4c (l4 fh (childT_imp dL)) cjLf
        cVR = ap4c (l4 fh (childV_imp dR)) cjRf
        cSR = ap4c (l4 fh (childS_imp dR)) cjRf
        cTR = ap4c (l4 fh (childT_imp dR)) cjRf
        cVLwfRed = splitL4 fh X1 cVL ; cVLwfFun = splitR4 fh X1 cVL
        cVRwfRed = splitL4 fh X2 cVR ; cVRwfFun = splitR4 fh X2 cVR
        isF2FpO = gPiL4 fh (isF2 fp) tail1
                    (G4trans (ap2 pi (isF2 fp) tail1) (ap1 wfFunRec sK) O fh
                      (G4sym (ap1 wfFunRec sK) (ap2 pi (isF2 fp) tail1) fh (addFunPA4 fh (wfFunRec_op_ap2c_imp sK ne_sK)))
                      (wfFunSK4 fh))
        srcEqSK = addFunPA4 fh (srcF_op_ap2c_imp sK ne_sK)
        tgtEqSK = addFunPA4 fh (tgtF_op_ap2c_imp sK ne_sK)
        wrN = G4trans (ap1 wfRed N) (ap2 pi (ap1 wfRed X1) (ap1 wfRed X2)) O fh
                (l4 fh (wfRed_ap2c fp X1 X2)) (piB4 fh (ap1 wfRed X1) (ap1 wfRed X2) cVLwfRed cVRwfRed)
        wfN = G4trans (ap1 wfFunRec N) (ap2 pi (isF2 fp) (ap2 pi (funValid fp) (ap2 pi (ap1 wfFunRec X1) (ap1 wfFunRec X2)))) O fh
                (l4 fh (wfFunRec_ap2c fp X1 X2))
                (piB4 fh (isF2 fp) (ap2 pi (funValid fp) (ap2 pi (ap1 wfFunRec X1) (ap1 wfFunRec X2))) isF2FpO
                  (piB4 fh (funValid fp) (ap2 pi (ap1 wfFunRec X1) (ap1 wfFunRec X2)) (wfFunFpO fh)
                    (piB4 fh (ap1 wfFunRec X1) (ap1 wfFunRec X2) cVLwfFun cVRwfFun)))
        srcN = G4trans (ap1 srcF N) (tmAp2 fp (ap1 tgtF dL) (ap1 tgtF dR)) (ap1 tgtF sK) fh
                 (G4trans (ap1 srcF N) (tmAp2 fp (ap1 srcF X1) (ap1 srcF X2)) (tmAp2 fp (ap1 tgtF dL) (ap1 tgtF dR)) fh
                   (l4 fh (srcF_ap2c fp X1 X2))
                   (G4Ap2R fp (ap1 srcF X1) (ap1 tgtF dL) (ap1 srcF X2) (ap1 tgtF dR) fh cSL cSR))
                 (G4sym (ap1 tgtF sK) (tmAp2 fp (ap1 tgtF dL) (ap1 tgtF dR)) fh tgtEqSK)
        tgtNleft = G4trans (ap1 tgtF N) (tmAp2 fp (ap1 tgtF X1) (ap1 tgtF X2)) (tmAp2 fp Ya Yb) fh
                     (l4 fh (tgtF_ap2c fp X1 X2)) (G4Ap2R fp (ap1 tgtF X1) Ya (ap1 tgtF X2) Yb fh cTL cTR)
        srcSKrw = G4trans (ap1 srcF sK) (tmAp2 fp (ap1 srcF dL) (ap1 srcF dR)) (tmAp2 cc (ap1 srcF dL) bR) fh
                    srcEqSK
                    (G4trans (tmAp2 fp (ap1 srcF dL) (ap1 srcF dR)) (tmAp2 cc (ap1 srcF dL) (ap1 srcF dR)) (tmAp2 cc (ap1 srcF dL) bR) fh
                      (G4Ap2Head fp cc (ap1 srcF dL) (ap1 srcF dR) fh reconEqR)
                      (G4Ap2Arg2 cc (ap1 srcF dL) (ap1 srcF dR) bR fh srcFdR))
        ccCollapse = G4Ap2Head (cRec (gF cc) (h1F cc) (h2F cc)) fp Ya (ap1 devF bR) fh
                       (G4trans (cRec (gF cc) (h1F cc) (h2F cc)) cc fp fh (l4 fh congRecA) (G4sym fp cc fh reconEqR))
        devbRcollapse = G4Ap2Arg2 fp Ya (ap1 devF bR) Yb fh
                          (G4cong devF bR (ap1 srcF dR) fh (G4sym (ap1 srcF dR) bR fh srcFdR))
        devSK = G4trans (ap1 devF (ap1 srcF sK)) (ap1 devF (tmAp2 cc (ap1 srcF dL) bR)) (tmAp2 fp Ya Yb) fh
                  (G4cong devF (ap1 srcF sK) (tmAp2 cc (ap1 srcF dL) bR) fh srcSKrw)
                  (G4trans (ap1 devF (tmAp2 cc (ap1 srcF dL) bR)) (tmAp2 (cRec (gF cc) (h1F cc) (h2F cc)) Ya (ap1 devF bR)) (tmAp2 fp Ya Yb) fh
                    devRcong
                    (G4trans (tmAp2 (cRec (gF cc) (h1F cc) (h2F cc)) Ya (ap1 devF bR)) (tmAp2 fp Ya (ap1 devF bR)) (tmAp2 fp Ya Yb) fh
                      ccCollapse devbRcollapse))
        tgtN = G4trans (ap1 tgtF N) (tmAp2 fp Ya Yb) (ap1 devF (ap1 srcF sK)) fh
                 tgtNleft (G4sym (ap1 devF (ap1 srcF sK)) (tmAp2 fp Ya Yb) fh devSK)
    in nodeGlue fh N triEq wrN wfN srcN tgtN

  -- per-case reconstruction fp = ccA, given the funhead8 projection from fh.
  reconA : (fh : Formula) -> Deriv (imp fh (eqF (ap1 Fst fp) (natCode 8))) -> Deriv (Ctx fh (eqF fp ccA))
  reconA fh fhF8 =
    reconstruct fh fp ccA
      (funValidFfromWfFun fh fp (restRval fp) (compI fhF8 (wfFun_op_R_head_himp fp)) (wfFunFpO fh))
      (compI fhF8 (funValid_R_imp fp))

-- glue_ap2c_Rcong_rU :  u-redex (dtag=dgRu).  srcF dR = tmAp1 cId (..), mf=5.
glue_ap2c_Rcong_rU :
  Deriv (Ctx (Cnj (Cnj (eqF (ap1 Fst (funP sK)) (natCode 8)) (eqF (ap1 Fst (pR sK)) (natCode 2)))
                  (eqF (ap1 Fst (ap1 Fst (ap1 Snd (pR sK)))) (natCode 4))) Bgoal)
glue_ap2c_Rcong_rU =
  let funhead8 = eqF (ap1 Fst fp) (natCode 8)
      condPR2 = eqF (ap1 Fst dR) (natCode 2)
      condDtag = eqF (ap1 Fst (ap1 Fst (ap1 Snd dR))) (natCode 4)
      L1 = Cnj funhead8 condPR2
      fh = Cnj L1 condDtag
      eqR = eqF (ap1 triF sK) (dAp2c fp (ap1 triF dL) (ap1 triF dR))
      fold_a = fold2 funhead8 condPR2 (imp condDtag eqR) (triF_op_ap2c_Rcong_notAp1c_imp sK ne_sK 4 (\ ()))
      triEq = addPA4 fh (fold2 L1 condDtag eqR fold_a)
      fhF8 = compI (cnjL L1 condDtag) (cnjL funhead8 condPR2)
      fhPR2 = compI (cnjL L1 condDtag) (cnjR funhead8 condPR2)
      fhDtag = cnjR L1 condDtag
      bR = tmAp1 cId (srcChildArg dR)
      srcFdR = fromFh fh (gMp (compI fhPR2 (srcF_rU_himp dR)) fhDtag)
      reconEqR = reconA fh fhF8
      bridge = ruleTrans (cong1 Fst (ruleTrans (cong1 Fst (axSnd tgAp1 (ap2 Pair cId (srcChildArg dR)))) (axFst cId (srcChildArg dR)))) (axFst (natCode 5) O)
      devRcong = l4 fh (mp (devF_ap2_Rcong_imp ccA (ap1 srcF dL) bR (hd_cRec (cG fp) (cH1 fp) (cH2 fp)) 1 5
                            (hd_tmAp1 cId (srcChildArg dR)) (\ ()) (\ ())) bridge)
  in ap2cCongGlue fh bR triEq srcFdR reconEqR devRcong

-- glue_ap2c_Rcong_rV :  v-redex (dtag=dgRv).  srcF dR = tmAp2 cProj .. (binary), mf=7, mb=2.
glue_ap2c_Rcong_rV :
  Deriv (Ctx (Cnj (Cnj (eqF (ap1 Fst (funP sK)) (natCode 8)) (eqF (ap1 Fst (pR sK)) (natCode 2)))
                  (eqF (ap1 Fst (ap1 Fst (ap1 Snd (pR sK)))) (natCode 5))) Bgoal)
glue_ap2c_Rcong_rV =
  let funhead8 = eqF (ap1 Fst fp) (natCode 8)
      condPR2 = eqF (ap1 Fst dR) (natCode 2)
      condDtag = eqF (ap1 Fst (ap1 Fst (ap1 Snd dR))) (natCode 5)
      L1 = Cnj funhead8 condPR2
      fh = Cnj L1 condDtag
      eqR = eqF (ap1 triF sK) (dAp2c fp (ap1 triF dL) (ap1 triF dR))
      fold_a = fold2 funhead8 condPR2 (imp condDtag eqR) (triF_op_ap2c_Rcong_notAp1c_imp sK ne_sK 5 (\ ()))
      triEq = addPA4 fh (fold2 L1 condDtag eqR fold_a)
      fhF8 = compI (cnjL L1 condDtag) (cnjL funhead8 condPR2)
      fhPR2 = compI (cnjL L1 condDtag) (cnjR funhead8 condPR2)
      fhDtag = cnjR L1 condDtag
      bR = tmAp2 cProj (srcChildArgL dR) (srcChildArgR dR)
      srcFdR = fromFh fh (gMp (compI fhPR2 (srcF_rV_himp dR)) fhDtag)
      reconEqR = reconA fh fhF8
      bridge = ruleTrans (cong1 Fst (ruleTrans (cong1 Fst (axSnd tgAp2 (ap2 Pair cProj (ap2 Pair (srcChildArgL dR) (srcChildArgR dR))))) (axFst cProj (ap2 Pair (srcChildArgL dR) (srcChildArgR dR))))) (axFst (natCode 7) O)
      devRcong = l4 fh (mp (devF_ap2_Rcong_imp ccA (ap1 srcF dL) bR (hd_cRec (cG fp) (cH1 fp) (cH2 fp)) 2 7
                            (hd_tmAp2 cProj (srcChildArgL dR) (srcChildArgR dR)) (\ ()) (\ ())) bridge)
  in ap2cCongGlue fh bR triEq srcFdR reconEqR devRcong

-- glue_ap2c_Rcong_rC :  C-redex (dtag=dgRC).  fun cComp, mf=6, mb=1.
glue_ap2c_Rcong_rC :
  Deriv (Ctx (Cnj (Cnj (eqF (ap1 Fst (funP sK)) (natCode 8)) (eqF (ap1 Fst (pR sK)) (natCode 2)))
                  (eqF (ap1 Fst (ap1 Fst (ap1 Snd (pR sK)))) (natCode 6))) Bgoal)
glue_ap2c_Rcong_rC =
  let funhead8 = eqF (ap1 Fst fp) (natCode 8)
      condPR2 = eqF (ap1 Fst dR) (natCode 2)
      condDtag = eqF (ap1 Fst (ap1 Fst (ap1 Snd dR))) (natCode 6)
      L1 = Cnj funhead8 condPR2
      fh = Cnj L1 condDtag
      eqR = eqF (ap1 triF sK) (dAp2c fp (ap1 triF dL) (ap1 triF dR))
      fold_a = fold2 funhead8 condPR2 (imp condDtag eqR) (triF_op_ap2c_Rcong_notAp1c_imp sK ne_sK 6 (\ ()))
      triEq = addPA4 fh (fold2 L1 condDtag eqR fold_a)
      fhF8 = compI (cnjL L1 condDtag) (cnjL funhead8 condPR2)
      fhPR2 = compI (cnjL L1 condDtag) (cnjR funhead8 condPR2)
      fhDtag = cnjR L1 condDtag
      bR = bR_rC dR
      srcFdR = fromFh fh (gMp (compI fhPR2 (srcF_rC_himp dR)) fhDtag)
      reconEqR = reconA fh fhF8
      devRcong = l4 fh (mp (devF_ap2_Rcong_imp ccA (ap1 srcF dL) bR (hd_cRec (cG fp) (cH1 fp) (cH2 fp)) 1 6
                            (mbHead_rC dR) (\ ()) (\ ())) (bridge_rC dR))
  in ap2cCongGlue fh bR triEq srcFdR reconEqR devRcong

-- glue_ap2c_Rcong_rRb :  Rb-redex (dtag=dgRb).  fun cRec, mf=8, mb=2.
glue_ap2c_Rcong_rRb :
  Deriv (Ctx (Cnj (Cnj (eqF (ap1 Fst (funP sK)) (natCode 8)) (eqF (ap1 Fst (pR sK)) (natCode 2)))
                  (eqF (ap1 Fst (ap1 Fst (ap1 Snd (pR sK)))) (natCode 7))) Bgoal)
glue_ap2c_Rcong_rRb =
  let funhead8 = eqF (ap1 Fst fp) (natCode 8)
      condPR2 = eqF (ap1 Fst dR) (natCode 2)
      condDtag = eqF (ap1 Fst (ap1 Fst (ap1 Snd dR))) (natCode 7)
      L1 = Cnj funhead8 condPR2
      fh = Cnj L1 condDtag
      eqR = eqF (ap1 triF sK) (dAp2c fp (ap1 triF dL) (ap1 triF dR))
      fold_a = fold2 funhead8 condPR2 (imp condDtag eqR) (triF_op_ap2c_Rcong_notAp1c_imp sK ne_sK 7 (\ ()))
      triEq = addPA4 fh (fold2 L1 condDtag eqR fold_a)
      fhF8 = compI (cnjL L1 condDtag) (cnjL funhead8 condPR2)
      fhPR2 = compI (cnjL L1 condDtag) (cnjR funhead8 condPR2)
      fhDtag = cnjR L1 condDtag
      bR = bR_rRb dR
      srcFdR = fromFh fh (gMp (compI fhPR2 (srcF_rRb_himp dR)) fhDtag)
      reconEqR = reconA fh fhF8
      devRcong = l4 fh (mp (devF_ap2_Rcong_imp ccA (ap1 srcF dL) bR (hd_cRec (cG fp) (cH1 fp) (cH2 fp)) 2 8
                            (mbHead_rRb dR) (\ ()) (\ ())) (bridge_rRb dR))
  in ap2cCongGlue fh bR triEq srcFdR reconEqR devRcong

-- glue_ap2c_Rcong_rRs :  Rs-redex (dtag=dgRs).  fun cRec, mf=8, mb=2.
glue_ap2c_Rcong_rRs :
  Deriv (Ctx (Cnj (Cnj (eqF (ap1 Fst (funP sK)) (natCode 8)) (eqF (ap1 Fst (pR sK)) (natCode 2)))
                  (eqF (ap1 Fst (ap1 Fst (ap1 Snd (pR sK)))) (natCode 8))) Bgoal)
glue_ap2c_Rcong_rRs =
  let funhead8 = eqF (ap1 Fst fp) (natCode 8)
      condPR2 = eqF (ap1 Fst dR) (natCode 2)
      condDtag = eqF (ap1 Fst (ap1 Fst (ap1 Snd dR))) (natCode 8)
      L1 = Cnj funhead8 condPR2
      fh = Cnj L1 condDtag
      eqR = eqF (ap1 triF sK) (dAp2c fp (ap1 triF dL) (ap1 triF dR))
      fold_a = fold2 funhead8 condPR2 (imp condDtag eqR) (triF_op_ap2c_Rcong_notAp1c_imp sK ne_sK 8 (\ ()))
      triEq = addPA4 fh (fold2 L1 condDtag eqR fold_a)
      fhF8 = compI (cnjL L1 condDtag) (cnjL funhead8 condPR2)
      fhPR2 = compI (cnjL L1 condDtag) (cnjR funhead8 condPR2)
      fhDtag = cnjR L1 condDtag
      bR = bR_rRs dR
      srcFdR = fromFh fh (gMp (compI fhPR2 (srcF_rRs_himp dR)) fhDtag)
      reconEqR = reconA fh fhF8
      devRcong = l4 fh (mp (devF_ap2_Rcong_imp ccA (ap1 srcF dL) bR (hd_cRec (cG fp) (cH1 fp) (cH2 fp)) 2 8
                            (mbHead_rRs dR) (\ ()) (\ ())) (bridge_rRs dR))
  in ap2cCongGlue fh bR triEq srcFdR reconEqR devRcong
