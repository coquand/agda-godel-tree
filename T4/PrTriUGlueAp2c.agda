{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.PrTriUGlueAp2c -- the ap2c-congruence GLUE for the full-PR CR dispatch.
-- An ap2c node carries a Fun2 fun; the funhead sub-dispatches on Fst(funP sK):
-- 7 (v = cProj, leaf) -> derV residual ; 8 (cRec) -> depth-2 R-dispatch.
-- This file: depth-4 ctx kit (binary children pL/pR) + the v sub-glue.
--
-- No holes, no postulates, no termination warnings (only the benign
-- RuleInst3:328 unreachable-clauses warning); --safe --without-K --exact-split.

module T4.PrTriUGlueAp2c where

open import T4.Base

open import T4.PrTriUGlue
  using ( sK ; PA ; negLeaf ; Bgoal ; ne_sK ; pa2a ; pa2phik ; rebound )
open import T4.DerCodeS using ( dtag ; pL ; pR )
open import T4.PrDerCode using ( derV ; dgAp2c )
open import T4.PrCodeObj using ( tmO ; tmAp1 ; tmAp2 ; cProj ; hd_cProj ; tgAp1 ; tgAp2 )

-- cRec R-base (Rb) sub-case extras.
open import T4.GammaCtx using ( Cnj ; cnjL ; cnjR )
open import T4.PrDerCode using ( derRb ; bun3 ; derLeaf )
open import T4.BinTree using ( binNode )
open import T4.PrSrc using ( srcF_rRb )
open import T4.PrTgt using ( tgtF_rRb )
open import T4.PrWfRed using ( wfRed_rRb )
open import T4.PrWfFunRec using ( wfFunRec_rRb )
open import T4.PrTriUOpaque2Imp using ( triF_op_ap2c_Rb_imp )
open import T4.PrLeafReflOImp using ( srcF_reflO_himp ; tgtF_reflO_himp )
open import T4.PrDevByHead using ( devF_ap2_Rb_h ; gF )
open import T4.PrCodeObj using ( cRec ; hd_cRec ; recFun )
open import T4.PrFunValid using ( cG ; cH1 ; cH2 )
open import T4.PrWfFunLeafImp using ( wfFun_op_R_head_himp ; recon_R_imp ; funValid_R_imp ; restRval )
open import T4.PrWfRed using ( wfRed ; wfRed_rV )
open import T4.PrWfFunRec using ( wfFunRec ; funValid ; wfFunRec_rV )
open import T4.PrWfFun using ( wfFun ; isF2 )
open import T4.PrWfRedFull using ( wfRedFull ; wfRedFull_eq )
open import T4.PrTri using ( triF )
open import T4.PrSrc using ( srcF ; srcF_rV )
open import T4.PrTgt using ( tgtF ; tgtF_rV )
open import T4.PrDev using ( devF )
open import T4.PrQCheckU using ( conj3 )
open import T4.PrQCheckProjU using ( PhiKU ; QofChildU )
open import T4.PrCRGlueU using ( conj3_unfold )
open import T4.PrCRGlueImpU
  using ( childV_imp ; childS_imp ; childT_imp ; eqDecO_complete_imp ; sigmaBothO_imp
        ; piBothO_imp ; piZeroL_imp ; piZeroR_imp )
open import T4.EqDecO using ( eqDecO )

open import T4.PrTriUOpaqueImp using ( triF_op_ap2c_v_imp )
open import T4.PrSrcUOpaqueImp using ( srcF_op_ap2c_imp )
open import T4.PrTgtUOpaqueImp using ( tgtF_op_ap2c_imp )
open import T4.PrWfRedUOpaqueImp using ( wfRed_op_ap2c_imp )
open import T4.PrWfFunRecUOpaqueImp using ( wfFunRec_op_ap2c_imp )
open import T4.PrDevByHead using ( devF_ap2_v_h )

open import T4.PrTgtUOpaque using ( funP )
open import T4.PrFunValidCanon using ( funValidF ; funValidF_eq )
open import T4.PrFunValid using ( recon )
open import T4.PrWfFunLeafImp using ( wfFun_op_v_himp ; funValid_v_imp )

open import T4.WfRedExtract using ( pLValueBound ; pRValueBound )
open import BRA3.Logic using ( prependEqLeft ; eqSymImp )
open import BRA3.Contrapositive using ( compI ; identP ; liftP )
open import T4.Thm12.ImpHelpers using ( impCong1 ; impCongR ; impCongL )
open import T4.CtxKit
  using ( lift2 ; ap2c ; lift3 ; ap3c ; trans3c
        ; lift4 ; get4a ; get4b ; get4c ; get4d ; ap4c ; trans4c )

open import BRA3.Church using ( pi ; sigma )
open import BRA3.ChurchLeq using ( leq )

------------------------------------------------------------------------
-- htagA2 = dtag sK = dgAp2c ;  Aform-extraction.

htagA2 : Formula
htagA2 = eqF (ap1 Fst (dtag sK)) dgAp2c

private
  Aform : Formula
  Aform = eqF (ap1 wfRedFull sK) O

  afToWfRed : Deriv (imp Aform (eqF (ap1 wfRed sK) O))
  afToWfRed = compI (prependEqLeft (ap2 pi (ap1 wfRed sK) (ap1 wfFunRec sK)) (ap1 wfRedFull sK) O
                       (ruleSym (wfRedFull_eq sK)))
                    (piZeroL_imp (ap1 wfRed sK) (ap1 wfFunRec sK))
  afToWfFun : Deriv (imp Aform (eqF (ap1 wfFunRec sK) O))
  afToWfFun = compI (prependEqLeft (ap2 pi (ap1 wfRed sK) (ap1 wfFunRec sK)) (ap1 wfRedFull sK) O
                       (ruleSym (wfRedFull_eq sK)))
                    (piZeroR_imp (ap1 wfRed sK) (ap1 wfFunRec sK))

------------------------------------------------------------------------
-- Depth-4 ctx kit over  [negLeaf, htagA2, fh, PA] .

private
  l4 : (fh : Formula) {X : Formula} -> Deriv X -> Deriv (imp negLeaf (imp htagA2 (imp fh (imp PA X))))
  l4 fh d = lift4 negLeaf htagA2 fh PA d

  G4cong : (f : Fun1) (a b : Term) (fh : Formula) ->
    Deriv (imp negLeaf (imp htagA2 (imp fh (imp PA (eqF a b))))) ->
    Deriv (imp negLeaf (imp htagA2 (imp fh (imp PA (eqF (ap1 f a) (ap1 f b))))))
  G4cong f a b fh d = ap4c (l4 fh (impCong1 f a b (identP (eqF a b)))) d

  G4sym : (a b : Term) (fh : Formula) ->
    Deriv (imp negLeaf (imp htagA2 (imp fh (imp PA (eqF a b))))) ->
    Deriv (imp negLeaf (imp htagA2 (imp fh (imp PA (eqF b a)))))
  G4sym a b fh d = ap4c (l4 fh (eqSymImp a b)) d

  G4trans : (a b c : Term) (fh : Formula) ->
    Deriv (imp negLeaf (imp htagA2 (imp fh (imp PA (eqF a b))))) ->
    Deriv (imp negLeaf (imp htagA2 (imp fh (imp PA (eqF b c))))) ->
    Deriv (imp negLeaf (imp htagA2 (imp fh (imp PA (eqF a c)))))
  G4trans a b c fh d e = trans4c a b c d e

  addPA4 : (fh : Formula) {X : Formula} ->
    Deriv (imp negLeaf (imp htagA2 (imp fh X))) ->
    Deriv (imp negLeaf (imp htagA2 (imp fh (imp PA X))))
  addPA4 fh {X} d = ap3c (lift3 negLeaf htagA2 fh (axK X PA)) d

  addFunPA4 : (fh : Formula) {X : Formula} ->
    Deriv (imp negLeaf (imp htagA2 X)) ->
    Deriv (imp negLeaf (imp htagA2 (imp fh (imp PA X))))
  addFunPA4 fh {X} d = ap2c (lift2 negLeaf htagA2 (compI (axK X PA) (axK (imp PA X) fh))) d

  paA : (fh : Formula) -> Deriv (imp negLeaf (imp htagA2 (imp fh (imp PA Aform))))
  paA fh = ap4c (l4 fh pa2a) (get4d negLeaf htagA2 fh PA)
  wfRedSK4 : (fh : Formula) -> Deriv (imp negLeaf (imp htagA2 (imp fh (imp PA (eqF (ap1 wfRed sK) O)))))
  wfRedSK4 fh = ap4c (l4 fh afToWfRed) (paA fh)
  wfFunSK4 : (fh : Formula) -> Deriv (imp negLeaf (imp htagA2 (imp fh (imp PA (eqF (ap1 wfFunRec sK) O)))))
  wfFunSK4 fh = ap4c (l4 fh afToWfFun) (paA fh)

  piB4 : (fh : Formula) (X Y : Term) ->
    Deriv (imp negLeaf (imp htagA2 (imp fh (imp PA (eqF X O))))) ->
    Deriv (imp negLeaf (imp htagA2 (imp fh (imp PA (eqF Y O))))) ->
    Deriv (imp negLeaf (imp htagA2 (imp fh (imp PA (eqF (ap2 pi X Y) O)))))
  piB4 fh X Y dX dY = ap4c (ap4c (l4 fh (piBothO_imp X Y)) dX) dY

  mkWfRedFull4 : (fh : Formula) (t : Term) ->
    Deriv (imp negLeaf (imp htagA2 (imp fh (imp PA (eqF (ap1 wfRed t) O))))) ->
    Deriv (imp negLeaf (imp htagA2 (imp fh (imp PA (eqF (ap1 wfFunRec t) O))))) ->
    Deriv (imp negLeaf (imp htagA2 (imp fh (imp PA (eqF (ap1 wfRedFull t) O)))))
  mkWfRedFull4 fh t wr wf =
    G4trans (ap1 wfRedFull t) (ap2 pi (ap1 wfRed t) (ap1 wfFunRec t)) O fh
      (l4 fh (wfRedFull_eq t)) (piB4 fh (ap1 wfRed t) (ap1 wfFunRec t) wr wf)

  mkChildCjFull4 : (fh : Formula) (child : Term) -> Deriv (leq child (var 0)) ->
    Deriv (imp negLeaf (imp htagA2 (imp fh (imp PA (eqF (ap1 wfRedFull child) O))))) ->
    Deriv (imp negLeaf (imp htagA2 (imp fh (imp PA (eqF (ap1 conj3 child) O)))))
  mkChildCjFull4 fh child leqCh cvf =
    ap4c (ap4c (l4 fh (QofChildU child leqCh)) (ap4c (l4 fh pa2phik) (get4d negLeaf htagA2 fh PA))) cvf

  splitL4 : (fh : Formula) (t : Term) ->
    Deriv (imp negLeaf (imp htagA2 (imp fh (imp PA (eqF (ap1 wfRedFull t) O))))) ->
    Deriv (imp negLeaf (imp htagA2 (imp fh (imp PA (eqF (ap1 wfRed t) O)))))
  splitL4 fh t d =
    ap4c (l4 fh (piZeroL_imp (ap1 wfRed t) (ap1 wfFunRec t)))
      (G4trans (ap2 pi (ap1 wfRed t) (ap1 wfFunRec t)) (ap1 wfRedFull t) O fh
        (G4sym (ap1 wfRedFull t) (ap2 pi (ap1 wfRed t) (ap1 wfFunRec t)) fh (l4 fh (wfRedFull_eq t))) d)
  splitR4 : (fh : Formula) (t : Term) ->
    Deriv (imp negLeaf (imp htagA2 (imp fh (imp PA (eqF (ap1 wfRedFull t) O))))) ->
    Deriv (imp negLeaf (imp htagA2 (imp fh (imp PA (eqF (ap1 wfFunRec t) O)))))
  splitR4 fh t d =
    ap4c (l4 fh (piZeroR_imp (ap1 wfRed t) (ap1 wfFunRec t)))
      (G4trans (ap2 pi (ap1 wfRed t) (ap1 wfFunRec t)) (ap1 wfRedFull t) O fh
        (G4sym (ap1 wfRedFull t) (ap2 pi (ap1 wfRed t) (ap1 wfFunRec t)) fh (l4 fh (wfRedFull_eq t))) d)

  tmAp2Arg1Imp : (gg a a' b : Term) -> Deriv (imp (eqF a a') (eqF (tmAp2 gg a b) (tmAp2 gg a' b)))
  tmAp2Arg1Imp gg a a' b =
    impCongR Pair (ap2 Pair gg (ap2 Pair a b)) (ap2 Pair gg (ap2 Pair a' b)) tgAp2
      (impCongR Pair (ap2 Pair a b) (ap2 Pair a' b) gg (impCongL Pair a a' b (identP (eqF a a'))))
  tmAp2Arg2Imp : (gg a b b' : Term) -> Deriv (imp (eqF b b') (eqF (tmAp2 gg a b) (tmAp2 gg a b')))
  tmAp2Arg2Imp gg a b b' =
    impCongR Pair (ap2 Pair gg (ap2 Pair a b)) (ap2 Pair gg (ap2 Pair a b')) tgAp2
      (impCongR Pair (ap2 Pair a b) (ap2 Pair a b') gg (impCongR Pair b b' a (identP (eqF b b'))))
  tmAp2HeadImp : (f g a b : Term) -> Deriv (imp (eqF f g) (eqF (tmAp2 f a b) (tmAp2 g a b)))
  tmAp2HeadImp f g a b =
    impCongR Pair (ap2 Pair f (ap2 Pair a b)) (ap2 Pair g (ap2 Pair a b)) tgAp2
      (impCongL Pair f g (ap2 Pair a b) (identP (eqF f g)))

  G4Ap2R : (gg a a' b b' : Term) (fh : Formula) ->
    Deriv (imp negLeaf (imp htagA2 (imp fh (imp PA (eqF a a'))))) ->
    Deriv (imp negLeaf (imp htagA2 (imp fh (imp PA (eqF b b'))))) ->
    Deriv (imp negLeaf (imp htagA2 (imp fh (imp PA (eqF (tmAp2 gg a b) (tmAp2 gg a' b'))))))
  G4Ap2R gg a a' b b' fh dA dB =
    G4trans (tmAp2 gg a b) (tmAp2 gg a' b) (tmAp2 gg a' b') fh
      (ap4c (l4 fh (tmAp2Arg1Imp gg a a' b)) dA)
      (ap4c (l4 fh (tmAp2Arg2Imp gg a' b b')) dB)
  G4Ap2Head : (f g a b : Term) (fh : Formula) ->
    Deriv (imp negLeaf (imp htagA2 (imp fh (imp PA (eqF f g))))) ->
    Deriv (imp negLeaf (imp htagA2 (imp fh (imp PA (eqF (tmAp2 f a b) (tmAp2 g a b))))))
  G4Ap2Head f g a b fh d = ap4c (l4 fh (tmAp2HeadImp f g a b)) d
  G4Ap2Arg1 : (gg a a' b : Term) (fh : Formula) ->
    Deriv (imp negLeaf (imp htagA2 (imp fh (imp PA (eqF a a'))))) ->
    Deriv (imp negLeaf (imp htagA2 (imp fh (imp PA (eqF (tmAp2 gg a b) (tmAp2 gg a' b))))))
  G4Ap2Arg1 gg a a' b fh d = ap4c (l4 fh (tmAp2Arg1Imp gg a a' b)) d
  G4Ap2Arg2 : (gg a b b' : Term) (fh : Formula) ->
    Deriv (imp negLeaf (imp htagA2 (imp fh (imp PA (eqF b b'))))) ->
    Deriv (imp negLeaf (imp htagA2 (imp fh (imp PA (eqF (tmAp2 gg a b) (tmAp2 gg a b'))))))
  G4Ap2Arg2 gg a b b' fh d = ap4c (l4 fh (tmAp2Arg2Imp gg a b b')) d

  fromFh : (fh : Formula) {X : Formula} -> Deriv (imp fh X) ->
    Deriv (imp negLeaf (imp htagA2 (imp fh (imp PA X))))
  fromFh fh d = ap4c (l4 fh d) (get4c negLeaf htagA2 fh PA)

  gPiL4 : (fh : Formula) (X Y : Term) ->
    Deriv (imp negLeaf (imp htagA2 (imp fh (imp PA (eqF (ap2 pi X Y) O))))) ->
    Deriv (imp negLeaf (imp htagA2 (imp fh (imp PA (eqF X O)))))
  gPiL4 fh X Y d = ap4c (l4 fh (piZeroL_imp X Y)) d
  gPiR4 : (fh : Formula) (X Y : Term) ->
    Deriv (imp negLeaf (imp htagA2 (imp fh (imp PA (eqF (ap2 pi X Y) O))))) ->
    Deriv (imp negLeaf (imp htagA2 (imp fh (imp PA (eqF Y O)))))
  gPiR4 fh X Y d = ap4c (l4 fh (piZeroR_imp X Y)) d

  assembleConj34 : (fh : Formula) ->
    Deriv (imp negLeaf (imp htagA2 (imp fh (imp PA (eqF (ap1 wfRedFull (ap1 triF sK)) O))))) ->
    Deriv (imp negLeaf (imp htagA2 (imp fh (imp PA (eqF (ap1 srcF (ap1 triF sK)) (ap1 tgtF sK)))))) ->
    Deriv (imp negLeaf (imp htagA2 (imp fh (imp PA (eqF (ap1 tgtF (ap1 triF sK)) (ap1 devF (ap1 srcF sK))))))) ->
    Deriv (imp negLeaf (imp htagA2 (imp fh (imp PA Bgoal))))
  assembleConj34 fh factV factS factT =
    let eqS = eqDecO (ap1 srcF (ap1 triF sK)) (ap1 tgtF sK)
        eqT = eqDecO (ap1 tgtF (ap1 triF sK)) (ap1 devF (ap1 srcF sK))
        sO = ap4c (l4 fh (eqDecO_complete_imp (ap1 srcF (ap1 triF sK)) (ap1 tgtF sK))) factS
        tO = ap4c (l4 fh (eqDecO_complete_imp (ap1 tgtF (ap1 triF sK)) (ap1 devF (ap1 srcF sK)))) factT
        inner = ap4c (ap4c (l4 fh (sigmaBothO_imp eqS eqT)) sO) tO
        outer = ap4c (ap4c (l4 fh (sigmaBothO_imp (ap1 wfRedFull (ap1 triF sK)) (ap2 sigma eqS eqT))) factV) inner
    in G4trans (ap1 conj3 sK) (ap2 sigma (ap1 wfRedFull (ap1 triF sK)) (ap2 sigma eqS eqT)) O fh
         (l4 fh (conj3_unfold sK)) outer

------------------------------------------------------------------------
-- glue_ap2c_v :  funhead = 7 (cProj).  triF sK = derV (triF (pL sK)) (triF (pR sK)).

glue_ap2c_v : Deriv (imp negLeaf (imp htagA2 (imp (eqF (ap1 Fst (funP sK)) (natCode 7)) (imp PA Bgoal))))
glue_ap2c_v =
  let fh = eqF (ap1 Fst (funP sK)) (natCode 7)
      dL = pL sK
      dR = pR sK
      X1 = ap1 triF dL
      X2 = ap1 triF dR
      fp = funP sK
      Y2 = ap1 devF (ap1 srcF dR)
      Dv = derV X1 X2
      leqL = rebound dL (pLValueBound sK ne_sK)
      leqR = rebound dR (pRValueBound sK ne_sK)
      -- wfFunRec sK = pi (isF2 fp)(pi (funValid fp)(pi (wfFunRec dL)(wfFunRec dR))).
      tail2 = ap2 pi (ap1 wfFunRec dL) (ap1 wfFunRec dR)
      tail1 = ap2 pi (funValid fp) tail2
      wfFunRecEq = addFunPA4 fh (wfFunRec_op_ap2c_imp sK ne_sK)
      wfFunPiEq = G4trans (ap2 pi (isF2 fp) tail1) (ap1 wfFunRec sK) O fh
                    (G4sym (ap1 wfFunRec sK) (ap2 pi (isF2 fp) tail1) fh wfFunRecEq) (wfFunSK4 fh)
      rest1 = gPiR4 fh (isF2 fp) tail1 wfFunPiEq
      funValidFunPO = gPiL4 fh (funValid fp) tail2 rest1
      rest2 = gPiR4 fh (funValid fp) tail2 rest1
      wfFunDLO = gPiL4 fh (ap1 wfFunRec dL) (ap1 wfFunRec dR) rest2
      wfFunDRO = gPiR4 fh (ap1 wfFunRec dL) (ap1 wfFunRec dR) rest2
      -- reconstruct fp = cProj (leaf, funhead 7).
      wfFunOpV = fromFh fh (wfFun_op_v_himp fp)
      funValidFFunPO = G4trans (ap1 funValidF fp) (ap1 wfFun fp) O fh
                         (G4sym (ap1 wfFun fp) (ap1 funValidF fp) fh wfFunOpV) funValidFunPO
      eqdOEq = ap4c (l4 fh (prependEqLeft (eqDecO fp (ap1 recon fp)) (ap1 funValidF fp) O
                              (ruleSym (funValidF_eq fp)))) funValidFFunPO
      reconEqV = ap4c (fromFh fh (funValid_v_imp fp)) eqdOEq
      -- child wfRed.
      wfRedPiEq = G4trans (ap2 pi (ap1 wfRed dL) (ap1 wfRed dR)) (ap1 wfRed sK) O fh
                    (G4sym (ap1 wfRed sK) (ap2 pi (ap1 wfRed dL) (ap1 wfRed dR)) fh
                      (addFunPA4 fh (wfRed_op_ap2c_imp sK ne_sK)))
                    (wfRedSK4 fh)
      wfRedDLO = gPiL4 fh (ap1 wfRed dL) (ap1 wfRed dR) wfRedPiEq
      wfRedDRO = gPiR4 fh (ap1 wfRed dL) (ap1 wfRed dR) wfRedPiEq
      childCjL = mkChildCjFull4 fh dL leqL (mkWfRedFull4 fh dL wfRedDLO wfFunDLO)
      childCjR = mkChildCjFull4 fh dR leqR (mkWfRedFull4 fh dR wfRedDRO wfFunDRO)
      cVL = ap4c (l4 fh (childV_imp dL)) childCjL
      cSL = ap4c (l4 fh (childS_imp dL)) childCjL
      cVR = ap4c (l4 fh (childV_imp dR)) childCjR
      cSR = ap4c (l4 fh (childS_imp dR)) childCjR
      cTR = ap4c (l4 fh (childT_imp dR)) childCjR
      cVLwfRed = splitL4 fh X1 cVL
      cVLwfFun = splitR4 fh X1 cVL
      cVRwfRed = splitL4 fh X2 cVR
      cVRwfFun = splitR4 fh X2 cVR
      -- opaque eqs.
      triEq = addPA4 fh (triF_op_ap2c_v_imp sK ne_sK)
      srcEqSK = addFunPA4 fh (srcF_op_ap2c_imp sK ne_sK)
      tgtEqSK = addFunPA4 fh (tgtF_op_ap2c_imp sK ne_sK)
      -- V-fact.
      wfRedTriSK = G4trans (ap1 wfRed (ap1 triF sK)) (ap1 wfRed Dv) O fh
                     (G4cong wfRed (ap1 triF sK) Dv fh triEq)
                     (G4trans (ap1 wfRed Dv) (ap2 pi (ap1 wfRed X1) (ap1 wfRed X2)) O fh
                       (l4 fh (wfRed_rV X1 X2)) (piB4 fh (ap1 wfRed X1) (ap1 wfRed X2) cVLwfRed cVRwfRed))
      wfFunTriSK = G4trans (ap1 wfFunRec (ap1 triF sK)) (ap1 wfFunRec Dv) O fh
                     (G4cong wfFunRec (ap1 triF sK) Dv fh triEq)
                     (G4trans (ap1 wfFunRec Dv) (ap2 pi (ap1 wfFunRec X1) (ap1 wfFunRec X2)) O fh
                       (l4 fh (wfFunRec_rV X1 X2)) (piB4 fh (ap1 wfFunRec X1) (ap1 wfFunRec X2) cVLwfFun cVRwfFun))
      factV = mkWfRedFull4 fh (ap1 triF sK) wfRedTriSK wfFunTriSK
      -- S-fact.
      srcTriEq = G4trans (ap1 srcF (ap1 triF sK)) (ap1 srcF Dv) (tmAp2 cProj (ap1 tgtF dL) (ap1 tgtF dR)) fh
                   (G4cong srcF (ap1 triF sK) Dv fh triEq)
                   (G4trans (ap1 srcF Dv) (tmAp2 cProj (ap1 srcF X1) (ap1 srcF X2))
                     (tmAp2 cProj (ap1 tgtF dL) (ap1 tgtF dR)) fh
                     (l4 fh (srcF_rV X1 X2))
                     (G4Ap2R cProj (ap1 srcF X1) (ap1 tgtF dL) (ap1 srcF X2) (ap1 tgtF dR) fh cSL cSR))
      tgtEqSKp = G4trans (ap1 tgtF sK) (tmAp2 fp (ap1 tgtF dL) (ap1 tgtF dR))
                   (tmAp2 cProj (ap1 tgtF dL) (ap1 tgtF dR)) fh
                   tgtEqSK (G4Ap2Head fp cProj (ap1 tgtF dL) (ap1 tgtF dR) fh reconEqV)
      factS = G4trans (ap1 srcF (ap1 triF sK)) (tmAp2 cProj (ap1 tgtF dL) (ap1 tgtF dR)) (ap1 tgtF sK) fh
                srcTriEq (G4sym (ap1 tgtF sK) (tmAp2 cProj (ap1 tgtF dL) (ap1 tgtF dR)) fh tgtEqSKp)
      -- T-fact.
      srcEqSKp = G4trans (ap1 srcF sK) (tmAp2 fp (ap1 srcF dL) (ap1 srcF dR))
                   (tmAp2 cProj (ap1 srcF dL) (ap1 srcF dR)) fh
                   srcEqSK (G4Ap2Head fp cProj (ap1 srcF dL) (ap1 srcF dR) fh reconEqV)
      devSrcEq = G4trans (ap1 devF (ap1 srcF sK)) (ap1 devF (tmAp2 cProj (ap1 srcF dL) (ap1 srcF dR))) Y2 fh
                   (G4cong devF (ap1 srcF sK) (tmAp2 cProj (ap1 srcF dL) (ap1 srcF dR)) fh srcEqSKp)
                   (l4 fh (devF_ap2_v_h cProj (ap1 srcF dL) (ap1 srcF dR) hd_cProj))
      factT = G4trans (ap1 tgtF (ap1 triF sK)) Y2 (ap1 devF (ap1 srcF sK)) fh
                (G4trans (ap1 tgtF (ap1 triF sK)) (ap1 tgtF Dv) Y2 fh
                  (G4cong tgtF (ap1 triF sK) Dv fh triEq)
                  (G4trans (ap1 tgtF Dv) (ap1 tgtF X2) Y2 fh (l4 fh (tgtF_rV X1 X2)) cTR))
                (G4sym (ap1 devF (ap1 srcF sK)) Y2 fh devSrcEq)
  in assembleConj34 fh factV factS factT

------------------------------------------------------------------------
-- glue_ap2c_Rb :  funhead = 8 (cRec), pR head = 1 (reflO base).  The R-base
-- contraction:  triF sK = derRb g h1 h2 (triF (pL sK))  (after fp = cRec g h1 h2).
-- Folds the two funhead conditions into  fh = Cnj funhead8 pRhead1  and reuses
-- the depth-4 kit.

private
  -- object-level uncurry:  (A -> B -> Cf)  ->  (Cnj A B -> Cf) .
  uncurryImp : (A B Cf : Formula) -> Deriv (imp (imp A (imp B Cf)) (imp (Cnj A B) Cf))
  uncurryImp A B Cf =
    let hD = axK (imp A (imp B Cf)) (Cnj A B)
        hA = liftP (imp A (imp B Cf)) (cnjL A B)
        hB = liftP (imp A (imp B Cf)) (cnjR A B)
    in ap2c (ap2c hD hA) hB

  tmAp1ArgImp : (f a b : Term) -> Deriv (imp (eqF a b) (eqF (tmAp1 f a) (tmAp1 f b)))
  tmAp1ArgImp f a b =
    impCongR Pair (ap2 Pair f a) (ap2 Pair f b) tgAp1 (impCongR Pair a b f (identP (eqF a b)))
  G4TmAp1 : (f a b : Term) (fh : Formula) ->
    Deriv (imp negLeaf (imp htagA2 (imp fh (imp PA (eqF a b))))) ->
    Deriv (imp negLeaf (imp htagA2 (imp fh (imp PA (eqF (tmAp1 f a) (tmAp1 f b))))))
  G4TmAp1 f a b fh d = ap4c (lift4 negLeaf htagA2 fh PA (tmAp1ArgImp f a b)) d

  tmAp1HeadImp : (f g Yv : Term) -> Deriv (imp (eqF f g) (eqF (tmAp1 f Yv) (tmAp1 g Yv)))
  tmAp1HeadImp f g Yv =
    impCongR Pair (ap2 Pair f Yv) (ap2 Pair g Yv) tgAp1 (impCongL Pair f g Yv (identP (eqF f g)))
  G4TmAp1Head : (f g Yv : Term) (fh : Formula) ->
    Deriv (imp negLeaf (imp htagA2 (imp fh (imp PA (eqF f g))))) ->
    Deriv (imp negLeaf (imp htagA2 (imp fh (imp PA (eqF (tmAp1 f Yv) (tmAp1 g Yv))))))
  G4TmAp1Head f g Yv fh d = ap4c (lift4 negLeaf htagA2 fh PA (tmAp1HeadImp f g Yv)) d

glue_ap2c_Rb : Deriv (imp negLeaf (imp htagA2
                 (imp (Cnj (eqF (ap1 Fst (funP sK)) (natCode 8)) (eqF (ap1 Fst (pR sK)) (natCode 1)))
                      (imp PA Bgoal))))
glue_ap2c_Rb =
  let funhead8 = eqF (ap1 Fst (funP sK)) (natCode 8)
      pRhead1 = eqF (ap1 Fst (pR sK)) (natCode 1)
      fh = Cnj funhead8 pRhead1
      dL = pL sK
      dR = pR sK
      X1 = ap1 triF dL
      fp = funP sK
      g = cG fp
      h1 = cH1 fp
      h2 = cH2 fp
      cc = cRec g h1 h2
      Y = ap1 devF (ap1 srcF dL)
      Drb = derRb g h1 h2 X1
      leqL = rebound dL (pLValueBound sK ne_sK)
      -- extract wfFun fp = O and wfFunRec dL = O.
      tail2 = ap2 pi (ap1 wfFunRec dL) (ap1 wfFunRec dR)
      tail1 = ap2 pi (funValid fp) tail2
      wfFunRecEq = addFunPA4 fh (wfFunRec_op_ap2c_imp sK ne_sK)
      wfFunPiEq = G4trans (ap2 pi (isF2 fp) tail1) (ap1 wfFunRec sK) O fh
                    (G4sym (ap1 wfFunRec sK) (ap2 pi (isF2 fp) tail1) fh wfFunRecEq) (wfFunSK4 fh)
      rest1 = gPiR4 fh (isF2 fp) tail1 wfFunPiEq
      funValidFunPO = gPiL4 fh (funValid fp) tail2 rest1
      rest2 = gPiR4 fh (funValid fp) tail2 rest1
      wfFunDLO = gPiL4 fh (ap1 wfFunRec dL) (ap1 wfFunRec dR) rest2
      -- funValidF fp = O (head conjunct).
      wfFunRHead = fromFh fh (compI (cnjL funhead8 pRhead1) (wfFun_op_R_head_himp fp))
      piFunValidO = G4trans (ap2 pi (ap1 funValidF fp) (restRval fp)) (ap1 wfFun fp) O fh
                      (G4sym (ap1 wfFun fp) (ap2 pi (ap1 funValidF fp) (restRval fp)) fh wfFunRHead)
                      funValidFunPO
      funValidFfpO = gPiL4 fh (ap1 funValidF fp) (restRval fp) piFunValidO
      eqdOEq = ap4c (l4 fh (prependEqLeft (eqDecO fp (ap1 recon fp)) (ap1 funValidF fp) O
                              (ruleSym (funValidF_eq fp)))) funValidFfpO
      reconEqR = ap4c (fromFh fh (compI (cnjL funhead8 pRhead1) (funValid_R_imp fp))) eqdOEq
      -- child dL validity.
      wfRedPiEq = G4trans (ap2 pi (ap1 wfRed dL) (ap1 wfRed dR)) (ap1 wfRed sK) O fh
                    (G4sym (ap1 wfRed sK) (ap2 pi (ap1 wfRed dL) (ap1 wfRed dR)) fh
                      (addFunPA4 fh (wfRed_op_ap2c_imp sK ne_sK)))
                    (wfRedSK4 fh)
      wfRedDLO = gPiL4 fh (ap1 wfRed dL) (ap1 wfRed dR) wfRedPiEq
      childCjL = mkChildCjFull4 fh dL leqL (mkWfRedFull4 fh dL wfRedDLO wfFunDLO)
      cVL = ap4c (l4 fh (childV_imp dL)) childCjL
      cSL = ap4c (l4 fh (childS_imp dL)) childCjL
      cTL = ap4c (l4 fh (childT_imp dL)) childCjL
      cVLwfRed = splitL4 fh X1 cVL
      cVLwfFun = splitR4 fh X1 cVL
      -- reflO facts for dR.
      srcDRtmO = fromFh fh (compI (cnjR funhead8 pRhead1) (srcF_reflO_himp dR))
      tgtDRtmO = fromFh fh (compI (cnjR funhead8 pRhead1) (tgtF_reflO_himp dR))
      -- opaque eqs.
      srcEqSK = addFunPA4 fh (srcF_op_ap2c_imp sK ne_sK)
      tgtEqSK = addFunPA4 fh (tgtF_op_ap2c_imp sK ne_sK)
      foldRb = ap2c (lift2 negLeaf htagA2
                 (uncurryImp funhead8 pRhead1 (eqF (ap1 triF sK) (binNode (ap2 Pair (natCode 7) (ap1 Snd fp)) X1 derLeaf))))
                 (triF_op_ap2c_Rb_imp sK ne_sK)
      triEqRaw = addPA4 fh foldRb
      -- residual binNode -> derRb g h1 h2 X1.
      sndFpEq = G4trans (ap1 Snd fp) (ap1 Snd cc) (bun3 g h1 h2) fh
                  (G4cong Snd fp cc fh reconEqR)
                  (l4 fh (axSnd (natCode 8) (bun3 g h1 h2)))
      BIGa = ap2 Pair (ap2 Pair (natCode 7) (ap1 Snd fp)) (ap2 Pair X1 derLeaf)
      BIGb = ap2 Pair (ap2 Pair (natCode 7) (bun3 g h1 h2)) (ap2 Pair X1 derLeaf)
      labConvImp = impCongR Pair BIGa BIGb (natCode 2)
                     (impCongL Pair (ap2 Pair (natCode 7) (ap1 Snd fp)) (ap2 Pair (natCode 7) (bun3 g h1 h2)) (ap2 Pair X1 derLeaf)
                       (impCongR Pair (ap1 Snd fp) (bun3 g h1 h2) (natCode 7) (identP (eqF (ap1 Snd fp) (bun3 g h1 h2)))))
      triEqDerRb = G4trans (ap1 triF sK) (binNode (ap2 Pair (natCode 7) (ap1 Snd fp)) X1 derLeaf) Drb fh
                     triEqRaw (ap4c (l4 fh labConvImp) sndFpEq)
      -- V-fact.
      wfFunccO = G4trans (ap1 wfFun cc) (ap1 wfFun fp) O fh
                   (G4cong wfFun cc fp fh (G4sym fp cc fh reconEqR)) funValidFunPO
      wfRedTriSK = G4trans (ap1 wfRed (ap1 triF sK)) (ap1 wfRed Drb) O fh
                     (G4cong wfRed (ap1 triF sK) Drb fh triEqDerRb)
                     (G4trans (ap1 wfRed Drb) (ap1 wfRed X1) O fh (l4 fh (wfRed_rRb g h1 h2 X1)) cVLwfRed)
      wfFunTriSK = G4trans (ap1 wfFunRec (ap1 triF sK)) (ap1 wfFunRec Drb) O fh
                     (G4cong wfFunRec (ap1 triF sK) Drb fh triEqDerRb)
                     (G4trans (ap1 wfFunRec Drb) (ap2 pi (ap1 wfFun cc) (ap1 wfFunRec X1)) O fh
                       (l4 fh (wfFunRec_rRb g h1 h2 X1))
                       (piB4 fh (ap1 wfFun cc) (ap1 wfFunRec X1) wfFunccO cVLwfFun))
      factV = mkWfRedFull4 fh (ap1 triF sK) wfRedTriSK wfFunTriSK
      -- S-fact.
      srcTriEq = G4trans (ap1 srcF (ap1 triF sK)) (ap1 srcF Drb) (tmAp2 cc (ap1 tgtF dL) tmO) fh
                   (G4cong srcF (ap1 triF sK) Drb fh triEqDerRb)
                   (G4trans (ap1 srcF Drb) (tmAp2 cc (ap1 srcF X1) tmO) (tmAp2 cc (ap1 tgtF dL) tmO) fh
                     (l4 fh (srcF_rRb g h1 h2 X1))
                     (G4Ap2Arg1 cc (ap1 srcF X1) (ap1 tgtF dL) tmO fh cSL))
      tgtEqSKr = G4trans (ap1 tgtF sK) (tmAp2 fp (ap1 tgtF dL) (ap1 tgtF dR)) (tmAp2 cc (ap1 tgtF dL) tmO) fh
                   tgtEqSK
                   (G4trans (tmAp2 fp (ap1 tgtF dL) (ap1 tgtF dR)) (tmAp2 cc (ap1 tgtF dL) (ap1 tgtF dR)) (tmAp2 cc (ap1 tgtF dL) tmO) fh
                     (G4Ap2Head fp cc (ap1 tgtF dL) (ap1 tgtF dR) fh reconEqR)
                     (G4Ap2Arg2 cc (ap1 tgtF dL) (ap1 tgtF dR) tmO fh tgtDRtmO))
      factS = G4trans (ap1 srcF (ap1 triF sK)) (tmAp2 cc (ap1 tgtF dL) tmO) (ap1 tgtF sK) fh
                srcTriEq (G4sym (ap1 tgtF sK) (tmAp2 cc (ap1 tgtF dL) tmO) fh tgtEqSKr)
      -- T-fact.
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
      tgtTriEq = G4trans (ap1 tgtF (ap1 triF sK)) (ap1 tgtF Drb) (tmAp1 g Y) fh
                   (G4cong tgtF (ap1 triF sK) Drb fh triEqDerRb)
                   (G4trans (ap1 tgtF Drb) (tmAp1 g (ap1 tgtF X1)) (tmAp1 g Y) fh
                     (l4 fh (tgtF_rRb g h1 h2 X1)) (G4TmAp1 g (ap1 tgtF X1) Y fh cTL))
      factT = G4trans (ap1 tgtF (ap1 triF sK)) (tmAp1 g Y) (ap1 devF (ap1 srcF sK)) fh
                tgtTriEq (G4sym (ap1 devF (ap1 srcF sK)) (tmAp1 g Y) fh devSrcEq)
  in assembleConj34 fh factV factS factT
