{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.PrTriUGlueAp1c -- the ap1c-congruence GLUE for the full-PR CR dispatch.
-- An ap1c node sub-dispatches on the carried fun's head Fst(funP sK); each
-- funhead sub-case is a depth-4 glue over [negLeaf, htagA, funhead_k, PA]
-- (htagA = dtag sK = dgAp1c).  The leaf heads (o=4 / u=5 / s=3) reconstruct
-- funP = cZero/cId/cSuc via the imp-form leaf reconstruction (T4.PrWfFunLeafImp)
-- under the funhead hypothesis; the C head (6) is compound (wfFun_op_C).
--
-- This file: depth-4 ctx kit + the o/u/s sub-glues.  (C + the funhead caseElim
-- assembly follow.)
--
-- No holes, no postulates, no termination warnings (only the benign
-- RuleInst3:328 unreachable-clauses warning); --safe --without-K --exact-split.

module T4.PrTriUGlueAp1c where

open import T4.Base

open import T4.PrTriUGlue
  using ( sK ; PA ; negLeaf ; Bgoal ; ne_sK ; pa2a ; pa2phik ; rebound )
open import T4.DerCodeS using ( dtag ; pL )
open import T4.PrDerCode using ( derO ; derU ; dgAp1c ) renaming ( ap1c to dap1c )
open import T4.PrCodeObj using ( tmO ; tmAp1 ; cZero ; cId ; cSuc )
open import T4.PrWfRed using ( wfRed ; wfRed_rO ; wfRed_rU ; wfRed_ap1c )
open import T4.PrWfFunRec using ( wfFunRec ; funValid ; wfFunRec_rO ; wfFunRec_rU ; wfFunRec_ap1c )
open import T4.PrWfFun using ( wfFun ; isF1 ; wfFun_cSuc )
open import T4.PrWfFunShadow using ( isF1_codeF1 )
open import T4.PrTriShadow using ( f1S )
open import T4.PrWfRedFull using ( wfRedFull ; wfRedFull_eq ; piBothO )
open import T4.PrTri using ( triF )
open import T4.PrSrc using ( srcF ; srcF_rO ; srcF_rU ; srcF_ap1c )
open import T4.PrTgt using ( tgtF ; tgtF_rO ; tgtF_rU ; tgtF_ap1c )
open import T4.PrDev using ( devF )
open import T4.PrQCheckU using ( conj3 )
open import T4.PrQCheckProjU using ( PhiKU ; QofChildU )
open import T4.PrCRGlueU using ( conj3_unfold )
open import T4.PrCRGlueImpU
  using ( childV_imp ; childS_imp ; childT_imp ; eqDecO_complete_imp ; sigmaBothO_imp
        ; piBothO_imp ; piZeroL_imp ; piZeroR_imp )
open import T4.EqDecO using ( eqDecO )

open import T4.PrTriUOpaqueImp using ( triF_op_ap1c_o_imp ; triF_op_ap1c_u_imp ; triF_op_ap1c_s_imp )
open import T4.PrSrcUOpaqueImp using ( srcF_op_ap1c_imp )
open import T4.PrTgtUOpaqueImp using ( tgtF_op_ap1c_imp )
open import T4.PrWfRedUOpaqueImp using ( wfRed_op_ap1c_imp )
open import T4.PrWfFunRecUOpaqueImp using ( wfFunRec_op_ap1c_imp )
open import T4.PrDevByHead using ( devF_ap1_o_h ; devF_ap1_u_h ; devF_ap1_s_h ; devF_ap1_C_h ; gF ; h1F ; h2F )
open import T4.PrCodeObj using ( hd_cId ; hd_cZero ; hd_cSuc )

-- C-case (funhead = 6, compound) extras.
open import T4.PrTriUOpaqueImp using ( triF_op_ap1c_C_imp )
open import T4.PrSrc using ( srcF_rC )
open import T4.PrTgt using ( tgtF_rC )
open import T4.PrWfRed using ( wfRed_rC )
open import T4.PrWfFunRec using ( wfFunRec_rC )
open import T4.PrDerCode using ( derC ; bun3 ; derLeaf )
open import T4.BinTree using ( binNode )
open import T4.PrCodeObj using ( cComp ; hd_cComp ; compFun ; compH1 ; compH2 ; tgAp2 ; tmAp2 )
open import T4.PrFunValid using ( cG ; cH1 ; cH2 )
open import T4.PrWfFunLeafImp using ( restCval ; wfFun_op_C_head_himp ; funValid_C_imp )

open import T4.PrTgtUOpaque using ( funP )
open import T4.PrFunValidCanon using ( funValidF ; funValidF_eq )
open import T4.PrFunValid using ( recon )
open import T4.PrWfFunLeafImp
  using ( wfFun_op_o_himp ; wfFun_op_u_himp ; wfFun_op_s_himp
        ; funValid_o_imp ; funValid_u_imp ; funValid_s_imp )

open import T4.WfRedExtract using ( pLValueBound )
open import BRA3.Logic using ( prependEqLeft ; eqSymImp )
open import BRA3.Contrapositive using ( compI ; liftP ; identP )
open import T4.Thm12.ImpHelpers using ( impCong1 ; impCongR ; impCongL )
open import T4.PrCodeObj using ( tgAp1 )
open import T4.CtxKit
  using ( lift2 ; ap2c ; lift3 ; ap3c ; trans3c
        ; lift4 ; get4a ; get4b ; get4c ; get4d ; ap4c ; trans4c )

open import BRA3.Church using ( pi ; sigma )
open import BRA3.ChurchLeq using ( leq )

------------------------------------------------------------------------
-- Shared:  htagA = dtag sK = dgAp1c ;  Aform-extraction.

htagA : Formula
htagA = eqF (ap1 Fst (dtag sK)) dgAp1c

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
-- Depth-4 ctx kit over  [negLeaf, htagA, fh, PA] .  (fh = funhead.)

private
  -- bring a bare Deriv into the ctx.
  l4 : (fh : Formula) {X : Formula} -> Deriv X -> Deriv (imp negLeaf (imp htagA (imp fh (imp PA X))))
  l4 fh d = lift4 negLeaf htagA fh PA d

  G4cong : (f : Fun1) (a b : Term) (fh : Formula) ->
    Deriv (imp negLeaf (imp htagA (imp fh (imp PA (eqF a b))))) ->
    Deriv (imp negLeaf (imp htagA (imp fh (imp PA (eqF (ap1 f a) (ap1 f b))))))
  G4cong f a b fh d = ap4c (l4 fh (impCong1 f a b (identP (eqF a b)))) d

  G4sym : (a b : Term) (fh : Formula) ->
    Deriv (imp negLeaf (imp htagA (imp fh (imp PA (eqF a b))))) ->
    Deriv (imp negLeaf (imp htagA (imp fh (imp PA (eqF b a)))))
  G4sym a b fh d = ap4c (l4 fh (eqSymImp a b)) d

  G4trans : (a b c : Term) (fh : Formula) ->
    Deriv (imp negLeaf (imp htagA (imp fh (imp PA (eqF a b))))) ->
    Deriv (imp negLeaf (imp htagA (imp fh (imp PA (eqF b c))))) ->
    Deriv (imp negLeaf (imp htagA (imp fh (imp PA (eqF a c)))))
  G4trans a b c fh d e = trans4c a b c d e

  -- add PA innermost to a [negLeaf, htagA, fh] depth-3 fact (e.g. the opaque triF eq).
  addPA4 : (fh : Formula) {X : Formula} ->
    Deriv (imp negLeaf (imp htagA (imp fh X))) ->
    Deriv (imp negLeaf (imp htagA (imp fh (imp PA X))))
  addPA4 fh {X} d = ap3c (lift3 negLeaf htagA fh (axK X PA)) d

  -- lift a [negLeaf, htagA] depth-2 fact (src/tgt/wfRed/wfFunRec op-eqs) to the ctx.
  addFunPA4 : (fh : Formula) {X : Formula} ->
    Deriv (imp negLeaf (imp htagA X)) ->
    Deriv (imp negLeaf (imp htagA (imp fh (imp PA X))))
  addFunPA4 fh {X} d = ap2c (lift2 negLeaf htagA (compI (axK X PA) (axK (imp PA X) fh))) d

  -- validity facts in ctx (PA -> wfRed/wfFunRec sK = O).
  paA : (fh : Formula) -> Deriv (imp negLeaf (imp htagA (imp fh (imp PA Aform))))
  paA fh = ap4c (l4 fh pa2a) (get4d negLeaf htagA fh PA)
  wfRedSK4 : (fh : Formula) -> Deriv (imp negLeaf (imp htagA (imp fh (imp PA (eqF (ap1 wfRed sK) O)))))
  wfRedSK4 fh = ap4c (l4 fh afToWfRed) (paA fh)
  wfFunSK4 : (fh : Formula) -> Deriv (imp negLeaf (imp htagA (imp fh (imp PA (eqF (ap1 wfFunRec sK) O)))))
  wfFunSK4 fh = ap4c (l4 fh afToWfFun) (paA fh)

  piB4 : (fh : Formula) (X Y : Term) ->
    Deriv (imp negLeaf (imp htagA (imp fh (imp PA (eqF X O))))) ->
    Deriv (imp negLeaf (imp htagA (imp fh (imp PA (eqF Y O))))) ->
    Deriv (imp negLeaf (imp htagA (imp fh (imp PA (eqF (ap2 pi X Y) O)))))
  piB4 fh X Y dX dY = ap4c (ap4c (l4 fh (piBothO_imp X Y)) dX) dY

  mkWfRedFull4 : (fh : Formula) (t : Term) ->
    Deriv (imp negLeaf (imp htagA (imp fh (imp PA (eqF (ap1 wfRed t) O))))) ->
    Deriv (imp negLeaf (imp htagA (imp fh (imp PA (eqF (ap1 wfFunRec t) O))))) ->
    Deriv (imp negLeaf (imp htagA (imp fh (imp PA (eqF (ap1 wfRedFull t) O)))))
  mkWfRedFull4 fh t wr wf =
    G4trans (ap1 wfRedFull t) (ap2 pi (ap1 wfRed t) (ap1 wfFunRec t)) O fh
      (l4 fh (wfRedFull_eq t)) (piB4 fh (ap1 wfRed t) (ap1 wfFunRec t) wr wf)

  mkChildCjFull4 : (fh : Formula) (child : Term) -> Deriv (leq child (var 0)) ->
    Deriv (imp negLeaf (imp htagA (imp fh (imp PA (eqF (ap1 wfRedFull child) O))))) ->
    Deriv (imp negLeaf (imp htagA (imp fh (imp PA (eqF (ap1 conj3 child) O)))))
  mkChildCjFull4 fh child leqCh cvf =
    ap4c (ap4c (l4 fh (QofChildU child leqCh)) (ap4c (l4 fh pa2phik) (get4d negLeaf htagA fh PA))) cvf

  splitL4 : (fh : Formula) (t : Term) ->
    Deriv (imp negLeaf (imp htagA (imp fh (imp PA (eqF (ap1 wfRedFull t) O))))) ->
    Deriv (imp negLeaf (imp htagA (imp fh (imp PA (eqF (ap1 wfRed t) O)))))
  splitL4 fh t d =
    ap4c (l4 fh (piZeroL_imp (ap1 wfRed t) (ap1 wfFunRec t)))
      (G4trans (ap2 pi (ap1 wfRed t) (ap1 wfFunRec t)) (ap1 wfRedFull t) O fh
        (G4sym (ap1 wfRedFull t) (ap2 pi (ap1 wfRed t) (ap1 wfFunRec t)) fh (l4 fh (wfRedFull_eq t))) d)
  splitR4 : (fh : Formula) (t : Term) ->
    Deriv (imp negLeaf (imp htagA (imp fh (imp PA (eqF (ap1 wfRedFull t) O))))) ->
    Deriv (imp negLeaf (imp htagA (imp fh (imp PA (eqF (ap1 wfFunRec t) O)))))
  splitR4 fh t d =
    ap4c (l4 fh (piZeroR_imp (ap1 wfRed t) (ap1 wfFunRec t)))
      (G4trans (ap2 pi (ap1 wfRed t) (ap1 wfFunRec t)) (ap1 wfRedFull t) O fh
        (G4sym (ap1 wfRedFull t) (ap2 pi (ap1 wfRed t) (ap1 wfFunRec t)) fh (l4 fh (wfRedFull_eq t))) d)

  tmAp1ArgImp : (f a b : Term) -> Deriv (imp (eqF a b) (eqF (tmAp1 f a) (tmAp1 f b)))
  tmAp1ArgImp f a b =
    impCongR Pair (ap2 Pair f a) (ap2 Pair f b) tgAp1 (impCongR Pair a b f (identP (eqF a b)))
  G4TmAp1 : (f a b : Term) (fh : Formula) ->
    Deriv (imp negLeaf (imp htagA (imp fh (imp PA (eqF a b))))) ->
    Deriv (imp negLeaf (imp htagA (imp fh (imp PA (eqF (tmAp1 f a) (tmAp1 f b))))))
  G4TmAp1 f a b fh d = ap4c (l4 fh (tmAp1ArgImp f a b)) d

  tmAp1HeadImp : (f g Y : Term) -> Deriv (imp (eqF f g) (eqF (tmAp1 f Y) (tmAp1 g Y)))
  tmAp1HeadImp f g Y =
    impCongR Pair (ap2 Pair f Y) (ap2 Pair g Y) tgAp1 (impCongL Pair f g Y (identP (eqF f g)))
  G4TmAp1Head : (f g Y : Term) (fh : Formula) ->
    Deriv (imp negLeaf (imp htagA (imp fh (imp PA (eqF f g))))) ->
    Deriv (imp negLeaf (imp htagA (imp fh (imp PA (eqF (tmAp1 f Y) (tmAp1 g Y))))))
  G4TmAp1Head f g Y fh d = ap4c (l4 fh (tmAp1HeadImp f g Y)) d

  gPiL4 : (fh : Formula) (X Y : Term) ->
    Deriv (imp negLeaf (imp htagA (imp fh (imp PA (eqF (ap2 pi X Y) O))))) ->
    Deriv (imp negLeaf (imp htagA (imp fh (imp PA (eqF X O)))))
  gPiL4 fh X Y d = ap4c (l4 fh (piZeroL_imp X Y)) d
  gPiR4 : (fh : Formula) (X Y : Term) ->
    Deriv (imp negLeaf (imp htagA (imp fh (imp PA (eqF (ap2 pi X Y) O))))) ->
    Deriv (imp negLeaf (imp htagA (imp fh (imp PA (eqF Y O)))))
  gPiR4 fh X Y d = ap4c (l4 fh (piZeroR_imp X Y)) d

  -- bring an  imp fh X  fact (the leaf reconstruction) into the ctx.
  fromFh : (fh : Formula) {X : Formula} -> Deriv (imp fh X) ->
    Deriv (imp negLeaf (imp htagA (imp fh (imp PA X))))
  fromFh fh d = ap4c (l4 fh d) (get4c negLeaf htagA fh PA)

  assembleConj34 : (fh : Formula) ->
    Deriv (imp negLeaf (imp htagA (imp fh (imp PA (eqF (ap1 wfRedFull (ap1 triF sK)) O))))) ->
    Deriv (imp negLeaf (imp htagA (imp fh (imp PA (eqF (ap1 srcF (ap1 triF sK)) (ap1 tgtF sK)))))) ->
    Deriv (imp negLeaf (imp htagA (imp fh (imp PA (eqF (ap1 tgtF (ap1 triF sK)) (ap1 devF (ap1 srcF sK))))))) ->
    Deriv (imp negLeaf (imp htagA (imp fh (imp PA Bgoal))))
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
-- glue_ap1c_o :  funhead = 4 (cZero).  triF sK = derO (triF (pL sK)).

glue_ap1c_o : Deriv (imp negLeaf (imp htagA (imp (eqF (ap1 Fst (funP sK)) (natCode 4)) (imp PA Bgoal))))
glue_ap1c_o =
  let fh = eqF (ap1 Fst (funP sK)) (natCode 4)
      d  = pL sK
      X  = ap1 triF d
      fp = funP sK
      leqD = rebound d (pLValueBound sK ne_sK)
      -- wfFunRec sK = O  =>  pi (isF1 fp)(pi (funValid fp)(wfFunRec d)) = O.
      tail = ap2 pi (funValid fp) (ap1 wfFunRec d)
      wfFunRecEq = addFunPA4 fh (wfFunRec_op_ap1c_imp sK ne_sK)
      wfFunPiEq = G4trans (ap2 pi (isF1 fp) tail) (ap1 wfFunRec sK) O fh
                    (G4sym (ap1 wfFunRec sK) (ap2 pi (isF1 fp) tail) fh wfFunRecEq) (wfFunSK4 fh)
      restEq = gPiR4 fh (isF1 fp) tail wfFunPiEq
      funValidFunPO = gPiL4 fh (funValid fp) (ap1 wfFunRec d) restEq
      wfFunDO = gPiR4 fh (funValid fp) (ap1 wfFunRec d) restEq
      -- reconstruct fp = cZero.
      wfFunOpO_c = fromFh fh (wfFun_op_o_himp fp)
      funValidFFunPO = G4trans (ap1 funValidF fp) (ap1 wfFun fp) O fh
                         (G4sym (ap1 wfFun fp) (ap1 funValidF fp) fh wfFunOpO_c) funValidFunPO
      eqdOEq = ap4c (l4 fh (prependEqLeft (eqDecO fp (ap1 recon fp)) (ap1 funValidF fp) O
                              (ruleSym (funValidF_eq fp)))) funValidFFunPO
      reconEqO = ap4c (fromFh fh (funValid_o_imp fp)) eqdOEq
      -- child validity.
      wfRedDO = G4trans (ap1 wfRed d) (ap1 wfRed sK) O fh
                  (G4sym (ap1 wfRed sK) (ap1 wfRed d) fh (addFunPA4 fh (wfRed_op_ap1c_imp sK ne_sK)))
                  (wfRedSK4 fh)
      childCj = mkChildCjFull4 fh d leqD (mkWfRedFull4 fh d wfRedDO wfFunDO)
      cV = ap4c (l4 fh (childV_imp d)) childCj
      cS = ap4c (l4 fh (childS_imp d)) childCj
      cT = ap4c (l4 fh (childT_imp d)) childCj
      cVwfRed = splitL4 fh X cV
      cVwfFun = splitR4 fh X cV
      -- opaque eqs.
      triEq = addPA4 fh (triF_op_ap1c_o_imp sK ne_sK)
      srcEqSK = addFunPA4 fh (srcF_op_ap1c_imp sK ne_sK)
      tgtEqSK = addFunPA4 fh (tgtF_op_ap1c_imp sK ne_sK)
      -- V-fact.
      wfRedTriSK = G4trans (ap1 wfRed (ap1 triF sK)) (ap1 wfRed (derO X)) O fh
                     (G4cong wfRed (ap1 triF sK) (derO X) fh triEq)
                     (G4trans (ap1 wfRed (derO X)) (ap1 wfRed X) O fh (l4 fh (wfRed_rO X)) cVwfRed)
      wfFunTriSK = G4trans (ap1 wfFunRec (ap1 triF sK)) (ap1 wfFunRec (derO X)) O fh
                     (G4cong wfFunRec (ap1 triF sK) (derO X) fh triEq)
                     (G4trans (ap1 wfFunRec (derO X)) (ap1 wfFunRec X) O fh (l4 fh (wfFunRec_rO X)) cVwfFun)
      factV = mkWfRedFull4 fh (ap1 triF sK) wfRedTriSK wfFunTriSK
      -- S-fact.
      srcTriEq = G4trans (ap1 srcF (ap1 triF sK)) (ap1 srcF (derO X)) (tmAp1 cZero (ap1 tgtF d)) fh
                   (G4cong srcF (ap1 triF sK) (derO X) fh triEq)
                   (G4trans (ap1 srcF (derO X)) (tmAp1 cZero (ap1 srcF X)) (tmAp1 cZero (ap1 tgtF d)) fh
                     (l4 fh (srcF_rO X)) (G4TmAp1 cZero (ap1 srcF X) (ap1 tgtF d) fh cS))
      tgtEqSKz = G4trans (ap1 tgtF sK) (tmAp1 fp (ap1 tgtF d)) (tmAp1 cZero (ap1 tgtF d)) fh
                   tgtEqSK (G4TmAp1Head fp cZero (ap1 tgtF d) fh reconEqO)
      factS = G4trans (ap1 srcF (ap1 triF sK)) (tmAp1 cZero (ap1 tgtF d)) (ap1 tgtF sK) fh
                srcTriEq (G4sym (ap1 tgtF sK) (tmAp1 cZero (ap1 tgtF d)) fh tgtEqSKz)
      -- T-fact.
      srcEqSKz = G4trans (ap1 srcF sK) (tmAp1 fp (ap1 srcF d)) (tmAp1 cZero (ap1 srcF d)) fh
                   srcEqSK (G4TmAp1Head fp cZero (ap1 srcF d) fh reconEqO)
      devSrcEq = G4trans (ap1 devF (ap1 srcF sK)) (ap1 devF (tmAp1 cZero (ap1 srcF d))) tmO fh
                   (G4cong devF (ap1 srcF sK) (tmAp1 cZero (ap1 srcF d)) fh srcEqSKz)
                   (l4 fh (devF_ap1_o_h cZero (ap1 srcF d) hd_cZero))
      factT = G4trans (ap1 tgtF (ap1 triF sK)) tmO (ap1 devF (ap1 srcF sK)) fh
                (G4trans (ap1 tgtF (ap1 triF sK)) (ap1 tgtF (derO X)) tmO fh
                  (G4cong tgtF (ap1 triF sK) (derO X) fh triEq) (l4 fh (tgtF_rO X)))
                (G4sym (ap1 devF (ap1 srcF sK)) tmO fh devSrcEq)
  in assembleConj34 fh factV factS factT

------------------------------------------------------------------------
-- glue_ap1c_u :  funhead = 5 (cId).  triF sK = derU (triF (pL sK)).

glue_ap1c_u : Deriv (imp negLeaf (imp htagA (imp (eqF (ap1 Fst (funP sK)) (natCode 5)) (imp PA Bgoal))))
glue_ap1c_u =
  let fh = eqF (ap1 Fst (funP sK)) (natCode 5)
      d  = pL sK
      X  = ap1 triF d
      fp = funP sK
      Y  = ap1 devF (ap1 srcF d)
      leqD = rebound d (pLValueBound sK ne_sK)
      tail = ap2 pi (funValid fp) (ap1 wfFunRec d)
      wfFunRecEq = addFunPA4 fh (wfFunRec_op_ap1c_imp sK ne_sK)
      wfFunPiEq = G4trans (ap2 pi (isF1 fp) tail) (ap1 wfFunRec sK) O fh
                    (G4sym (ap1 wfFunRec sK) (ap2 pi (isF1 fp) tail) fh wfFunRecEq) (wfFunSK4 fh)
      restEq = gPiR4 fh (isF1 fp) tail wfFunPiEq
      funValidFunPO = gPiL4 fh (funValid fp) (ap1 wfFunRec d) restEq
      wfFunDO = gPiR4 fh (funValid fp) (ap1 wfFunRec d) restEq
      wfFunOpO_c = fromFh fh (wfFun_op_u_himp fp)
      funValidFFunPO = G4trans (ap1 funValidF fp) (ap1 wfFun fp) O fh
                         (G4sym (ap1 wfFun fp) (ap1 funValidF fp) fh wfFunOpO_c) funValidFunPO
      eqdOEq = ap4c (l4 fh (prependEqLeft (eqDecO fp (ap1 recon fp)) (ap1 funValidF fp) O
                              (ruleSym (funValidF_eq fp)))) funValidFFunPO
      reconEqO = ap4c (fromFh fh (funValid_u_imp fp)) eqdOEq
      wfRedDO = G4trans (ap1 wfRed d) (ap1 wfRed sK) O fh
                  (G4sym (ap1 wfRed sK) (ap1 wfRed d) fh (addFunPA4 fh (wfRed_op_ap1c_imp sK ne_sK)))
                  (wfRedSK4 fh)
      childCj = mkChildCjFull4 fh d leqD (mkWfRedFull4 fh d wfRedDO wfFunDO)
      cV = ap4c (l4 fh (childV_imp d)) childCj
      cS = ap4c (l4 fh (childS_imp d)) childCj
      cT = ap4c (l4 fh (childT_imp d)) childCj
      cVwfRed = splitL4 fh X cV
      cVwfFun = splitR4 fh X cV
      triEq = addPA4 fh (triF_op_ap1c_u_imp sK ne_sK)
      srcEqSK = addFunPA4 fh (srcF_op_ap1c_imp sK ne_sK)
      tgtEqSK = addFunPA4 fh (tgtF_op_ap1c_imp sK ne_sK)
      wfRedTriSK = G4trans (ap1 wfRed (ap1 triF sK)) (ap1 wfRed (derU X)) O fh
                     (G4cong wfRed (ap1 triF sK) (derU X) fh triEq)
                     (G4trans (ap1 wfRed (derU X)) (ap1 wfRed X) O fh (l4 fh (wfRed_rU X)) cVwfRed)
      wfFunTriSK = G4trans (ap1 wfFunRec (ap1 triF sK)) (ap1 wfFunRec (derU X)) O fh
                     (G4cong wfFunRec (ap1 triF sK) (derU X) fh triEq)
                     (G4trans (ap1 wfFunRec (derU X)) (ap1 wfFunRec X) O fh (l4 fh (wfFunRec_rU X)) cVwfFun)
      factV = mkWfRedFull4 fh (ap1 triF sK) wfRedTriSK wfFunTriSK
      srcTriEq = G4trans (ap1 srcF (ap1 triF sK)) (ap1 srcF (derU X)) (tmAp1 cId (ap1 tgtF d)) fh
                   (G4cong srcF (ap1 triF sK) (derU X) fh triEq)
                   (G4trans (ap1 srcF (derU X)) (tmAp1 cId (ap1 srcF X)) (tmAp1 cId (ap1 tgtF d)) fh
                     (l4 fh (srcF_rU X)) (G4TmAp1 cId (ap1 srcF X) (ap1 tgtF d) fh cS))
      tgtEqSKz = G4trans (ap1 tgtF sK) (tmAp1 fp (ap1 tgtF d)) (tmAp1 cId (ap1 tgtF d)) fh
                   tgtEqSK (G4TmAp1Head fp cId (ap1 tgtF d) fh reconEqO)
      factS = G4trans (ap1 srcF (ap1 triF sK)) (tmAp1 cId (ap1 tgtF d)) (ap1 tgtF sK) fh
                srcTriEq (G4sym (ap1 tgtF sK) (tmAp1 cId (ap1 tgtF d)) fh tgtEqSKz)
      srcEqSKz = G4trans (ap1 srcF sK) (tmAp1 fp (ap1 srcF d)) (tmAp1 cId (ap1 srcF d)) fh
                   srcEqSK (G4TmAp1Head fp cId (ap1 srcF d) fh reconEqO)
      devSrcEq = G4trans (ap1 devF (ap1 srcF sK)) (ap1 devF (tmAp1 cId (ap1 srcF d))) Y fh
                   (G4cong devF (ap1 srcF sK) (tmAp1 cId (ap1 srcF d)) fh srcEqSKz)
                   (l4 fh (devF_ap1_u_h cId (ap1 srcF d) hd_cId))
      factT = G4trans (ap1 tgtF (ap1 triF sK)) Y (ap1 devF (ap1 srcF sK)) fh
                (G4trans (ap1 tgtF (ap1 triF sK)) (ap1 tgtF (derU X)) Y fh
                  (G4cong tgtF (ap1 triF sK) (derU X) fh triEq)
                  (G4trans (ap1 tgtF (derU X)) (ap1 tgtF X) Y fh (l4 fh (tgtF_rU X)) cT))
                (G4sym (ap1 devF (ap1 srcF sK)) Y fh devSrcEq)
  in assembleConj34 fh factV factS factT

------------------------------------------------------------------------
-- glue_ap1c_s :  funhead = 3 (cSuc).  triF sK = ap1c cSuc (triF (pL sK)).
-- A congruence residual (not a redex); cSuc is canonical so isF1/funValid bare.

glue_ap1c_s : Deriv (imp negLeaf (imp htagA (imp (eqF (ap1 Fst (funP sK)) (natCode 3)) (imp PA Bgoal))))
glue_ap1c_s =
  let fh = eqF (ap1 Fst (funP sK)) (natCode 3)
      d  = pL sK
      X  = ap1 triF d
      fp = funP sK
      Y  = ap1 devF (ap1 srcF d)
      Ap = dap1c cSuc X
      leqD = rebound d (pLValueBound sK ne_sK)
      tail = ap2 pi (funValid fp) (ap1 wfFunRec d)
      wfFunRecEq = addFunPA4 fh (wfFunRec_op_ap1c_imp sK ne_sK)
      wfFunPiEq = G4trans (ap2 pi (isF1 fp) tail) (ap1 wfFunRec sK) O fh
                    (G4sym (ap1 wfFunRec sK) (ap2 pi (isF1 fp) tail) fh wfFunRecEq) (wfFunSK4 fh)
      restEq = gPiR4 fh (isF1 fp) tail wfFunPiEq
      funValidFunPO = gPiL4 fh (funValid fp) (ap1 wfFunRec d) restEq
      wfFunDO = gPiR4 fh (funValid fp) (ap1 wfFunRec d) restEq
      wfFunOpO_c = fromFh fh (wfFun_op_s_himp fp)
      funValidFFunPO = G4trans (ap1 funValidF fp) (ap1 wfFun fp) O fh
                         (G4sym (ap1 wfFun fp) (ap1 funValidF fp) fh wfFunOpO_c) funValidFunPO
      eqdOEq = ap4c (l4 fh (prependEqLeft (eqDecO fp (ap1 recon fp)) (ap1 funValidF fp) O
                              (ruleSym (funValidF_eq fp)))) funValidFFunPO
      reconEqO = ap4c (fromFh fh (funValid_s_imp fp)) eqdOEq
      wfRedDO = G4trans (ap1 wfRed d) (ap1 wfRed sK) O fh
                  (G4sym (ap1 wfRed sK) (ap1 wfRed d) fh (addFunPA4 fh (wfRed_op_ap1c_imp sK ne_sK)))
                  (wfRedSK4 fh)
      childCj = mkChildCjFull4 fh d leqD (mkWfRedFull4 fh d wfRedDO wfFunDO)
      cV = ap4c (l4 fh (childV_imp d)) childCj
      cS = ap4c (l4 fh (childS_imp d)) childCj
      cT = ap4c (l4 fh (childT_imp d)) childCj
      cVwfRed = splitL4 fh X cV
      cVwfFun = splitR4 fh X cV
      triEq = addPA4 fh (triF_op_ap1c_s_imp sK ne_sK)
      srcEqSK = addFunPA4 fh (srcF_op_ap1c_imp sK ne_sK)
      tgtEqSK = addFunPA4 fh (tgtF_op_ap1c_imp sK ne_sK)
      -- V-fact : wfRedFull (ap1c cSuc X) = O.
      wfRedTriSK = G4trans (ap1 wfRed (ap1 triF sK)) (ap1 wfRed Ap) O fh
                     (G4cong wfRed (ap1 triF sK) Ap fh triEq)
                     (G4trans (ap1 wfRed Ap) (ap1 wfRed X) O fh (l4 fh (wfRed_ap1c cSuc X)) cVwfRed)
      wfFunTriSK = G4trans (ap1 wfFunRec (ap1 triF sK)) (ap1 wfFunRec Ap) O fh
                     (G4cong wfFunRec (ap1 triF sK) Ap fh triEq)
                     (G4trans (ap1 wfFunRec Ap)
                       (ap2 pi (isF1 cSuc) (ap2 pi (funValid cSuc) (ap1 wfFunRec X))) O fh
                       (l4 fh (wfFunRec_ap1c cSuc X))
                       (piB4 fh (isF1 cSuc) (ap2 pi (funValid cSuc) (ap1 wfFunRec X)) (l4 fh (isF1_codeF1 f1S))
                         (piB4 fh (funValid cSuc) (ap1 wfFunRec X) (l4 fh wfFun_cSuc) cVwfFun)))
      factV = mkWfRedFull4 fh (ap1 triF sK) wfRedTriSK wfFunTriSK
      -- S-fact.
      srcTriEq = G4trans (ap1 srcF (ap1 triF sK)) (ap1 srcF Ap) (tmAp1 cSuc (ap1 tgtF d)) fh
                   (G4cong srcF (ap1 triF sK) Ap fh triEq)
                   (G4trans (ap1 srcF Ap) (tmAp1 cSuc (ap1 srcF X)) (tmAp1 cSuc (ap1 tgtF d)) fh
                     (l4 fh (srcF_ap1c cSuc X)) (G4TmAp1 cSuc (ap1 srcF X) (ap1 tgtF d) fh cS))
      tgtEqSKz = G4trans (ap1 tgtF sK) (tmAp1 fp (ap1 tgtF d)) (tmAp1 cSuc (ap1 tgtF d)) fh
                   tgtEqSK (G4TmAp1Head fp cSuc (ap1 tgtF d) fh reconEqO)
      factS = G4trans (ap1 srcF (ap1 triF sK)) (tmAp1 cSuc (ap1 tgtF d)) (ap1 tgtF sK) fh
                srcTriEq (G4sym (ap1 tgtF sK) (tmAp1 cSuc (ap1 tgtF d)) fh tgtEqSKz)
      -- T-fact.
      srcEqSKz = G4trans (ap1 srcF sK) (tmAp1 fp (ap1 srcF d)) (tmAp1 cSuc (ap1 srcF d)) fh
                   srcEqSK (G4TmAp1Head fp cSuc (ap1 srcF d) fh reconEqO)
      devSrcEq = G4trans (ap1 devF (ap1 srcF sK)) (ap1 devF (tmAp1 cSuc (ap1 srcF d))) (tmAp1 cSuc Y) fh
                   (G4cong devF (ap1 srcF sK) (tmAp1 cSuc (ap1 srcF d)) fh srcEqSKz)
                   (l4 fh (devF_ap1_s_h cSuc (ap1 srcF d) hd_cSuc))
      tgtTriEq = G4trans (ap1 tgtF (ap1 triF sK)) (ap1 tgtF Ap) (tmAp1 cSuc Y) fh
                   (G4cong tgtF (ap1 triF sK) Ap fh triEq)
                   (G4trans (ap1 tgtF Ap) (tmAp1 cSuc (ap1 tgtF X)) (tmAp1 cSuc Y) fh
                     (l4 fh (tgtF_ap1c cSuc X)) (G4TmAp1 cSuc (ap1 tgtF X) Y fh cT))
      factT = G4trans (ap1 tgtF (ap1 triF sK)) (tmAp1 cSuc Y) (ap1 devF (ap1 srcF sK)) fh
                tgtTriEq (G4sym (ap1 devF (ap1 srcF sK)) (tmAp1 cSuc Y) fh devSrcEq)
  in assembleConj34 fh factV factS factT

------------------------------------------------------------------------
-- glue_ap1c_C :  funhead = 6 (cComp).  triF sK = derC g h1 h2 (triF (pL sK)),
-- g/h1/h2 = funP sK components (after reconstruction fp = cComp g h1 h2).

private
  tmAp1FunCong : (f gg Yv : Term) -> Deriv (eqF f gg) -> Deriv (eqF (tmAp1 f Yv) (tmAp1 gg Yv))
  tmAp1FunCong f gg Yv e = congR Pair tgAp1 (congL Pair Yv e)

  tmAp2Cong : (G G' A A' B B' : Term) ->
    Deriv (eqF G G') -> Deriv (eqF A A') -> Deriv (eqF B B') ->
    Deriv (eqF (tmAp2 G A B) (tmAp2 G' A' B'))
  tmAp2Cong G G' A A' B B' eG eA eB =
    congR Pair tgAp2
      (ruleTrans (congL Pair (ap2 Pair A B) eG)
                 (congR Pair G' (ruleTrans (congL Pair B eA) (congR Pair A' eB))))

  congCC : (g h1 h2 Yv : Term) ->
    Deriv (eqF (tmAp2 (gF (cComp g h1 h2)) (tmAp1 (h1F (cComp g h1 h2)) Yv) (tmAp1 (h2F (cComp g h1 h2)) Yv))
               (tmAp2 g (tmAp1 h1 Yv) (tmAp1 h2 Yv)))
  congCC g h1 h2 Yv =
    tmAp2Cong (gF (cComp g h1 h2)) g
              (tmAp1 (h1F (cComp g h1 h2)) Yv) (tmAp1 h1 Yv)
              (tmAp1 (h2F (cComp g h1 h2)) Yv) (tmAp1 h2 Yv)
              (compFun g h1 h2)
              (tmAp1FunCong (h1F (cComp g h1 h2)) h1 Yv (compH1 g h1 h2))
              (tmAp1FunCong (h2F (cComp g h1 h2)) h2 Yv (compH2 g h1 h2))

  tmAp2Arg1Imp : (gg a a' b : Term) -> Deriv (imp (eqF a a') (eqF (tmAp2 gg a b) (tmAp2 gg a' b)))
  tmAp2Arg1Imp gg a a' b =
    impCongR Pair (ap2 Pair gg (ap2 Pair a b)) (ap2 Pair gg (ap2 Pair a' b)) tgAp2
      (impCongR Pair (ap2 Pair a b) (ap2 Pair a' b) gg (impCongL Pair a a' b (identP (eqF a a'))))
  tmAp2Arg2Imp : (gg a b b' : Term) -> Deriv (imp (eqF b b') (eqF (tmAp2 gg a b) (tmAp2 gg a b')))
  tmAp2Arg2Imp gg a b b' =
    impCongR Pair (ap2 Pair gg (ap2 Pair a b)) (ap2 Pair gg (ap2 Pair a b')) tgAp2
      (impCongR Pair (ap2 Pair a b) (ap2 Pair a b') gg (impCongR Pair b b' a (identP (eqF b b'))))

  G4Ap2R : (gg a a' b b' : Term) (fh : Formula) ->
    Deriv (imp negLeaf (imp htagA (imp fh (imp PA (eqF a a'))))) ->
    Deriv (imp negLeaf (imp htagA (imp fh (imp PA (eqF b b'))))) ->
    Deriv (imp negLeaf (imp htagA (imp fh (imp PA (eqF (tmAp2 gg a b) (tmAp2 gg a' b'))))))
  G4Ap2R gg a a' b b' fh dA dB =
    G4trans (tmAp2 gg a b) (tmAp2 gg a' b) (tmAp2 gg a' b') fh
      (ap4c (l4 fh (tmAp2Arg1Imp gg a a' b)) dA)
      (ap4c (l4 fh (tmAp2Arg2Imp gg a' b b')) dB)

glue_ap1c_C : Deriv (imp negLeaf (imp htagA (imp (eqF (ap1 Fst (funP sK)) (natCode 6)) (imp PA Bgoal))))
glue_ap1c_C =
  let fh = eqF (ap1 Fst (funP sK)) (natCode 6)
      d  = pL sK
      X  = ap1 triF d
      fp = funP sK
      g  = cG fp
      h1 = cH1 fp
      h2 = cH2 fp
      cc = cComp g h1 h2
      Y  = ap1 devF (ap1 srcF d)
      Dc = derC g h1 h2 X
      leqD = rebound d (pLValueBound sK ne_sK)
      tail = ap2 pi (funValid fp) (ap1 wfFunRec d)
      wfFunRecEq = addFunPA4 fh (wfFunRec_op_ap1c_imp sK ne_sK)
      wfFunPiEq = G4trans (ap2 pi (isF1 fp) tail) (ap1 wfFunRec sK) O fh
                    (G4sym (ap1 wfFunRec sK) (ap2 pi (isF1 fp) tail) fh wfFunRecEq) (wfFunSK4 fh)
      restEq = gPiR4 fh (isF1 fp) tail wfFunPiEq
      funValidFunPO = gPiL4 fh (funValid fp) (ap1 wfFunRec d) restEq
      wfFunDO = gPiR4 fh (funValid fp) (ap1 wfFunRec d) restEq
      -- funValidF fp = O (head conjunct of wfFun fp).
      wfFunCHead = fromFh fh (wfFun_op_C_head_himp fp)
      piFunValidO = G4trans (ap2 pi (ap1 funValidF fp) (restCval fp)) (ap1 wfFun fp) O fh
                      (G4sym (ap1 wfFun fp) (ap2 pi (ap1 funValidF fp) (restCval fp)) fh wfFunCHead)
                      funValidFunPO
      funValidFfpO = gPiL4 fh (ap1 funValidF fp) (restCval fp) piFunValidO
      -- reconstruct fp = cc.
      eqdOEq = ap4c (l4 fh (prependEqLeft (eqDecO fp (ap1 recon fp)) (ap1 funValidF fp) O
                              (ruleSym (funValidF_eq fp)))) funValidFfpO
      reconEqC = ap4c (fromFh fh (funValid_C_imp fp)) eqdOEq
      -- child validity.
      wfRedDO = G4trans (ap1 wfRed d) (ap1 wfRed sK) O fh
                  (G4sym (ap1 wfRed sK) (ap1 wfRed d) fh (addFunPA4 fh (wfRed_op_ap1c_imp sK ne_sK)))
                  (wfRedSK4 fh)
      childCj = mkChildCjFull4 fh d leqD (mkWfRedFull4 fh d wfRedDO wfFunDO)
      cV = ap4c (l4 fh (childV_imp d)) childCj
      cS = ap4c (l4 fh (childS_imp d)) childCj
      cT = ap4c (l4 fh (childT_imp d)) childCj
      cVwfRed = splitL4 fh X cV
      cVwfFun = splitR4 fh X cV
      -- opaque eqs.
      triEqRaw = addPA4 fh (triF_op_ap1c_C_imp sK ne_sK)
      srcEqSK = addFunPA4 fh (srcF_op_ap1c_imp sK ne_sK)
      tgtEqSK = addFunPA4 fh (tgtF_op_ap1c_imp sK ne_sK)
      -- residual binNode -> derC g h1 h2 X.
      sndFpEq = G4trans (ap1 Snd fp) (ap1 Snd cc) (bun3 g h1 h2) fh
                  (G4cong Snd fp cc fh reconEqC)
                  (l4 fh (axSnd (natCode 6) (bun3 g h1 h2)))
      BIGa = ap2 Pair (ap2 Pair (natCode 6) (ap1 Snd fp)) (ap2 Pair X derLeaf)
      BIGb = ap2 Pair (ap2 Pair (natCode 6) (bun3 g h1 h2)) (ap2 Pair X derLeaf)
      labConvImp = impCongR Pair BIGa BIGb (natCode 2)
                     (impCongL Pair (ap2 Pair (natCode 6) (ap1 Snd fp)) (ap2 Pair (natCode 6) (bun3 g h1 h2)) (ap2 Pair X derLeaf)
                       (impCongR Pair (ap1 Snd fp) (bun3 g h1 h2) (natCode 6) (identP (eqF (ap1 Snd fp) (bun3 g h1 h2)))))
      triEqDerC = G4trans (ap1 triF sK) (binNode (ap2 Pair (natCode 6) (ap1 Snd fp)) X derLeaf) Dc fh
                    triEqRaw (ap4c (l4 fh labConvImp) sndFpEq)
      -- V-fact.
      wfFunccO = G4trans (ap1 wfFun cc) (ap1 wfFun fp) O fh
                   (G4cong wfFun cc fp fh (G4sym fp cc fh reconEqC)) funValidFunPO
      wfRedTriSK = G4trans (ap1 wfRed (ap1 triF sK)) (ap1 wfRed Dc) O fh
                     (G4cong wfRed (ap1 triF sK) Dc fh triEqDerC)
                     (G4trans (ap1 wfRed Dc) (ap1 wfRed X) O fh (l4 fh (wfRed_rC g h1 h2 X)) cVwfRed)
      wfFunTriSK = G4trans (ap1 wfFunRec (ap1 triF sK)) (ap1 wfFunRec Dc) O fh
                     (G4cong wfFunRec (ap1 triF sK) Dc fh triEqDerC)
                     (G4trans (ap1 wfFunRec Dc) (ap2 pi (ap1 wfFun cc) (ap1 wfFunRec X)) O fh
                       (l4 fh (wfFunRec_rC g h1 h2 X))
                       (piB4 fh (ap1 wfFun cc) (ap1 wfFunRec X) wfFunccO cVwfFun))
      factV = mkWfRedFull4 fh (ap1 triF sK) wfRedTriSK wfFunTriSK
      -- S-fact.
      srcTriEq = G4trans (ap1 srcF (ap1 triF sK)) (ap1 srcF Dc) (tmAp1 cc (ap1 tgtF d)) fh
                   (G4cong srcF (ap1 triF sK) Dc fh triEqDerC)
                   (G4trans (ap1 srcF Dc) (tmAp1 cc (ap1 srcF X)) (tmAp1 cc (ap1 tgtF d)) fh
                     (l4 fh (srcF_rC g h1 h2 X)) (G4TmAp1 cc (ap1 srcF X) (ap1 tgtF d) fh cS))
      tgtEqSKc = G4trans (ap1 tgtF sK) (tmAp1 fp (ap1 tgtF d)) (tmAp1 cc (ap1 tgtF d)) fh
                   tgtEqSK (G4TmAp1Head fp cc (ap1 tgtF d) fh reconEqC)
      factS = G4trans (ap1 srcF (ap1 triF sK)) (tmAp1 cc (ap1 tgtF d)) (ap1 tgtF sK) fh
                srcTriEq (G4sym (ap1 tgtF sK) (tmAp1 cc (ap1 tgtF d)) fh tgtEqSKc)
      -- T-fact.
      srcEqSKc = G4trans (ap1 srcF sK) (tmAp1 fp (ap1 srcF d)) (tmAp1 cc (ap1 srcF d)) fh
                   srcEqSK (G4TmAp1Head fp cc (ap1 srcF d) fh reconEqC)
      tgtTriEq = G4trans (ap1 tgtF (ap1 triF sK)) (ap1 tgtF Dc) (tmAp2 g (tmAp1 h1 Y) (tmAp1 h2 Y)) fh
                   (G4cong tgtF (ap1 triF sK) Dc fh triEqDerC)
                   (G4trans (ap1 tgtF Dc)
                     (tmAp2 g (tmAp1 h1 (ap1 tgtF X)) (tmAp1 h2 (ap1 tgtF X)))
                     (tmAp2 g (tmAp1 h1 Y) (tmAp1 h2 Y)) fh
                     (l4 fh (tgtF_rC g h1 h2 X))
                     (G4Ap2R g (tmAp1 h1 (ap1 tgtF X)) (tmAp1 h1 Y) (tmAp1 h2 (ap1 tgtF X)) (tmAp1 h2 Y) fh
                       (G4TmAp1 h1 (ap1 tgtF X) Y fh cT) (G4TmAp1 h2 (ap1 tgtF X) Y fh cT)))
      devSrcEq = G4trans (ap1 devF (ap1 srcF sK)) (ap1 devF (tmAp1 cc (ap1 srcF d)))
                   (tmAp2 g (tmAp1 h1 Y) (tmAp1 h2 Y)) fh
                   (G4cong devF (ap1 srcF sK) (tmAp1 cc (ap1 srcF d)) fh srcEqSKc)
                   (G4trans (ap1 devF (tmAp1 cc (ap1 srcF d)))
                     (tmAp2 (gF cc) (tmAp1 (h1F cc) Y) (tmAp1 (h2F cc) Y))
                     (tmAp2 g (tmAp1 h1 Y) (tmAp1 h2 Y)) fh
                     (l4 fh (devF_ap1_C_h cc (ap1 srcF d) (hd_cComp g h1 h2)))
                     (l4 fh (congCC g h1 h2 Y)))
      factT = G4trans (ap1 tgtF (ap1 triF sK)) (tmAp2 g (tmAp1 h1 Y) (tmAp1 h2 Y)) (ap1 devF (ap1 srcF sK)) fh
                tgtTriEq (G4sym (ap1 devF (ap1 srcF sK)) (tmAp2 g (tmAp1 h1 Y) (tmAp1 h2 Y)) fh devSrcEq)
  in assembleConj34 fh factV factS factT
