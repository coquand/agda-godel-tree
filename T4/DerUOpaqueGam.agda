{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.DerUOpaqueGam -- Gamma-polymorphic, ne-THREADED opaque equations for
-- srcF / tgtF / wfRed at an OPAQUE child whose non-O hypothesis is not available
-- bare (the left child  pL p  of an Ad node).  Every fact is  imp Gam X , with
-- ne / leaf-test / tag supplied as Gam-facts.  Mirrors the ne-bare imp-form eqs
-- (T4.DerSrcUOpaqueImp etc.) but threads ne through the harness (Himp) and the
-- child lookup (lookup_op_imp), exactly as T4.DerTriUSuGam does for triF.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.DerUOpaqueGam where

open import T4.Base

open import T4.DerCodeS using ( dtag ; pL ; pR ; pArg )
open import T4.DerCode using ( dgSu ; dgAd ; dgRO ; dgRS )
open import T4.AdDispatchAux using ( dtag_O ; FstO )
open import T4.DescSndImp using ( neSucc ; succForm_imp )
open import T4.DerTriUSuGam using ( pLValueBound_imp )
open import T4.WfRedExtract using ( pLValueBound ; pRValueBound )
open import T4.OpaqueLookupImp using ( lookup_op_imp )
open import T4.GammaCtx using ( Cnj ; cnjL ; cnjR ; cnjCurry )
open import T4.ForkImp
  using ( fork_true_to_fst_imp ; fork_false_to_snd_imp
        ; testEq_fire_imp ; testEq_skip_imp ; natEqFire_imp )
open import T4.ProgParse using ( get_tag )
open import T4.FoldRec using ( lookupAt ; fold ; get_newK )
open import T4.ParsObj using ( stepOf )
open import T4.BinTree using ( nIdx ; lIdx ; rIdx )

open import T4.DerSrc
  using ( testEq ; ze#F ; ze#F_at ; suCell ; adCell ; roCell ; rsCell
        ; cellNode ; srcF ; restAd ; restRO
        ; w21 ; w31 ; w32 ; w41 ; w42 ; w43 )
open import T4.DerTgt using ( cellNodeT ; tgtF ; restAdT )
open import T4.WfRed using ( wfCellNode ; wfRed ; wfAdCell ; wfRestAd ; wfRestRO ; wfRestRS ; rejectCell )
open import T4.NatEqReflect using ( natEqF_complete )

open import T4.TrsCodeObj using ( ze# ; su# ; ad# ; tagSu )

open import BRA3.Church       using ( pi ; predecessor ; sub )
open import BRA3.ChurchLeq    using ( leq )
open import BRA3.PairAlgebra  using ( compose1U_eq ; Post )
open import BRA3.SubT.NatEq   using ( natEqF )
open import BRA3.Classical    using ( axContrapos )
open import BRA3.Logic        using ( eqSymImp )
open import BRA3.Contrapositive using ( compI ; liftP ; identP ; bComb )
open import T4.Thm12.ImpHelpers
  using ( impLift ; impCong1 ; impCongL ; impCongR ; impEqTrans )

import T4.OpaqueHarnessImp

------------------------------------------------------------------------
-- pRValueBound_imp :  imp (p != O) (pR p <= pred p) .  (transport trick.)

pRValueBound_imp : (p : Term) ->
  Deriv (imp (neg (eqF p O)) (leq (pR p) (ap1 predecessor p)))
pRValueBound_imp p =
  let sp : Term
      sp = ap1 s (ap1 predecessor p)
      neS : Deriv (neg (eqF sp O))
      neS = neSucc (ap1 predecessor p)
      D : Deriv (leq (pR sp) (ap1 predecessor sp))
      D = pRValueBound sp neS
      sfi : Deriv (imp (neg (eqF p O)) (eqF p sp))
      sfi = succForm_imp p
      argEq : Deriv (imp (neg (eqF p O)) (eqF (pR p) (pR sp)))
      argEq = impCong1 Snd (pArg p) (pArg sp)
                (impCong1 Snd (ap1 Snd p) (ap1 Snd sp)
                  (impCong1 Snd p sp sfi))
      predEq : Deriv (imp (neg (eqF p O))
                 (eqF (ap1 predecessor p) (ap1 predecessor sp)))
      predEq = impCong1 predecessor p sp sfi
      stepA = impCongL sub (pR p) (pR sp) (ap1 predecessor p) argEq
      stepB = impCongR sub (ap1 predecessor p) (ap1 predecessor sp) (pR sp) predEq
      chain = impEqTrans (ap2 sub (pR p) (ap1 predecessor p))
                         (ap2 sub (pR sp) (ap1 predecessor p))
                         (ap2 sub (pR sp) (ap1 predecessor sp)) stepA stepB
  in impEqTrans (ap2 sub (pR p) (ap1 predecessor p))
                (ap2 sub (pR sp) (ap1 predecessor sp)) O chain (impLift D)

------------------------------------------------------------------------
-- ne from a leaf marker / from a node tag.

private
  applyContra : (P X : Formula) -> Deriv (neg X) ->
    Deriv (imp (imp P X) (neg P))
  applyContra P X negX =
    let K : Formula
        K = imp (neg X) (neg P)
        ap : Deriv (imp K (neg P))
        ap = bComb (identP K) (liftP K negX)
    in compI (axContrapos P X) ap

neLeaf_imp : (c : Term) ->
  Deriv (imp (eqF (ap1 Fst c) (natCode 1)) (neg (eqF c O)))
neLeaf_imp c =
  let H : Formula
      H = eqF (ap1 Fst c) (natCode 1)
      P : Formula
      P = eqF c O
      G : Formula
      G = Cnj H P
      gH : Deriv (imp G H)
      gH = cnjL H P
      gP : Deriv (imp G P)
      gP = cnjR H P
      sH : Deriv (imp G (eqF (ap1 s O) (ap1 Fst c)))
      sH = compI gH (eqSymImp (ap1 Fst c) (natCode 1))
      fcO : Deriv (imp G (eqF (ap1 Fst c) O))
      fcO = impEqTrans (ap1 Fst c) (ap1 Fst O) O
              (impCong1 Fst c O gP) (liftP G FstO)
      sO_O : Deriv (imp G (eqF (ap1 s O) O))
      sO_O = impEqTrans (ap1 s O) (ap1 Fst c) O sH fcO
      d_HP : Deriv (imp H (imp P (eqF (ap1 s O) O)))
      d_HP = cnjCurry sO_O
  in compI d_HP (applyContra P (eqF (ap1 s O) O) ax_succ_nonzero)

neTag_imp : (c : Term) (j : Nat) ->
  Deriv (imp (eqF (dtag c) (natCode (suc j))) (neg (eqF c O)))
neTag_imp c j =
  let sj : Term
      sj = ap1 s (natCode j)
      H : Formula
      H = eqF (dtag c) (natCode (suc j))
      P : Formula
      P = eqF c O
      G : Formula
      G = Cnj H P
      gH : Deriv (imp G H)
      gH = cnjL H P
      gP : Deriv (imp G P)
      gP = cnjR H P
      sH : Deriv (imp G (eqF sj (dtag c)))
      sH = compI gH (eqSymImp (dtag c) (natCode (suc j)))
      dtagEq : Deriv (imp G (eqF (dtag c) (dtag O)))
      dtagEq = impCong1 Fst (ap1 Snd c) (ap1 Snd O) (impCong1 Snd c O gP)
      dtO : Deriv (imp G (eqF (dtag c) O))
      dtO = impEqTrans (dtag c) (dtag O) O dtagEq (liftP G dtag_O)
      sj_O : Deriv (imp G (eqF sj O))
      sj_O = impEqTrans sj (dtag c) O sH dtO
      d_HP : Deriv (imp H (imp P (eqF sj O)))
      d_HP = cnjCurry sj_O
  in compI d_HP (applyContra P (eqF sj O) (neSucc (natCode j)))

------------------------------------------------------------------------
-- The Gamma-threaded node plumbing, parametric in the two cells.

module NodeGam (g cellLeaf cellNode : Fun1) where
  sbf : Fun1
  sbf = stepOf cellLeaf cellNode

  open T4.OpaqueHarnessImp.HimpBase g sbf public

  ff : Fun1
  ff = fold g (Post sbf pi)

  test1F : Fun1
  test1F = C natEqF get_tag (constN 1)

  op_tag_imp : (c : Term) ->
    Deriv (imp (neg (eqF c O)) (eqF (ap1 get_tag (opkg c)) (ap1 Fst c)))
  op_tag_imp c =
    impEqTrans (ap1 get_tag (opkg c)) (ap1 Fst (ap1 get_newK (opkg c))) (ap1 Fst c)
      (impLift (compose1U_eq Fst get_newK (opkg c)))
      (impCong1 Fst (ap1 get_newK (opkg c)) c (op_newK_imp c))

  test1_eq : (c : Term) ->
    Deriv (imp (neg (eqF c O))
               (eqF (ap1 test1F (opkg c)) (ap2 natEqF (ap1 Fst c) (natCode 1))))
  test1_eq c =
    impEqTrans (ap1 test1F (opkg c))
               (ap2 natEqF (ap1 get_tag (opkg c)) (ap1 (constN 1) (opkg c)))
               (ap2 natEqF (ap1 Fst c) (natCode 1))
      (impLift (ax_C natEqF get_tag (constN 1) (opkg c)))
      (impEqTrans (ap2 natEqF (ap1 get_tag (opkg c)) (ap1 (constN 1) (opkg c)))
                  (ap2 natEqF (ap1 Fst c) (ap1 (constN 1) (opkg c)))
                  (ap2 natEqF (ap1 Fst c) (natCode 1))
         (impCongL natEqF (ap1 get_tag (opkg c)) (ap1 Fst c) (ap1 (constN 1) (opkg c)) (op_tag_imp c))
         (impLift (congR natEqF (ap1 Fst c) (constN_eq 1 (opkg c)))))

  unfold_g : (Gam : Formula) (c : Term) ->
    Deriv (imp Gam (neg (eqF c O))) ->
    Deriv (imp Gam (eqF (ap1 ff c) (ap1 sbf (opkg c))))
  unfold_g Gam c gNe = compI gNe (opUnfold_imp c)

  toLeaf_g : (Gam : Formula) (c : Term) ->
    Deriv (imp Gam (neg (eqF c O))) ->
    Deriv (imp Gam (eqF (ap1 Fst c) (natCode 1))) ->
    Deriv (imp Gam (eqF (ap1 sbf (opkg c)) (ap1 cellLeaf (opkg c))))
  toLeaf_g Gam c gNe gLeaf =
    let gGtag : Deriv (imp Gam (eqF (ap1 get_tag (opkg c)) (natCode 1)))
        gGtag = impEqTrans (ap1 get_tag (opkg c)) (ap1 Fst c) (natCode 1)
                  (compI gNe (op_tag_imp c)) gLeaf
    in fork_true_to_fst_imp Gam cellLeaf cellNode test1F (opkg c)
         (natEqFire_imp Gam get_tag 1 (opkg c) gGtag)

  toNode_g : (Gam : Formula) (c : Term) ->
    Deriv (imp Gam (neg (eqF c O))) ->
    Deriv (imp Gam (eqF (ap2 natEqF (ap1 Fst c) (natCode 1)) O)) ->
    Deriv (imp Gam (eqF (ap1 sbf (opkg c)) (ap1 cellNode (opkg c))))
  toNode_g Gam c gNe gNl =
    let t1O : Deriv (imp Gam (eqF (ap1 test1F (opkg c)) O))
        t1O = impEqTrans (ap1 test1F (opkg c)) (ap2 natEqF (ap1 Fst c) (natCode 1)) O
                (compI gNe (test1_eq c)) gNl
    in fork_false_to_snd_imp Gam cellLeaf cellNode test1F (opkg c) t1O

  nieq_g : (Gam : Formula) (c : Term) (lbl : Term) ->
    Deriv (imp Gam (neg (eqF c O))) ->
    Deriv (imp Gam (eqF (dtag c) lbl)) ->
    Deriv (imp Gam (eqF (ap1 nIdx (opkg c)) lbl))
  nieq_g Gam c lbl gNe gHtag =
    impEqTrans (ap1 nIdx (opkg c)) (dtag c) lbl (compI gNe (op_nIdx_imp c)) gHtag

  recPL_g : (Gam : Formula) (c : Term) ->
    Deriv (imp Gam (neg (eqF c O))) ->
    Deriv (imp Gam (eqF (ap1 (lookupAt lIdx) (opkg c)) (ap1 ff (pL c))))
  recPL_g Gam c gNe =
    lookup_op_imp Gam g sbf lIdx (ap1 predecessor c) (pL c)
      (compI gNe (op_pL_imp c)) (compI gNe (pLValueBound_imp c))

  recPR_g : (Gam : Formula) (c : Term) ->
    Deriv (imp Gam (neg (eqF c O))) ->
    Deriv (imp Gam (eqF (ap1 (lookupAt rIdx) (opkg c)) (ap1 ff (pR c))))
  recPR_g Gam c gNe =
    lookup_op_imp Gam g sbf rIdx (ap1 predecessor c) (pR c)
      (compI gNe (op_pR_imp c)) (compI gNe (pRValueBound_imp c))

------------------------------------------------------------------------
-- Instances.

private
  module Hsrc = NodeGam Z ze#F cellNode
  module Htgt = NodeGam Z ze#F cellNodeT
  module Hwf  = NodeGam rejectCell Z wfCellNode

------------------------------------------------------------------------
-- Leaf eqs :  srcF c = ze# ,  tgtF c = ze# .

srcF_op_Ze_gam : (Gam : Formula) (c : Term) ->
  Deriv (imp Gam (neg (eqF c O))) ->
  Deriv (imp Gam (eqF (ap1 Fst c) (natCode 1))) ->
  Deriv (imp Gam (eqF (ap1 srcF c) ze#))
srcF_op_Ze_gam Gam c gNe gLeaf =
  let opk = Hsrc.opkg c in
  impEqTrans (ap1 srcF c) (ap1 Hsrc.sbf opk) ze# (Hsrc.unfold_g Gam c gNe)
    (impEqTrans (ap1 Hsrc.sbf opk) (ap1 ze#F opk) ze#
       (Hsrc.toLeaf_g Gam c gNe gLeaf) (liftP Gam (ze#F_at opk)))

tgtF_op_Ze_gam : (Gam : Formula) (c : Term) ->
  Deriv (imp Gam (neg (eqF c O))) ->
  Deriv (imp Gam (eqF (ap1 Fst c) (natCode 1))) ->
  Deriv (imp Gam (eqF (ap1 tgtF c) ze#))
tgtF_op_Ze_gam Gam c gNe gLeaf =
  let opk = Htgt.opkg c in
  impEqTrans (ap1 tgtF c) (ap1 Htgt.sbf opk) ze# (Htgt.unfold_g Gam c gNe)
    (impEqTrans (ap1 Htgt.sbf opk) (ap1 ze#F opk) ze#
       (Htgt.toLeaf_g Gam c gNe gLeaf) (liftP Gam (ze#F_at opk)))

------------------------------------------------------------------------
-- Su eqs :  srcF c = su# (srcF (pL c)) ,  tgtF c = su# (tgtF (pL c)) ,
--           wfRed c = wfRed (pL c) .

srcF_op_Su_gam : (Gam : Formula) (c : Term) ->
  Deriv (imp Gam (neg (eqF c O))) ->
  Deriv (imp Gam (eqF (ap2 natEqF (ap1 Fst c) (natCode 1)) O)) ->
  Deriv (imp Gam (eqF (dtag c) dgSu)) ->
  Deriv (imp Gam (eqF (ap1 srcF c) (su# (ap1 srcF (pL c)))))
srcF_op_Su_gam Gam c gNe gNl gHtag =
  let opk = Hsrc.opkg c
      nieq = Hsrc.nieq_g Gam c dgSu gNe gHtag
      cellfires : Deriv (imp Gam (eqF (ap1 cellNode opk) (ap1 suCell opk)))
      cellfires = fork_true_to_fst_imp Gam suCell restAd (testEq 1) opk
                    (testEq_fire_imp Gam 1 opk nieq)
      rec = Hsrc.recPL_g Gam c gNe
      cell_val : Deriv (imp Gam (eqF (ap1 suCell opk) (su# (ap1 srcF (pL c)))))
      cell_val =
        impEqTrans (ap1 suCell opk) (ap2 pi (ap1 (constN 1) opk) (ap1 (lookupAt lIdx) opk))
                   (su# (ap1 srcF (pL c)))
          (liftP Gam (ax_C pi (constN 1) (lookupAt lIdx) opk))
          (impEqTrans (ap2 pi (ap1 (constN 1) opk) (ap1 (lookupAt lIdx) opk))
                      (ap2 pi (natCode 1) (ap1 (lookupAt lIdx) opk))
                      (su# (ap1 srcF (pL c)))
             (liftP Gam (congL pi (ap1 (lookupAt lIdx) opk) (constN_eq 1 opk)))
             (impCongR pi (ap1 (lookupAt lIdx) opk) (ap1 srcF (pL c)) (natCode 1) rec))
  in impEqTrans (ap1 srcF c) (ap1 Hsrc.sbf opk) (su# (ap1 srcF (pL c)))
       (Hsrc.unfold_g Gam c gNe)
       (impEqTrans (ap1 Hsrc.sbf opk) (ap1 cellNode opk) (su# (ap1 srcF (pL c)))
          (Hsrc.toNode_g Gam c gNe gNl)
          (impEqTrans (ap1 cellNode opk) (ap1 suCell opk) (su# (ap1 srcF (pL c)))
             cellfires cell_val))

tgtF_op_Su_gam : (Gam : Formula) (c : Term) ->
  Deriv (imp Gam (neg (eqF c O))) ->
  Deriv (imp Gam (eqF (ap2 natEqF (ap1 Fst c) (natCode 1)) O)) ->
  Deriv (imp Gam (eqF (dtag c) dgSu)) ->
  Deriv (imp Gam (eqF (ap1 tgtF c) (su# (ap1 tgtF (pL c)))))
tgtF_op_Su_gam Gam c gNe gNl gHtag =
  let opk = Htgt.opkg c
      nieq = Htgt.nieq_g Gam c dgSu gNe gHtag
      cellfires : Deriv (imp Gam (eqF (ap1 cellNodeT opk) (ap1 suCell opk)))
      cellfires = fork_true_to_fst_imp Gam suCell restAdT (testEq 1) opk
                    (testEq_fire_imp Gam 1 opk nieq)
      rec = Htgt.recPL_g Gam c gNe
      cell_val : Deriv (imp Gam (eqF (ap1 suCell opk) (su# (ap1 tgtF (pL c)))))
      cell_val =
        impEqTrans (ap1 suCell opk) (ap2 pi (ap1 (constN 1) opk) (ap1 (lookupAt lIdx) opk))
                   (su# (ap1 tgtF (pL c)))
          (liftP Gam (ax_C pi (constN 1) (lookupAt lIdx) opk))
          (impEqTrans (ap2 pi (ap1 (constN 1) opk) (ap1 (lookupAt lIdx) opk))
                      (ap2 pi (natCode 1) (ap1 (lookupAt lIdx) opk))
                      (su# (ap1 tgtF (pL c)))
             (liftP Gam (congL pi (ap1 (lookupAt lIdx) opk) (constN_eq 1 opk)))
             (impCongR pi (ap1 (lookupAt lIdx) opk) (ap1 tgtF (pL c)) (natCode 1) rec))
  in impEqTrans (ap1 tgtF c) (ap1 Htgt.sbf opk) (su# (ap1 tgtF (pL c)))
       (Htgt.unfold_g Gam c gNe)
       (impEqTrans (ap1 Htgt.sbf opk) (ap1 cellNodeT opk) (su# (ap1 tgtF (pL c)))
          (Htgt.toNode_g Gam c gNe gNl)
          (impEqTrans (ap1 cellNodeT opk) (ap1 suCell opk) (su# (ap1 tgtF (pL c)))
             cellfires cell_val))

wfRed_op_Su_gam : (Gam : Formula) (c : Term) ->
  Deriv (imp Gam (neg (eqF c O))) ->
  Deriv (imp Gam (eqF (ap2 natEqF (ap1 Fst c) (natCode 1)) O)) ->
  Deriv (imp Gam (eqF (dtag c) dgSu)) ->
  Deriv (imp Gam (eqF (ap1 wfRed c) (ap1 wfRed (pL c))))
wfRed_op_Su_gam Gam c gNe gNl gHtag =
  let opk = Hwf.opkg c
      nieq = Hwf.nieq_g Gam c dgSu gNe gHtag
      cellfires : Deriv (imp Gam (eqF (ap1 wfCellNode opk) (ap1 (lookupAt lIdx) opk)))
      cellfires = fork_true_to_fst_imp Gam (lookupAt lIdx) wfRestAd (testEq 1) opk
                    (testEq_fire_imp Gam 1 opk nieq)
      rec = Hwf.recPL_g Gam c gNe
  in impEqTrans (ap1 wfRed c) (ap1 Hwf.sbf opk) (ap1 wfRed (pL c))
       (Hwf.unfold_g Gam c gNe)
       (impEqTrans (ap1 Hwf.sbf opk) (ap1 wfCellNode opk) (ap1 wfRed (pL c))
          (Hwf.toNode_g Gam c gNe gNl)
          (impEqTrans (ap1 wfCellNode opk) (ap1 (lookupAt lIdx) opk) (ap1 wfRed (pL c))
             cellfires rec))

------------------------------------------------------------------------
-- Ad / RO / RS srcF eqs (ad#-headed source, for the Ad-else development).

srcF_op_Ad_gam : (Gam : Formula) (c : Term) ->
  Deriv (imp Gam (neg (eqF c O))) ->
  Deriv (imp Gam (eqF (ap2 natEqF (ap1 Fst c) (natCode 1)) O)) ->
  Deriv (imp Gam (eqF (dtag c) dgAd)) ->
  Deriv (imp Gam (eqF (ap1 srcF c) (ad# (ap1 srcF (pL c)) (ap1 srcF (pR c)))))
srcF_op_Ad_gam Gam c gNe gNl gHtag =
  let opk = Hsrc.opkg c
      val : Term
      val = ad# (ap1 srcF (pL c)) (ap1 srcF (pR c))
      nieq = Hsrc.nieq_g Gam c dgAd gNe gHtag
      toRestAd : Deriv (imp Gam (eqF (ap1 cellNode opk) (ap1 restAd opk)))
      toRestAd = fork_false_to_snd_imp Gam suCell restAd (testEq 1) opk
                   (testEq_skip_imp Gam 2 1 opk w21 nieq)
      toAdCell : Deriv (imp Gam (eqF (ap1 restAd opk) (ap1 adCell opk)))
      toAdCell = fork_true_to_fst_imp Gam adCell restRO (testEq 2) opk
                   (testEq_fire_imp Gam 2 opk nieq)
      recL = Hsrc.recPL_g Gam c gNe
      recR = Hsrc.recPR_g Gam c gNe
      innerC : Term
      innerC = ap1 (C pi (lookupAt lIdx) (lookupAt rIdx)) opk
      inner_val : Deriv (imp Gam (eqF innerC (ap2 pi (ap1 srcF (pL c)) (ap1 srcF (pR c)))))
      inner_val =
        impEqTrans innerC (ap2 pi (ap1 (lookupAt lIdx) opk) (ap1 (lookupAt rIdx) opk))
                   (ap2 pi (ap1 srcF (pL c)) (ap1 srcF (pR c)))
          (liftP Gam (ax_C pi (lookupAt lIdx) (lookupAt rIdx) opk))
          (impEqTrans (ap2 pi (ap1 (lookupAt lIdx) opk) (ap1 (lookupAt rIdx) opk))
                      (ap2 pi (ap1 srcF (pL c)) (ap1 (lookupAt rIdx) opk))
                      (ap2 pi (ap1 srcF (pL c)) (ap1 srcF (pR c)))
             (impCongL pi (ap1 (lookupAt lIdx) opk) (ap1 srcF (pL c)) (ap1 (lookupAt rIdx) opk) recL)
             (impCongR pi (ap1 (lookupAt rIdx) opk) (ap1 srcF (pR c)) (ap1 srcF (pL c)) recR))
      cell_val : Deriv (imp Gam (eqF (ap1 adCell opk) val))
      cell_val =
        impEqTrans (ap1 adCell opk) (ap2 pi (ap1 (constN 2) opk) innerC) val
          (liftP Gam (ax_C pi (constN 2) (C pi (lookupAt lIdx) (lookupAt rIdx)) opk))
          (impEqTrans (ap2 pi (ap1 (constN 2) opk) innerC) (ap2 pi (natCode 2) innerC) val
             (liftP Gam (congL pi innerC (constN_eq 2 opk)))
             (impCongR pi innerC (ap2 pi (ap1 srcF (pL c)) (ap1 srcF (pR c))) (natCode 2) inner_val))
  in impEqTrans (ap1 srcF c) (ap1 Hsrc.sbf opk) val (Hsrc.unfold_g Gam c gNe)
       (impEqTrans (ap1 Hsrc.sbf opk) (ap1 cellNode opk) val (Hsrc.toNode_g Gam c gNe gNl)
          (impEqTrans (ap1 cellNode opk) (ap1 restAd opk) val toRestAd
             (impEqTrans (ap1 restAd opk) (ap1 adCell opk) val toAdCell cell_val)))

srcF_op_RO_gam : (Gam : Formula) (c : Term) ->
  Deriv (imp Gam (neg (eqF c O))) ->
  Deriv (imp Gam (eqF (ap2 natEqF (ap1 Fst c) (natCode 1)) O)) ->
  Deriv (imp Gam (eqF (dtag c) dgRO)) ->
  Deriv (imp Gam (eqF (ap1 srcF c) (ad# ze# (ap1 srcF (pL c)))))
srcF_op_RO_gam Gam c gNe gNl gHtag =
  let opk = Hsrc.opkg c
      val : Term
      val = ad# ze# (ap1 srcF (pL c))
      nieq = Hsrc.nieq_g Gam c dgRO gNe gHtag
      toRestAd = fork_false_to_snd_imp Gam suCell restAd (testEq 1) opk
                   (testEq_skip_imp Gam 3 1 opk w31 nieq)
      toRestRO = fork_false_to_snd_imp Gam adCell restRO (testEq 2) opk
                   (testEq_skip_imp Gam 3 2 opk w32 nieq)
      toRoCell = fork_true_to_fst_imp Gam roCell rsCell (testEq 3) opk
                   (testEq_fire_imp Gam 3 opk nieq)
      recL = Hsrc.recPL_g Gam c gNe
      innerC : Term
      innerC = ap1 (C pi ze#F (lookupAt lIdx)) opk
      inner_val : Deriv (imp Gam (eqF innerC (ap2 pi ze# (ap1 srcF (pL c)))))
      inner_val =
        impEqTrans innerC (ap2 pi (ap1 ze#F opk) (ap1 (lookupAt lIdx) opk))
                   (ap2 pi ze# (ap1 srcF (pL c)))
          (liftP Gam (ax_C pi ze#F (lookupAt lIdx) opk))
          (impEqTrans (ap2 pi (ap1 ze#F opk) (ap1 (lookupAt lIdx) opk))
                      (ap2 pi ze# (ap1 (lookupAt lIdx) opk))
                      (ap2 pi ze# (ap1 srcF (pL c)))
             (liftP Gam (congL pi (ap1 (lookupAt lIdx) opk) (ze#F_at opk)))
             (impCongR pi (ap1 (lookupAt lIdx) opk) (ap1 srcF (pL c)) ze# recL))
      cell_val : Deriv (imp Gam (eqF (ap1 roCell opk) val))
      cell_val =
        impEqTrans (ap1 roCell opk) (ap2 pi (ap1 (constN 2) opk) innerC) val
          (liftP Gam (ax_C pi (constN 2) (C pi ze#F (lookupAt lIdx)) opk))
          (impEqTrans (ap2 pi (ap1 (constN 2) opk) innerC) (ap2 pi (natCode 2) innerC) val
             (liftP Gam (congL pi innerC (constN_eq 2 opk)))
             (impCongR pi innerC (ap2 pi ze# (ap1 srcF (pL c))) (natCode 2) inner_val))
  in impEqTrans (ap1 srcF c) (ap1 Hsrc.sbf opk) val (Hsrc.unfold_g Gam c gNe)
       (impEqTrans (ap1 Hsrc.sbf opk) (ap1 cellNode opk) val (Hsrc.toNode_g Gam c gNe gNl)
          (impEqTrans (ap1 cellNode opk) (ap1 restAd opk) val toRestAd
             (impEqTrans (ap1 restAd opk) (ap1 restRO opk) val toRestRO
                (impEqTrans (ap1 restRO opk) (ap1 roCell opk) val toRoCell cell_val))))

srcF_op_RS_gam : (Gam : Formula) (c : Term) ->
  Deriv (imp Gam (neg (eqF c O))) ->
  Deriv (imp Gam (eqF (ap2 natEqF (ap1 Fst c) (natCode 1)) O)) ->
  Deriv (imp Gam (eqF (dtag c) dgRS)) ->
  Deriv (imp Gam (eqF (ap1 srcF c) (ad# (su# (ap1 srcF (pL c))) (ap1 srcF (pR c)))))
srcF_op_RS_gam Gam c gNe gNl gHtag =
  let opk = Hsrc.opkg c
      val : Term
      val = ad# (su# (ap1 srcF (pL c))) (ap1 srcF (pR c))
      nieq = Hsrc.nieq_g Gam c dgRS gNe gHtag
      toRestAd = fork_false_to_snd_imp Gam suCell restAd (testEq 1) opk
                   (testEq_skip_imp Gam 4 1 opk w41 nieq)
      toRestRO = fork_false_to_snd_imp Gam adCell restRO (testEq 2) opk
                   (testEq_skip_imp Gam 4 2 opk w42 nieq)
      toRsCell = fork_false_to_snd_imp Gam roCell rsCell (testEq 3) opk
                   (testEq_skip_imp Gam 4 3 opk w43 nieq)
      recL = Hsrc.recPL_g Gam c gNe
      recR = Hsrc.recPR_g Gam c gNe
      suPart : Term
      suPart = ap1 (C pi (constN 1) (lookupAt lIdx)) opk
      suPart_val : Deriv (imp Gam (eqF suPart (su# (ap1 srcF (pL c)))))
      suPart_val =
        impEqTrans suPart (ap2 pi (ap1 (constN 1) opk) (ap1 (lookupAt lIdx) opk))
                   (su# (ap1 srcF (pL c)))
          (liftP Gam (ax_C pi (constN 1) (lookupAt lIdx) opk))
          (impEqTrans (ap2 pi (ap1 (constN 1) opk) (ap1 (lookupAt lIdx) opk))
                      (ap2 pi (natCode 1) (ap1 (lookupAt lIdx) opk))
                      (su# (ap1 srcF (pL c)))
             (liftP Gam (congL pi (ap1 (lookupAt lIdx) opk) (constN_eq 1 opk)))
             (impCongR pi (ap1 (lookupAt lIdx) opk) (ap1 srcF (pL c)) (natCode 1) recL))
      innerC : Term
      innerC = ap1 (C pi (C pi (constN 1) (lookupAt lIdx)) (lookupAt rIdx)) opk
      inner_val : Deriv (imp Gam (eqF innerC (ap2 pi (su# (ap1 srcF (pL c))) (ap1 srcF (pR c)))))
      inner_val =
        impEqTrans innerC (ap2 pi suPart (ap1 (lookupAt rIdx) opk))
                   (ap2 pi (su# (ap1 srcF (pL c))) (ap1 srcF (pR c)))
          (liftP Gam (ax_C pi (C pi (constN 1) (lookupAt lIdx)) (lookupAt rIdx) opk))
          (impEqTrans (ap2 pi suPart (ap1 (lookupAt rIdx) opk))
                      (ap2 pi (su# (ap1 srcF (pL c))) (ap1 (lookupAt rIdx) opk))
                      (ap2 pi (su# (ap1 srcF (pL c))) (ap1 srcF (pR c)))
             (impCongL pi suPart (su# (ap1 srcF (pL c))) (ap1 (lookupAt rIdx) opk) suPart_val)
             (impCongR pi (ap1 (lookupAt rIdx) opk) (ap1 srcF (pR c)) (su# (ap1 srcF (pL c))) recR))
      cell_val : Deriv (imp Gam (eqF (ap1 rsCell opk) val))
      cell_val =
        impEqTrans (ap1 rsCell opk) (ap2 pi (ap1 (constN 2) opk) innerC) val
          (liftP Gam (ax_C pi (constN 2) (C pi (C pi (constN 1) (lookupAt lIdx)) (lookupAt rIdx)) opk))
          (impEqTrans (ap2 pi (ap1 (constN 2) opk) innerC) (ap2 pi (natCode 2) innerC) val
             (liftP Gam (congL pi innerC (constN_eq 2 opk)))
             (impCongR pi innerC (ap2 pi (su# (ap1 srcF (pL c))) (ap1 srcF (pR c))) (natCode 2) inner_val))
  in impEqTrans (ap1 srcF c) (ap1 Hsrc.sbf opk) val (Hsrc.unfold_g Gam c gNe)
       (impEqTrans (ap1 Hsrc.sbf opk) (ap1 cellNode opk) val (Hsrc.toNode_g Gam c gNe gNl)
          (impEqTrans (ap1 cellNode opk) (ap1 restAd opk) val toRestAd
             (impEqTrans (ap1 restAd opk) (ap1 restRO opk) val toRestRO
                (impEqTrans (ap1 restRO opk) (ap1 rsCell opk) val toRsCell cell_val))))

------------------------------------------------------------------------
-- Reject (gam-form):  dtag c not in {1,2,3,4}  =>  wfRed c = s O .
-- (Used to close the junk-tag branch of the Ad else sub-dispatch: a valid node
--  whose tag is none of Su/Ad/RO/RS contradicts  wfRed c = O .)

wfRed_op_reject_gam : (Gam : Formula) (c : Term) ->
  Deriv (imp Gam (neg (eqF c O))) ->
  Deriv (imp Gam (eqF (ap2 natEqF (ap1 Fst c) (natCode 1)) O)) ->
  Deriv (imp Gam (neg (eqF (dtag c) (natCode 1)))) ->
  Deriv (imp Gam (neg (eqF (dtag c) (natCode 2)))) ->
  Deriv (imp Gam (neg (eqF (dtag c) (natCode 3)))) ->
  Deriv (imp Gam (neg (eqF (dtag c) (natCode 4)))) ->
  Deriv (imp Gam (eqF (ap1 wfRed c) (ap1 s O)))
wfRed_op_reject_gam Gam c gNe gNl gn1 gn2 gn3 gn4 =
  let opk = Hwf.opkg c
      gSkip : (k : Nat) -> Deriv (imp Gam (neg (eqF (dtag c) (natCode k)))) ->
        Deriv (imp Gam (eqF (ap1 (testEq k) opk) O))
      gSkip k gnk =
        impEqTrans (ap1 (testEq k) opk) (ap2 natEqF (dtag c) (natCode k)) O
          (impEqTrans (ap1 (testEq k) opk) (ap2 natEqF (ap1 nIdx opk) (natCode k))
                      (ap2 natEqF (dtag c) (natCode k))
             (impLift (ruleTrans (ax_C natEqF nIdx (constN k) opk)
                        (congR natEqF (ap1 nIdx opk) (constN_eq k opk))))
             (impCongL natEqF (ap1 nIdx opk) (dtag c) (natCode k) (compI gNe (Hwf.op_nIdx_imp c))))
          (compI gnk (natEqF_complete (dtag c) (natCode k)))
      cell_fires : Deriv (imp Gam (eqF (ap1 wfCellNode opk) (ap1 rejectCell opk)))
      cell_fires =
        impEqTrans (ap1 wfCellNode opk) (ap1 wfRestAd opk) (ap1 rejectCell opk)
          (fork_false_to_snd_imp Gam (lookupAt lIdx) wfRestAd (testEq 1) opk (gSkip 1 gn1))
          (impEqTrans (ap1 wfRestAd opk) (ap1 wfRestRO opk) (ap1 rejectCell opk)
            (fork_false_to_snd_imp Gam wfAdCell wfRestRO (testEq 2) opk (gSkip 2 gn2))
            (impEqTrans (ap1 wfRestRO opk) (ap1 wfRestRS opk) (ap1 rejectCell opk)
              (fork_false_to_snd_imp Gam (lookupAt lIdx) wfRestRS (testEq 3) opk (gSkip 3 gn3))
              (fork_false_to_snd_imp Gam wfAdCell rejectCell (testEq 4) opk (gSkip 4 gn4))))
  in impEqTrans (ap1 wfRed c) (ap1 Hwf.sbf opk) (ap1 s O)
       (Hwf.unfold_g Gam c gNe)
       (impEqTrans (ap1 Hwf.sbf opk) (ap1 wfCellNode opk) (ap1 s O)
          (Hwf.toNode_g Gam c gNe gNl)
          (impEqTrans (ap1 wfCellNode opk) (ap1 rejectCell opk) (ap1 s O)
             cell_fires (impLift (constN_eq 1 opk))))
