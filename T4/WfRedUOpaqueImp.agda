{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.WfRedUOpaqueImp -- IMP-FORM opaque wfRed equations over the unsized coding,
-- under [negLeaf, htag] / Hleaf, for the tag dispatch (child-validity extraction).
-- Mirrors T4.DerSrcUOpaqueImp; the reject case is handled in the dispatch.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.WfRedUOpaqueImp where

open import T4.Base

open import T4.DerCode using ( dgSu ; dgAd ; dgRO ; dgRS )
open import T4.DerCodeS using ( dtag ; pL ; pR )
open import T4.BinTree using ( nIdx ; lIdx ; rIdx )
open import T4.FoldRec using ( lookupAt ; fold ; get_newK )
open import T4.ParsObj using ( stepOf )
open import T4.ProgParse using ( get_tag )
open import T4.OpaqueLookup using ( lookup_op )
open import T4.WfRedExtract using ( pLValueBound ; pRValueBound )

open import T4.WfRed
  using ( wfRed ; wfAdCell ; rejectCell ; wfRestRS ; wfRestRO ; wfRestAd ; wfCellNode )
open import T4.DerSrc using ( testEq ; w21 ; w31 ; w32 ; w41 ; w42 ; w43 )

open import T4.ForkImp
  using ( fork_true_to_fst_imp ; fork_false_to_snd_imp ; testEq_fire_imp ; testEq_skip_imp
        ; natEqFire_imp )
open import T4.CtxKit using ( lift2 ; trans2c )
open import T4.NatEqReflect using ( natEqF_complete )
open import T4.Thm12.ImpHelpers using ( impLift ; impEqTrans )

open import BRA3.Church       using ( pi ; predecessor )
open import BRA3.PairAlgebra  using ( compose1U_eq )
open import BRA3.SubT.NatEq    using ( natEqF )
open import BRA3.Contrapositive using ( compI ; liftP ; identP )

import T4.OpaqueHarness
private
  wfStepU : Fun1
  wfStepU = stepOf Z wfCellNode
open T4.OpaqueHarness.HBase rejectCell wfStepU

private
  op_tag : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 get_tag (opkg p)) (ap1 Fst p))
  op_tag p ne =
    ruleTrans (compose1U_eq Fst get_newK (opkg p)) (cong1 Fst (op_newK p ne))

  test1At : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 (C natEqF get_tag (constN 1)) (opkg p))
               (ap2 natEqF (ap1 Fst p) (natCode 1)))
  test1At p ne =
    ruleTrans (ax_C natEqF get_tag (constN 1) (opkg p))
      (ruleTrans (congL natEqF (ap1 (constN 1) (opkg p)) (op_tag p ne))
                 (congR natEqF (ap1 Fst p) (constN_eq 1 (opkg p))))

  recPL : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 (lookupAt lIdx) (opkg p)) (ap1 wfRed (pL p)))
  recPL p ne = lookup_op rejectCell wfStepU lIdx (ap1 predecessor p) (pL p)
                 (op_pL p ne) (pLValueBound p ne)
  recPR : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 (lookupAt rIdx) (opkg p)) (ap1 wfRed (pR p)))
  recPR p ne = lookup_op rejectCell wfStepU rIdx (ap1 predecessor p) (pR p)
                 (op_pR p ne) (pRValueBound p ne)

  adCell_val : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 wfAdCell (opkg p)) (ap2 pi (ap1 wfRed (pL p)) (ap1 wfRed (pR p))))
  adCell_val p ne =
    let opk = opkg p in
    ruleTrans (ax_C pi (lookupAt lIdx) (lookupAt rIdx) opk)
      (ruleTrans (congL pi (ap1 (lookupAt rIdx) opk) (recPL p ne))
                 (congR pi (ap1 wfRed (pL p)) (recPR p ne)))

  module Node (p : Term) (ne : Deriv (neg (eqF p O))) (lbl : Term) where
    opk = opkg p
    negLeaf : Formula
    negLeaf = neg (eqF (ap1 Fst p) (natCode 1))
    htag : Formula
    htag = eqF (dtag p) lbl
    t1f : Term
    t1f = ap1 (C natEqF get_tag (constN 1)) opk
    nl_neg : Deriv (imp negLeaf (eqF t1f O))
    nl_neg = impEqTrans t1f (ap2 natEqF (ap1 Fst p) (natCode 1)) O
               (impLift (test1At p ne)) (natEqF_complete (ap1 Fst p) (natCode 1))
    step2 : Deriv (imp negLeaf (imp htag (eqF (ap1 wfStepU opk) (ap1 wfCellNode opk))))
    step2 = compI (fork_false_to_snd_imp negLeaf Z wfCellNode
                     (C natEqF get_tag (constN 1)) opk nl_neg)
                  (axK (eqF (ap1 wfStepU opk) (ap1 wfCellNode opk)) htag)
    nieq_imp : Deriv (imp htag (eqF (ap1 nIdx opk) lbl))
    nieq_imp = impEqTrans (ap1 nIdx opk) (dtag p) lbl
                 (impLift (op_nIdx p ne)) (identP htag)

------------------------------------------------------------------------
-- Ze :  wfRed p = O .

wfRed_op_Ze_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (eqF (ap1 Fst p) (natCode 1)) (eqF (ap1 wfRed p) O))
wfRed_op_Ze_imp p ne =
  let opk = opkg p
      Hleaf : Formula
      Hleaf = eqF (ap1 Fst p) (natCode 1)
      gtag : Deriv (imp Hleaf (eqF (ap1 get_tag opk) (natCode 1)))
      gtag = impEqTrans (ap1 get_tag opk) (ap1 Fst p) (natCode 1)
               (impLift (op_tag p ne)) (identP Hleaf)
      cell_fires : Deriv (imp Hleaf (eqF (ap1 wfStepU opk) (ap1 Z opk)))
      cell_fires = fork_true_to_fst_imp Hleaf Z wfCellNode (C natEqF get_tag (constN 1)) opk
                     (natEqFire_imp Hleaf get_tag 1 opk gtag)
  in impEqTrans (ap1 wfRed p) (ap1 wfStepU opk) O
       (impLift (opUnfold p ne))
       (impEqTrans (ap1 wfStepU opk) (ap1 Z opk) O cell_fires (impLift (axZ opk)))

------------------------------------------------------------------------
-- Su :  wfRed p = wfRed (pL p) .

wfRed_op_Su_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (dtag p) dgSu) (eqF (ap1 wfRed p) (ap1 wfRed (pL p)))))
wfRed_op_Su_imp p ne =
  let open Node p ne dgSu
      node_fires : Deriv (imp htag (eqF (ap1 wfCellNode opk) (ap1 (lookupAt lIdx) opk)))
      node_fires = fork_true_to_fst_imp htag (lookupAt lIdx) wfRestAd (testEq 1) opk
                     (testEq_fire_imp htag 1 opk nieq_imp)
  in trans2c (ap1 wfRed p) (ap1 wfStepU opk) (ap1 wfRed (pL p))
       (lift2 negLeaf htag (opUnfold p ne))
       (trans2c (ap1 wfStepU opk) (ap1 wfCellNode opk) (ap1 wfRed (pL p)) step2
         (trans2c (ap1 wfCellNode opk) (ap1 (lookupAt lIdx) opk) (ap1 wfRed (pL p))
           (liftP negLeaf node_fires) (lift2 negLeaf htag (recPL p ne))))

------------------------------------------------------------------------
-- Ad :  wfRed p = pi (wfRed (pL p)) (wfRed (pR p)) .

wfRed_op_Ad_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (dtag p) dgAd)
                  (eqF (ap1 wfRed p) (ap2 pi (ap1 wfRed (pL p)) (ap1 wfRed (pR p))))))
wfRed_op_Ad_imp p ne =
  let open Node p ne dgAd
      rhs : Term
      rhs = ap2 pi (ap1 wfRed (pL p)) (ap1 wfRed (pR p))
      node_fires : Deriv (imp htag (eqF (ap1 wfCellNode opk) (ap1 wfAdCell opk)))
      node_fires =
        impEqTrans (ap1 wfCellNode opk) (ap1 wfRestAd opk) (ap1 wfAdCell opk)
          (fork_false_to_snd_imp htag (lookupAt lIdx) wfRestAd (testEq 1) opk
             (testEq_skip_imp htag 2 1 opk w21 nieq_imp))
          (fork_true_to_fst_imp htag wfAdCell wfRestRO (testEq 2) opk
             (testEq_fire_imp htag 2 opk nieq_imp))
  in trans2c (ap1 wfRed p) (ap1 wfStepU opk) rhs
       (lift2 negLeaf htag (opUnfold p ne))
       (trans2c (ap1 wfStepU opk) (ap1 wfCellNode opk) rhs step2
         (trans2c (ap1 wfCellNode opk) (ap1 wfAdCell opk) rhs
           (liftP negLeaf node_fires) (lift2 negLeaf htag (adCell_val p ne))))

------------------------------------------------------------------------
-- RO :  wfRed p = wfRed (pL p) .

wfRed_op_RO_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (dtag p) dgRO) (eqF (ap1 wfRed p) (ap1 wfRed (pL p)))))
wfRed_op_RO_imp p ne =
  let open Node p ne dgRO
      node_fires : Deriv (imp htag (eqF (ap1 wfCellNode opk) (ap1 (lookupAt lIdx) opk)))
      node_fires =
        impEqTrans (ap1 wfCellNode opk) (ap1 wfRestAd opk) (ap1 (lookupAt lIdx) opk)
          (fork_false_to_snd_imp htag (lookupAt lIdx) wfRestAd (testEq 1) opk
             (testEq_skip_imp htag 3 1 opk w31 nieq_imp))
          (impEqTrans (ap1 wfRestAd opk) (ap1 wfRestRO opk) (ap1 (lookupAt lIdx) opk)
            (fork_false_to_snd_imp htag wfAdCell wfRestRO (testEq 2) opk
               (testEq_skip_imp htag 3 2 opk w32 nieq_imp))
            (fork_true_to_fst_imp htag (lookupAt lIdx) wfRestRS (testEq 3) opk
               (testEq_fire_imp htag 3 opk nieq_imp)))
  in trans2c (ap1 wfRed p) (ap1 wfStepU opk) (ap1 wfRed (pL p))
       (lift2 negLeaf htag (opUnfold p ne))
       (trans2c (ap1 wfStepU opk) (ap1 wfCellNode opk) (ap1 wfRed (pL p)) step2
         (trans2c (ap1 wfCellNode opk) (ap1 (lookupAt lIdx) opk) (ap1 wfRed (pL p))
           (liftP negLeaf node_fires) (lift2 negLeaf htag (recPL p ne))))

------------------------------------------------------------------------
-- RS :  wfRed p = pi (wfRed (pL p)) (wfRed (pR p)) .

wfRed_op_RS_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (dtag p) dgRS)
                  (eqF (ap1 wfRed p) (ap2 pi (ap1 wfRed (pL p)) (ap1 wfRed (pR p))))))
wfRed_op_RS_imp p ne =
  let open Node p ne dgRS
      rhs : Term
      rhs = ap2 pi (ap1 wfRed (pL p)) (ap1 wfRed (pR p))
      node_fires : Deriv (imp htag (eqF (ap1 wfCellNode opk) (ap1 wfAdCell opk)))
      node_fires =
        impEqTrans (ap1 wfCellNode opk) (ap1 wfRestAd opk) (ap1 wfAdCell opk)
          (fork_false_to_snd_imp htag (lookupAt lIdx) wfRestAd (testEq 1) opk
             (testEq_skip_imp htag 4 1 opk w41 nieq_imp))
          (impEqTrans (ap1 wfRestAd opk) (ap1 wfRestRO opk) (ap1 wfAdCell opk)
            (fork_false_to_snd_imp htag wfAdCell wfRestRO (testEq 2) opk
               (testEq_skip_imp htag 4 2 opk w42 nieq_imp))
            (impEqTrans (ap1 wfRestRO opk) (ap1 wfRestRS opk) (ap1 wfAdCell opk)
              (fork_false_to_snd_imp htag (lookupAt lIdx) wfRestRS (testEq 3) opk
                 (testEq_skip_imp htag 4 3 opk w43 nieq_imp))
              (fork_true_to_fst_imp htag wfAdCell (constN 1) (testEq 4) opk
                 (testEq_fire_imp htag 4 opk nieq_imp))))
  in trans2c (ap1 wfRed p) (ap1 wfStepU opk) rhs
       (lift2 negLeaf htag (opUnfold p ne))
       (trans2c (ap1 wfStepU opk) (ap1 wfCellNode opk) rhs step2
         (trans2c (ap1 wfCellNode opk) (ap1 wfAdCell opk) rhs
           (liftP negLeaf node_fires) (lift2 negLeaf htag (adCell_val p ne))))
