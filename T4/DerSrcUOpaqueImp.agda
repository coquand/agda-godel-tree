{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.DerSrcUOpaqueImp -- IMP-FORM opaque srcF equations over the unsized coding,
-- carried under [negLeaf, htag] (nodes) / Hleaf (leaf), for the tag dispatch.
-- srcF is flat (no depth-2 Ad), so all five cases follow the triF Su/RO/RS
-- imp-form pattern (T4.DerTriUOpaqueImp).
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.DerSrcUOpaqueImp where

open import T4.Base

open import T4.DerCode using ( dgSu ; dgAd ; dgRO ; dgRS )
open import T4.DerCodeS using ( dtag ; pL ; pR )
open import T4.BinTree using ( nIdx ; lIdx ; rIdx )
open import T4.FoldRec using ( lookupAt ; fold ; get_newK )
open import T4.ParsObj using ( stepOf )
open import T4.ProgParse using ( get_tag )
open import T4.OpaqueLookup using ( lookup_op )
open import T4.WfRedExtract using ( pLValueBound ; pRValueBound )
open import T4.TrsCodeObj using ( ze# ; su# ; ad# )

open import T4.DerSrc
  using ( srcF ; ze#F ; suCell ; adCell ; roCell ; rsCell ; restAd ; restRO ; cellNode
        ; ze#F_at ; testEq ; w21 ; w31 ; w32 ; w41 ; w42 ; w43 )

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
  srcStepU : Fun1
  srcStepU = stepOf ze#F cellNode
open T4.OpaqueHarness.H srcStepU

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
    Deriv (eqF (ap1 (lookupAt lIdx) (opkg p)) (ap1 srcF (pL p)))
  recPL p ne = lookup_op Z srcStepU lIdx (ap1 predecessor p) (pL p)
                 (op_pL p ne) (pLValueBound p ne)
  recPR : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 (lookupAt rIdx) (opkg p)) (ap1 srcF (pR p)))
  recPR p ne = lookup_op Z srcStepU rIdx (ap1 predecessor p) (pR p)
                 (op_pR p ne) (pRValueBound p ne)

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
    step2 : Deriv (imp negLeaf (imp htag (eqF (ap1 srcStepU opk) (ap1 cellNode opk))))
    step2 = compI (fork_false_to_snd_imp negLeaf ze#F cellNode
                     (C natEqF get_tag (constN 1)) opk nl_neg)
                  (axK (eqF (ap1 srcStepU opk) (ap1 cellNode opk)) htag)
    nieq_imp : Deriv (imp htag (eqF (ap1 nIdx opk) lbl))
    nieq_imp = impEqTrans (ap1 nIdx opk) (dtag p) lbl
                 (impLift (op_nIdx p ne)) (identP htag)

------------------------------------------------------------------------
-- Ze :  srcF p = ze# .

srcF_op_Ze_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (eqF (ap1 Fst p) (natCode 1)) (eqF (ap1 srcF p) ze#))
srcF_op_Ze_imp p ne =
  let opk = opkg p
      Hleaf : Formula
      Hleaf = eqF (ap1 Fst p) (natCode 1)
      gtag : Deriv (imp Hleaf (eqF (ap1 get_tag opk) (natCode 1)))
      gtag = impEqTrans (ap1 get_tag opk) (ap1 Fst p) (natCode 1)
               (impLift (op_tag p ne)) (identP Hleaf)
      cell_fires : Deriv (imp Hleaf (eqF (ap1 srcStepU opk) (ap1 ze#F opk)))
      cell_fires = fork_true_to_fst_imp Hleaf ze#F cellNode (C natEqF get_tag (constN 1)) opk
                     (natEqFire_imp Hleaf get_tag 1 opk gtag)
  in impEqTrans (ap1 srcF p) (ap1 srcStepU opk) ze#
       (impLift (opUnfold p ne))
       (impEqTrans (ap1 srcStepU opk) (ap1 ze#F opk) ze# cell_fires (impLift (ze#F_at opk)))

------------------------------------------------------------------------
-- Su :  srcF p = su# (srcF (pL p)) .

srcF_op_Su_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (dtag p) dgSu) (eqF (ap1 srcF p) (su# (ap1 srcF (pL p))))))
srcF_op_Su_imp p ne =
  let open Node p ne dgSu
      node_fires : Deriv (imp htag (eqF (ap1 cellNode opk) (ap1 suCell opk)))
      node_fires = fork_true_to_fst_imp htag suCell restAd (testEq 1) opk
                     (testEq_fire_imp htag 1 opk nieq_imp)
      suCell_val : Deriv (eqF (ap1 suCell opk) (su# (ap1 srcF (pL p))))
      suCell_val =
        ruleTrans (ax_C pi (constN 1) (lookupAt lIdx) opk)
          (ruleTrans (congL pi (ap1 (lookupAt lIdx) opk) (constN_eq 1 opk))
                     (congR pi (natCode 1) (recPL p ne)))
  in trans2c (ap1 srcF p) (ap1 srcStepU opk) (su# (ap1 srcF (pL p)))
       (lift2 negLeaf htag (opUnfold p ne))
       (trans2c (ap1 srcStepU opk) (ap1 cellNode opk) (su# (ap1 srcF (pL p))) step2
         (trans2c (ap1 cellNode opk) (ap1 suCell opk) (su# (ap1 srcF (pL p)))
           (liftP negLeaf node_fires) (lift2 negLeaf htag suCell_val)))

------------------------------------------------------------------------
-- Ad :  srcF p = ad# (srcF (pL p)) (srcF (pR p)) .

srcF_op_Ad_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (dtag p) dgAd)
                  (eqF (ap1 srcF p) (ad# (ap1 srcF (pL p)) (ap1 srcF (pR p))))))
srcF_op_Ad_imp p ne =
  let open Node p ne dgAd
      node_fires : Deriv (imp htag (eqF (ap1 cellNode opk) (ap1 adCell opk)))
      node_fires =
        impEqTrans (ap1 cellNode opk) (ap1 restAd opk) (ap1 adCell opk)
          (fork_false_to_snd_imp htag suCell restAd (testEq 1) opk
             (testEq_skip_imp htag 2 1 opk w21 nieq_imp))
          (fork_true_to_fst_imp htag adCell restRO (testEq 2) opk
             (testEq_fire_imp htag 2 opk nieq_imp))
      inner_val : Deriv (eqF (ap1 (C pi (lookupAt lIdx) (lookupAt rIdx)) opk)
                             (ap2 pi (ap1 srcF (pL p)) (ap1 srcF (pR p))))
      inner_val =
        ruleTrans (ax_C pi (lookupAt lIdx) (lookupAt rIdx) opk)
          (ruleTrans (congL pi (ap1 (lookupAt rIdx) opk) (recPL p ne))
                     (congR pi (ap1 srcF (pL p)) (recPR p ne)))
      adCell_val : Deriv (eqF (ap1 adCell opk) (ad# (ap1 srcF (pL p)) (ap1 srcF (pR p))))
      adCell_val =
        ruleTrans (ax_C pi (constN 2) (C pi (lookupAt lIdx) (lookupAt rIdx)) opk)
          (ruleTrans (congL pi (ap1 (C pi (lookupAt lIdx) (lookupAt rIdx)) opk) (constN_eq 2 opk))
                     (congR pi (natCode 2) inner_val))
  in trans2c (ap1 srcF p) (ap1 srcStepU opk) (ad# (ap1 srcF (pL p)) (ap1 srcF (pR p)))
       (lift2 negLeaf htag (opUnfold p ne))
       (trans2c (ap1 srcStepU opk) (ap1 cellNode opk) (ad# (ap1 srcF (pL p)) (ap1 srcF (pR p))) step2
         (trans2c (ap1 cellNode opk) (ap1 adCell opk) (ad# (ap1 srcF (pL p)) (ap1 srcF (pR p)))
           (liftP negLeaf node_fires) (lift2 negLeaf htag adCell_val)))

------------------------------------------------------------------------
-- RO :  srcF p = ad# ze# (srcF (pL p)) .

srcF_op_RO_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (dtag p) dgRO) (eqF (ap1 srcF p) (ad# ze# (ap1 srcF (pL p))))))
srcF_op_RO_imp p ne =
  let open Node p ne dgRO
      node_fires : Deriv (imp htag (eqF (ap1 cellNode opk) (ap1 roCell opk)))
      node_fires =
        impEqTrans (ap1 cellNode opk) (ap1 restAd opk) (ap1 roCell opk)
          (fork_false_to_snd_imp htag suCell restAd (testEq 1) opk
             (testEq_skip_imp htag 3 1 opk w31 nieq_imp))
          (impEqTrans (ap1 restAd opk) (ap1 restRO opk) (ap1 roCell opk)
            (fork_false_to_snd_imp htag adCell restRO (testEq 2) opk
               (testEq_skip_imp htag 3 2 opk w32 nieq_imp))
            (fork_true_to_fst_imp htag roCell rsCell (testEq 3) opk
               (testEq_fire_imp htag 3 opk nieq_imp)))
      inner_val : Deriv (eqF (ap1 (C pi ze#F (lookupAt lIdx)) opk) (ap2 pi ze# (ap1 srcF (pL p))))
      inner_val =
        ruleTrans (ax_C pi ze#F (lookupAt lIdx) opk)
          (ruleTrans (congL pi (ap1 (lookupAt lIdx) opk) (ze#F_at opk))
                     (congR pi ze# (recPL p ne)))
      roCell_val : Deriv (eqF (ap1 roCell opk) (ad# ze# (ap1 srcF (pL p))))
      roCell_val =
        ruleTrans (ax_C pi (constN 2) (C pi ze#F (lookupAt lIdx)) opk)
          (ruleTrans (congL pi (ap1 (C pi ze#F (lookupAt lIdx)) opk) (constN_eq 2 opk))
                     (congR pi (natCode 2) inner_val))
  in trans2c (ap1 srcF p) (ap1 srcStepU opk) (ad# ze# (ap1 srcF (pL p)))
       (lift2 negLeaf htag (opUnfold p ne))
       (trans2c (ap1 srcStepU opk) (ap1 cellNode opk) (ad# ze# (ap1 srcF (pL p))) step2
         (trans2c (ap1 cellNode opk) (ap1 roCell opk) (ad# ze# (ap1 srcF (pL p)))
           (liftP negLeaf node_fires) (lift2 negLeaf htag roCell_val)))

------------------------------------------------------------------------
-- RS :  srcF p = ad# (su# (srcF (pL p))) (srcF (pR p)) .

srcF_op_RS_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (dtag p) dgRS)
                  (eqF (ap1 srcF p) (ad# (su# (ap1 srcF (pL p))) (ap1 srcF (pR p))))))
srcF_op_RS_imp p ne =
  let open Node p ne dgRS
      node_fires : Deriv (imp htag (eqF (ap1 cellNode opk) (ap1 rsCell opk)))
      node_fires =
        impEqTrans (ap1 cellNode opk) (ap1 restAd opk) (ap1 rsCell opk)
          (fork_false_to_snd_imp htag suCell restAd (testEq 1) opk
             (testEq_skip_imp htag 4 1 opk w41 nieq_imp))
          (impEqTrans (ap1 restAd opk) (ap1 restRO opk) (ap1 rsCell opk)
            (fork_false_to_snd_imp htag adCell restRO (testEq 2) opk
               (testEq_skip_imp htag 4 2 opk w42 nieq_imp))
            (fork_false_to_snd_imp htag roCell rsCell (testEq 3) opk
               (testEq_skip_imp htag 4 3 opk w43 nieq_imp)))
      left_val : Deriv (eqF (ap1 (C pi (constN 1) (lookupAt lIdx)) opk) (su# (ap1 srcF (pL p))))
      left_val =
        ruleTrans (ax_C pi (constN 1) (lookupAt lIdx) opk)
          (ruleTrans (congL pi (ap1 (lookupAt lIdx) opk) (constN_eq 1 opk))
                     (congR pi (natCode 1) (recPL p ne)))
      inner_val : Deriv (eqF (ap1 (C pi (C pi (constN 1) (lookupAt lIdx)) (lookupAt rIdx)) opk)
                             (ap2 pi (su# (ap1 srcF (pL p))) (ap1 srcF (pR p))))
      inner_val =
        ruleTrans (ax_C pi (C pi (constN 1) (lookupAt lIdx)) (lookupAt rIdx) opk)
          (ruleTrans (congL pi (ap1 (lookupAt rIdx) opk) left_val)
                     (congR pi (su# (ap1 srcF (pL p))) (recPR p ne)))
      rsCell_val : Deriv (eqF (ap1 rsCell opk) (ad# (su# (ap1 srcF (pL p))) (ap1 srcF (pR p))))
      rsCell_val =
        ruleTrans (ax_C pi (constN 2) (C pi (C pi (constN 1) (lookupAt lIdx)) (lookupAt rIdx)) opk)
          (ruleTrans (congL pi (ap1 (C pi (C pi (constN 1) (lookupAt lIdx)) (lookupAt rIdx)) opk)
                         (constN_eq 2 opk))
                     (congR pi (natCode 2) inner_val))
  in trans2c (ap1 srcF p) (ap1 srcStepU opk) (ad# (su# (ap1 srcF (pL p))) (ap1 srcF (pR p)))
       (lift2 negLeaf htag (opUnfold p ne))
       (trans2c (ap1 srcStepU opk) (ap1 cellNode opk)
            (ad# (su# (ap1 srcF (pL p))) (ap1 srcF (pR p))) step2
         (trans2c (ap1 cellNode opk) (ap1 rsCell opk)
            (ad# (su# (ap1 srcF (pL p))) (ap1 srcF (pR p)))
           (liftP negLeaf node_fires) (lift2 negLeaf htag rsCell_val)))
