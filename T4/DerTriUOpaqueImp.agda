{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.DerTriUOpaqueImp -- IMP-FORM opaque triF equations over the unsized coding,
-- carried under the two dispatch antecedents
--   negLeaf = neg (Fst sK = natCode 1)   (the node branch: test1 skips)
--   htag    = (dtag sK = dgX)             (the label branch)
-- as needed by the object tag dispatch (caseElim exposes both as antecedents).
--
-- This validates the imp-form technique for the unsized coding; the remaining
-- tags / functions follow the same ForkImp + CtxKit pattern.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.DerTriUOpaqueImp where

open import T4.Base

open import T4.DerCode using ( derZe ; derSu ; derAd ; dgSu ; dgAd ; dgRO ; dgRS ; filler )
open import T4.DerCodeS using ( dtag ; pL ; pR )
open import T4.BinTree using ( nIdx ; lIdx ; rIdx )
open import T4.FoldRec using ( lookupAt ; fold ; get_newK )
open import T4.ParsObj using ( stepOf )
open import T4.ProgParse using ( get_tag )
open import T4.OpaqueLookup using ( lookup_op )
open import T4.WfRedExtract using ( pLValueBound ; pRValueBound )

open import T4.DerTri
  using ( triF ; cellLeafTri ; cellNodeTri ; suNodeCell ; roNodeCell ; rsNodeCell
        ; adCellTri ; restAdTri ; restROTri ; adExprRS ; cellLeafTri_at )
open import T4.DerSrc using ( testEq ; w31 ; w32 ; w41 ; w42 ; w43 )

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
  triStepU : Fun1
  triStepU = stepOf cellLeafTri cellNodeTri
open T4.OpaqueHarness.H triStepU

------------------------------------------------------------------------
-- Shared:  op_tag / test1 value.

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

------------------------------------------------------------------------
-- Su (imp-form):  imp negLeaf (imp htag (triF p = derSu (triF (pL p)))) .

triF_op_Su_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (dtag p) dgSu)
                  (eqF (ap1 triF p) (derSu (ap1 triF (pL p))))))
triF_op_Su_imp p ne =
  let opk = opkg p
      negLeaf : Formula
      negLeaf = neg (eqF (ap1 Fst p) (natCode 1))
      htag : Formula
      htag = eqF (dtag p) dgSu
      t1f : Term
      t1f = ap1 (C natEqF get_tag (constN 1)) opk
      -- (1) bare unfold,  triF p = triStepU opk .
      step1 : Deriv (imp negLeaf (imp htag (eqF (ap1 triF p) (ap1 triStepU opk))))
      step1 = lift2 negLeaf htag (opUnfold p ne)
      -- (2) test1 skips  =>  triStepU opk = cellNodeTri opk  (under negLeaf).
      nl_neg : Deriv (imp negLeaf (eqF t1f O))
      nl_neg = impEqTrans t1f (ap2 natEqF (ap1 Fst p) (natCode 1)) O
                 (impLift (test1At p ne))
                 (natEqF_complete (ap1 Fst p) (natCode 1))
      toNode_neg : Deriv (imp negLeaf (eqF (ap1 triStepU opk) (ap1 cellNodeTri opk)))
      toNode_neg = fork_false_to_snd_imp negLeaf cellLeafTri cellNodeTri
                     (C natEqF get_tag (constN 1)) opk nl_neg
      step2 : Deriv (imp negLeaf (imp htag (eqF (ap1 triStepU opk) (ap1 cellNodeTri opk))))
      step2 = compI toNode_neg (axK (eqF (ap1 triStepU opk) (ap1 cellNodeTri opk)) htag)
      -- (3) label fires  =>  cellNodeTri opk = suNodeCell opk  (under htag).
      nieq_imp : Deriv (imp htag (eqF (ap1 nIdx opk) dgSu))
      nieq_imp = impEqTrans (ap1 nIdx opk) (dtag p) dgSu
                   (impLift (op_nIdx p ne)) (identP htag)
      node_fires_htag : Deriv (imp htag (eqF (ap1 cellNodeTri opk) (ap1 suNodeCell opk)))
      node_fires_htag = fork_true_to_fst_imp htag suNodeCell restAdTri (testEq 1) opk
                          (testEq_fire_imp htag 1 opk nieq_imp)
      step3 : Deriv (imp negLeaf (imp htag (eqF (ap1 cellNodeTri opk) (ap1 suNodeCell opk))))
      step3 = liftP negLeaf node_fires_htag
      -- (4) bare cell value,  suNodeCell opk = derSu (triF (pL p)) .
      recL : Deriv (eqF (ap1 (lookupAt lIdx) opk) (ap1 triF (pL p)))
      recL = lookup_op Z triStepU lIdx (ap1 predecessor p) (pL p)
               (op_pL p ne) (pLValueBound p ne)
      inner_val : Deriv (eqF (ap1 (C pi (lookupAt lIdx) cellLeafTri) opk)
                             (ap2 pi (ap1 triF (pL p)) filler))
      inner_val =
        ruleTrans (ax_C pi (lookupAt lIdx) cellLeafTri opk)
          (ruleTrans (congL pi (ap1 cellLeafTri opk) recL)
                     (congR pi (ap1 triF (pL p)) (cellLeafTri_at opk)))
      mid_val : Deriv (eqF (ap1 (C pi (constN 1) (C pi (lookupAt lIdx) cellLeafTri)) opk)
                           (ap2 pi dgSu (ap2 pi (ap1 triF (pL p)) filler)))
      mid_val =
        ruleTrans (ax_C pi (constN 1) (C pi (lookupAt lIdx) cellLeafTri) opk)
          (ruleTrans (congL pi (ap1 (C pi (lookupAt lIdx) cellLeafTri) opk) (constN_eq 1 opk))
                     (congR pi (natCode 1) inner_val))
      suNodeCell_val : Deriv (eqF (ap1 suNodeCell opk) (derSu (ap1 triF (pL p))))
      suNodeCell_val =
        ruleTrans (ax_C pi (constN 2) (C pi (constN 1) (C pi (lookupAt lIdx) cellLeafTri)) opk)
          (ruleTrans (congL pi (ap1 (C pi (constN 1) (C pi (lookupAt lIdx) cellLeafTri)) opk)
                         (constN_eq 2 opk))
                     (congR pi (natCode 2) mid_val))
      step4 : Deriv (imp negLeaf (imp htag (eqF (ap1 suNodeCell opk) (derSu (ap1 triF (pL p))))))
      step4 = lift2 negLeaf htag suNodeCell_val
  in trans2c (ap1 triF p) (ap1 triStepU opk) (derSu (ap1 triF (pL p)))
       step1
       (trans2c (ap1 triStepU opk) (ap1 cellNodeTri opk) (derSu (ap1 triF (pL p)))
         step2
         (trans2c (ap1 cellNodeTri opk) (ap1 suNodeCell opk) (derSu (ap1 triF (pL p)))
           step3 step4))

------------------------------------------------------------------------
-- Ze (imp-form, single antecedent  Hleaf = (Fst p = natCode 1)).

triF_op_Ze_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (eqF (ap1 Fst p) (natCode 1)) (eqF (ap1 triF p) derZe))
triF_op_Ze_imp p ne =
  let opk = opkg p
      Hleaf : Formula
      Hleaf = eqF (ap1 Fst p) (natCode 1)
      gtag : Deriv (imp Hleaf (eqF (ap1 get_tag opk) (natCode 1)))
      gtag = impEqTrans (ap1 get_tag opk) (ap1 Fst p) (natCode 1)
               (impLift (op_tag p ne)) (identP Hleaf)
      t1fire : Deriv (imp Hleaf (eqF (ap1 (C natEqF get_tag (constN 1)) opk) (ap1 s O)))
      t1fire = natEqFire_imp Hleaf get_tag 1 opk gtag
      cell_fires : Deriv (imp Hleaf (eqF (ap1 triStepU opk) (ap1 cellLeafTri opk)))
      cell_fires = fork_true_to_fst_imp Hleaf cellLeafTri cellNodeTri
                     (C natEqF get_tag (constN 1)) opk t1fire
  in impEqTrans (ap1 triF p) (ap1 triStepU opk) derZe
       (impLift (opUnfold p ne))
       (impEqTrans (ap1 triStepU opk) (ap1 cellLeafTri opk) derZe
         cell_fires (impLift (cellLeafTri_at opk)))

------------------------------------------------------------------------
-- Shared node-branch pieces for the double-antecedent [negLeaf, htag] tags.

private
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
    toNode_neg : Deriv (imp negLeaf (eqF (ap1 triStepU opk) (ap1 cellNodeTri opk)))
    toNode_neg = fork_false_to_snd_imp negLeaf cellLeafTri cellNodeTri
                   (C natEqF get_tag (constN 1)) opk nl_neg
    step1 : {X : Formula} -> Deriv (imp negLeaf (imp htag (eqF (ap1 triF p) (ap1 triStepU opk))))
    step1 = lift2 negLeaf htag (opUnfold p ne)
    step2 : Deriv (imp negLeaf (imp htag (eqF (ap1 triStepU opk) (ap1 cellNodeTri opk))))
    step2 = compI toNode_neg (axK (eqF (ap1 triStepU opk) (ap1 cellNodeTri opk)) htag)
    nieq_imp : Deriv (imp htag (eqF (ap1 nIdx opk) lbl))
    nieq_imp = impEqTrans (ap1 nIdx opk) (dtag p) lbl
                 (impLift (op_nIdx p ne)) (identP htag)

------------------------------------------------------------------------
-- RO (imp-form):  imp negLeaf (imp htag (triF p = triF (pL p))) .

triF_op_RO_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (dtag p) dgRO) (eqF (ap1 triF p) (ap1 triF (pL p)))))
triF_op_RO_imp p ne =
  let open Node p ne dgRO
      node_fires : Deriv (imp htag (eqF (ap1 cellNodeTri opk) (ap1 roNodeCell opk)))
      node_fires =
        impEqTrans (ap1 cellNodeTri opk) (ap1 restAdTri opk) (ap1 roNodeCell opk)
          (fork_false_to_snd_imp htag suNodeCell restAdTri (testEq 1) opk
             (testEq_skip_imp htag 3 1 opk w31 nieq_imp))
          (impEqTrans (ap1 restAdTri opk) (ap1 restROTri opk) (ap1 roNodeCell opk)
            (fork_false_to_snd_imp htag adCellTri restROTri (testEq 2) opk
               (testEq_skip_imp htag 3 2 opk w32 nieq_imp))
            (fork_true_to_fst_imp htag roNodeCell rsNodeCell (testEq 3) opk
               (testEq_fire_imp htag 3 opk nieq_imp)))
      recL : Deriv (eqF (ap1 (lookupAt lIdx) opk) (ap1 triF (pL p)))
      recL = lookup_op Z triStepU lIdx (ap1 predecessor p) (pL p)
               (op_pL p ne) (pLValueBound p ne)
  in trans2c (ap1 triF p) (ap1 triStepU opk) (ap1 triF (pL p))
       (lift2 negLeaf htag (opUnfold p ne))
       (trans2c (ap1 triStepU opk) (ap1 cellNodeTri opk) (ap1 triF (pL p)) step2
         (trans2c (ap1 cellNodeTri opk) (ap1 roNodeCell opk) (ap1 triF (pL p))
           (liftP negLeaf node_fires) (lift2 negLeaf htag recL)))

------------------------------------------------------------------------
-- RS (imp-form):  imp negLeaf (imp htag (triF p = derSu (derAd (triF (pL p)) (triF (pR p))))) .

triF_op_RS_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (dtag p) dgRS)
                  (eqF (ap1 triF p) (derSu (derAd (ap1 triF (pL p)) (ap1 triF (pR p)))))))
triF_op_RS_imp p ne =
  let open Node p ne dgRS
      node_fires : Deriv (imp htag (eqF (ap1 cellNodeTri opk) (ap1 rsNodeCell opk)))
      node_fires =
        impEqTrans (ap1 cellNodeTri opk) (ap1 restAdTri opk) (ap1 rsNodeCell opk)
          (fork_false_to_snd_imp htag suNodeCell restAdTri (testEq 1) opk
             (testEq_skip_imp htag 4 1 opk w41 nieq_imp))
          (impEqTrans (ap1 restAdTri opk) (ap1 restROTri opk) (ap1 rsNodeCell opk)
            (fork_false_to_snd_imp htag adCellTri restROTri (testEq 2) opk
               (testEq_skip_imp htag 4 2 opk w42 nieq_imp))
            (fork_false_to_snd_imp htag roNodeCell rsNodeCell (testEq 3) opk
               (testEq_skip_imp htag 4 3 opk w43 nieq_imp)))
      recL : Deriv (eqF (ap1 (lookupAt lIdx) opk) (ap1 triF (pL p)))
      recL = lookup_op Z triStepU lIdx (ap1 predecessor p) (pL p)
               (op_pL p ne) (pLValueBound p ne)
      recR : Deriv (eqF (ap1 (lookupAt rIdx) opk) (ap1 triF (pR p)))
      recR = lookup_op Z triStepU rIdx (ap1 predecessor p) (pR p)
               (op_pR p ne) (pRValueBound p ne)
      innerAd_val : Deriv (eqF (ap1 (C pi (lookupAt lIdx) (lookupAt rIdx)) opk)
                               (ap2 pi (ap1 triF (pL p)) (ap1 triF (pR p))))
      innerAd_val =
        ruleTrans (ax_C pi (lookupAt lIdx) (lookupAt rIdx) opk)
          (ruleTrans (congL pi (ap1 (lookupAt rIdx) opk) recL)
                     (congR pi (ap1 triF (pL p)) recR))
      midAd_val : Deriv (eqF (ap1 (C pi (constN 2) (C pi (lookupAt lIdx) (lookupAt rIdx))) opk)
                             (ap2 pi dgAd (ap2 pi (ap1 triF (pL p)) (ap1 triF (pR p)))))
      midAd_val =
        ruleTrans (ax_C pi (constN 2) (C pi (lookupAt lIdx) (lookupAt rIdx)) opk)
          (ruleTrans (congL pi (ap1 (C pi (lookupAt lIdx) (lookupAt rIdx)) opk) (constN_eq 2 opk))
                     (congR pi (natCode 2) innerAd_val))
      adExprRS_val : Deriv (eqF (ap1 adExprRS opk) (derAd (ap1 triF (pL p)) (ap1 triF (pR p))))
      adExprRS_val =
        ruleTrans (ax_C pi (constN 2) (C pi (constN 2) (C pi (lookupAt lIdx) (lookupAt rIdx))) opk)
          (ruleTrans (congL pi (ap1 (C pi (constN 2) (C pi (lookupAt lIdx) (lookupAt rIdx))) opk)
                         (constN_eq 2 opk))
                     (congR pi (natCode 2) midAd_val))
      innerRS_val : Deriv (eqF (ap1 (C pi adExprRS cellLeafTri) opk)
                               (ap2 pi (derAd (ap1 triF (pL p)) (ap1 triF (pR p))) filler))
      innerRS_val =
        ruleTrans (ax_C pi adExprRS cellLeafTri opk)
          (ruleTrans (congL pi (ap1 cellLeafTri opk) adExprRS_val)
                     (congR pi (derAd (ap1 triF (pL p)) (ap1 triF (pR p))) (cellLeafTri_at opk)))
      midRS_val : Deriv (eqF (ap1 (C pi (constN 1) (C pi adExprRS cellLeafTri)) opk)
                             (ap2 pi dgSu (ap2 pi (derAd (ap1 triF (pL p)) (ap1 triF (pR p))) filler)))
      midRS_val =
        ruleTrans (ax_C pi (constN 1) (C pi adExprRS cellLeafTri) opk)
          (ruleTrans (congL pi (ap1 (C pi adExprRS cellLeafTri) opk) (constN_eq 1 opk))
                     (congR pi (natCode 1) innerRS_val))
      rsNodeCell_val : Deriv (eqF (ap1 rsNodeCell opk)
                                  (derSu (derAd (ap1 triF (pL p)) (ap1 triF (pR p)))))
      rsNodeCell_val =
        ruleTrans (ax_C pi (constN 2) (C pi (constN 1) (C pi adExprRS cellLeafTri)) opk)
          (ruleTrans (congL pi (ap1 (C pi (constN 1) (C pi adExprRS cellLeafTri)) opk)
                         (constN_eq 2 opk))
                     (congR pi (natCode 2) midRS_val))
  in trans2c (ap1 triF p) (ap1 triStepU opk) (derSu (derAd (ap1 triF (pL p)) (ap1 triF (pR p))))
       (lift2 negLeaf htag (opUnfold p ne))
       (trans2c (ap1 triStepU opk) (ap1 cellNodeTri opk)
            (derSu (derAd (ap1 triF (pL p)) (ap1 triF (pR p)))) step2
         (trans2c (ap1 cellNodeTri opk) (ap1 rsNodeCell opk)
            (derSu (derAd (ap1 triF (pL p)) (ap1 triF (pR p))))
           (liftP negLeaf node_fires) (lift2 negLeaf htag rsNodeCell_val)))
