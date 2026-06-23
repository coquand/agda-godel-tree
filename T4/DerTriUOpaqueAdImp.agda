{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.DerTriUOpaqueAdImp -- IMP-FORM opaque triF Ad critical-pair equations over
-- the unsized coding, carried under [negLeaf, htag=dgAd, left-child condition].
-- These drive the Ad sub-dispatch of the bundled CR glue.
--
--   left leaf            : triF p = derRO (triF (pR p))
--   left dtag = dgSu     : triF p = derRS (triF (pL (pL p))) (triF (pR p))
--   left node, label k!=1: triF p = derAd (triF (pL p)) (triF (pR p))
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.DerTriUOpaqueAdImp where

open import T4.Base

open import T4.DerCode using ( derSu ; derAd ; derRO ; derRS ; dgAd ; dgSu ; dgRS ; filler ; derChildL_Su )
open import T4.DerCodeS using ( dtag ; pL ; pR )
open import T4.BinTree using ( nIdx ; lIdx ; rIdx )
open import T4.FoldRec using ( lookupAt ; fold ; get_newK )
open import T4.ParsObj using ( stepOf )
open import T4.ProgParse using ( get_tag )
open import T4.OpaqueLookup using ( lookup_op )
open import T4.WfRedExtract using ( pLValueBound ; pRValueBound )

open import T4.DerTri
  using ( triF ; cellLeafTri ; cellNodeTri ; suNodeCell ; restAdTri ; restROTri
        ; adCellTri ; adZeBranch ; adSuBranch ; adElseBranch ; restNodeAd
        ; testLeafA ; testSuA ; tagAidx ; labAidx ; derLF ; cellLeafTri_at )
open import T4.DerTri2 using ( derLF_eq ; adElse_val )
open import T4.DerTriUOpaqueImp using ( triF_op_Su_imp )
open import T4.DerTriUSuGam using ( triF_op_Su_gam )
open import T4.DerSrc using ( testEq ; w21 )
open import T4.GammaCtx using ( Cnj ; cnjL ; cnjR ; cnjCurry )
open import T4.NeSuImp using ( neSu_imp )

open import T4.ForkImp
  using ( fork_true_to_fst_imp ; fork_false_to_snd_imp ; testEq_fire_imp ; testEq_skip_imp
        ; natEqFire_imp ; natEqSkip_imp ; natEqSkipNeg_imp )
open import T4.CtxKit using ( lift2 ; lift3 ; lift4 ; ap3c ; ap4c ; trans3c ; trans4c )
open import T4.NatEqReflect using ( natEqF_complete )
open import T4.Thm12.ImpHelpers using ( impLift ; impEqTrans ; impCong1 ; impCongL ; impCongR )

open import BRA3.Church       using ( pi ; predecessor )
open import BRA3.PairAlgebra  using ( compose1U_eq ; compose1U )
open import BRA3.SubT.NatEq    using ( natEqF )
open import BRA3.SubT.V2NatNeq using ( NatNeqWitness )
open import BRA3.Contrapositive using ( compI ; liftP ; identP )

import T4.OpaqueHarness
private
  triStepU : Fun1
  triStepU = stepOf cellLeafTri cellNodeTri
open T4.OpaqueHarness.H triStepU

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

  tagA_at : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 tagAidx (opkg p)) (ap1 Fst (pL p)))
  tagA_at p ne = ruleTrans (compose1U_eq Fst lIdx (opkg p)) (cong1 Fst (op_pL p ne))

  labA_at : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 labAidx (opkg p)) (ap1 Fst (ap1 Snd (pL p))))
  labA_at p ne =
    ruleTrans (compose1U_eq Fst (compose1U Snd lIdx) (opkg p))
      (ruleTrans (cong1 Fst (compose1U_eq Snd lIdx (opkg p)))
                 (cong1 Fst (cong1 Snd (op_pL p ne))))

  recPR : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 (lookupAt rIdx) (opkg p)) (ap1 triF (pR p)))
  recPR p ne = lookup_op Z triStepU rIdx (ap1 predecessor p) (pR p)
                 (op_pR p ne) (pRValueBound p ne)

  recPL : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 (lookupAt lIdx) (opkg p)) (ap1 triF (pL p)))
  recPL p ne = lookup_op Z triStepU lIdx (ap1 predecessor p) (pL p)
                 (op_pL p ne) (pLValueBound p ne)

  -- The shared [negLeaf, htag] -> [negLeaf, htag, leftCond] machinery.
  module AdNode (p : Term) (ne : Deriv (neg (eqF p O))) (leftCond : Formula) where
    opk = opkg p
    negLeaf : Formula
    negLeaf = neg (eqF (ap1 Fst p) (natCode 1))
    htag : Formula
    htag = eqF (dtag p) dgAd
    -- context-insertion helpers (Ga=negLeaf, Gb=htag, Gc=leftCond).
    fromNeg : {X : Formula} -> Deriv (imp negLeaf X) -> Deriv (imp negLeaf (imp htag (imp leftCond X)))
    fromNeg {X} d = compI d (compI (axK X leftCond) (axK (imp leftCond X) htag))
    fromHtag : {X : Formula} -> Deriv (imp htag X) -> Deriv (imp negLeaf (imp htag (imp leftCond X)))
    fromHtag {X} d = liftP negLeaf (compI d (axK X leftCond))
    fromLeft : {X : Formula} -> Deriv (imp leftCond X) -> Deriv (imp negLeaf (imp htag (imp leftCond X)))
    fromLeft d = lift2 negLeaf htag d
    fromBare : {X : Formula} -> Deriv X -> Deriv (imp negLeaf (imp htag (imp leftCond X)))
    fromBare d = lift3 negLeaf htag leftCond d
    -- toNode (under negLeaf) and toAd (under htag).
    nl_neg : Deriv (imp negLeaf (eqF (ap1 (C natEqF get_tag (constN 1)) opk) O))
    nl_neg = impEqTrans (ap1 (C natEqF get_tag (constN 1)) opk)
               (ap2 natEqF (ap1 Fst p) (natCode 1)) O
               (impLift (test1At p ne)) (natEqF_complete (ap1 Fst p) (natCode 1))
    toNode_neg : Deriv (imp negLeaf (eqF (ap1 triStepU opk) (ap1 cellNodeTri opk)))
    toNode_neg = fork_false_to_snd_imp negLeaf cellLeafTri cellNodeTri
                   (C natEqF get_tag (constN 1)) opk nl_neg
    nieq_imp : Deriv (imp htag (eqF (ap1 nIdx opk) dgAd))
    nieq_imp = impEqTrans (ap1 nIdx opk) (dtag p) dgAd (impLift (op_nIdx p ne)) (identP htag)
    toAd_htag : Deriv (imp htag (eqF (ap1 cellNodeTri opk) (ap1 adCellTri opk)))
    toAd_htag =
      impEqTrans (ap1 cellNodeTri opk) (ap1 restAdTri opk) (ap1 adCellTri opk)
        (fork_false_to_snd_imp htag suNodeCell restAdTri (testEq 1) opk
           (testEq_skip_imp htag 2 1 opk w21 nieq_imp))
        (fork_true_to_fst_imp htag adCellTri restROTri (testEq 2) opk
           (testEq_fire_imp htag 2 opk nieq_imp))

------------------------------------------------------------------------
-- Ad_Ze :  left leaf  =>  triF p = derRO (triF (pR p)) .

triF_op_Ad_Ze_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (dtag p) dgAd)
                  (imp (eqF (ap1 Fst (pL p)) (natCode 1))
                       (eqF (ap1 triF p) (derRO (ap1 triF (pR p)))))))
triF_op_Ad_Ze_imp p ne =
  let leftCond : Formula
      leftCond = eqF (ap1 Fst (pL p)) (natCode 1)
      open AdNode p ne leftCond
      tagA_eq : Deriv (imp leftCond (eqF (ap1 tagAidx opk) (natCode 1)))
      tagA_eq = impEqTrans (ap1 tagAidx opk) (ap1 Fst (pL p)) (natCode 1)
                  (impLift (tagA_at p ne)) (identP leftCond)
      ad_fires : Deriv (imp leftCond (eqF (ap1 adCellTri opk) (ap1 adZeBranch opk)))
      ad_fires = fork_true_to_fst_imp leftCond adZeBranch restNodeAd testLeafA opk
                   (natEqFire_imp leftCond tagAidx 1 opk tagA_eq)
      -- adZeBranch opk = derRO (triF (pR p))  (bare).
      inner_val : Deriv (eqF (ap1 (C pi (lookupAt rIdx) cellLeafTri) opk)
                             (ap2 pi (ap1 triF (pR p)) filler))
      inner_val =
        ruleTrans (ax_C pi (lookupAt rIdx) cellLeafTri opk)
          (ruleTrans (congL pi (ap1 cellLeafTri opk) (recPR p ne))
                     (congR pi (ap1 triF (pR p)) (cellLeafTri_at opk)))
      mid_val : Deriv (eqF (ap1 (C pi (constN 3) (C pi (lookupAt rIdx) cellLeafTri)) opk)
                           (ap2 pi (natCode 3) (ap2 pi (ap1 triF (pR p)) filler)))
      mid_val =
        ruleTrans (ax_C pi (constN 3) (C pi (lookupAt rIdx) cellLeafTri) opk)
          (ruleTrans (congL pi (ap1 (C pi (lookupAt rIdx) cellLeafTri) opk) (constN_eq 3 opk))
                     (congR pi (natCode 3) inner_val))
      adZe_val : Deriv (eqF (ap1 adZeBranch opk) (derRO (ap1 triF (pR p))))
      adZe_val =
        ruleTrans (ax_C pi (constN 2) (C pi (constN 3) (C pi (lookupAt rIdx) cellLeafTri)) opk)
          (ruleTrans (congL pi (ap1 (C pi (constN 3) (C pi (lookupAt rIdx) cellLeafTri)) opk)
                         (constN_eq 2 opk))
                     (congR pi (natCode 2) mid_val))
  in trans3c (ap1 triF p) (ap1 triStepU opk) (derRO (ap1 triF (pR p)))
       (fromBare (opUnfold p ne))
       (trans3c (ap1 triStepU opk) (ap1 cellNodeTri opk) (derRO (ap1 triF (pR p)))
         (fromNeg toNode_neg)
         (trans3c (ap1 cellNodeTri opk) (ap1 adCellTri opk) (derRO (ap1 triF (pR p)))
           (fromHtag toAd_htag)
           (trans3c (ap1 adCellTri opk) (ap1 adZeBranch opk) (derRO (ap1 triF (pR p)))
             (fromLeft ad_fires) (fromBare adZe_val))))

------------------------------------------------------------------------
-- Ad_else :  left node, not Su  =>  triF p = derAd (triF (pL p)) (triF (pR p)) .
-- Context [negLeaf, htag, lc1 = neg(Fst(pL p)=1), lc2 = neg(dtag(pL p)=dgSu)].

private
  module AdNodeE (p : Term) (ne : Deriv (neg (eqF p O))) where
    opk = opkg p
    negLeaf : Formula
    negLeaf = neg (eqF (ap1 Fst p) (natCode 1))
    htag : Formula
    htag = eqF (dtag p) dgAd
    lc1 : Formula
    lc1 = neg (eqF (ap1 Fst (pL p)) (natCode 1))
    lc2 : Formula
    lc2 = neg (eqF (dtag (pL p)) dgSu)
    fromNeg : {X : Formula} -> Deriv (imp negLeaf X) ->
      Deriv (imp negLeaf (imp htag (imp lc1 (imp lc2 X))))
    fromNeg {X} d =
      compI d (compI (axK X lc2) (compI (axK (imp lc2 X) lc1) (axK (imp lc1 (imp lc2 X)) htag)))
    fromHtag : {X : Formula} -> Deriv (imp htag X) ->
      Deriv (imp negLeaf (imp htag (imp lc1 (imp lc2 X))))
    fromHtag {X} d = liftP negLeaf (compI d (compI (axK X lc2) (axK (imp lc2 X) lc1)))
    fromLC1 : {X : Formula} -> Deriv (imp lc1 X) ->
      Deriv (imp negLeaf (imp htag (imp lc1 (imp lc2 X))))
    fromLC1 {X} d = lift2 negLeaf htag (compI d (axK X lc2))
    fromLC2 : {X : Formula} -> Deriv (imp lc2 X) ->
      Deriv (imp negLeaf (imp htag (imp lc1 (imp lc2 X))))
    fromLC2 d = lift3 negLeaf htag lc1 d
    fromBare : {X : Formula} -> Deriv X ->
      Deriv (imp negLeaf (imp htag (imp lc1 (imp lc2 X))))
    fromBare d = lift4 negLeaf htag lc1 lc2 d
    nl_neg : Deriv (imp negLeaf (eqF (ap1 (C natEqF get_tag (constN 1)) opk) O))
    nl_neg = impEqTrans (ap1 (C natEqF get_tag (constN 1)) opk)
               (ap2 natEqF (ap1 Fst p) (natCode 1)) O
               (impLift (test1At p ne)) (natEqF_complete (ap1 Fst p) (natCode 1))
    toNode_neg : Deriv (imp negLeaf (eqF (ap1 triStepU opk) (ap1 cellNodeTri opk)))
    toNode_neg = fork_false_to_snd_imp negLeaf cellLeafTri cellNodeTri
                   (C natEqF get_tag (constN 1)) opk nl_neg
    nieq_imp : Deriv (imp htag (eqF (ap1 nIdx opk) dgAd))
    nieq_imp = impEqTrans (ap1 nIdx opk) (dtag p) dgAd (impLift (op_nIdx p ne)) (identP htag)
    toAd_htag : Deriv (imp htag (eqF (ap1 cellNodeTri opk) (ap1 adCellTri opk)))
    toAd_htag =
      impEqTrans (ap1 cellNodeTri opk) (ap1 restAdTri opk) (ap1 adCellTri opk)
        (fork_false_to_snd_imp htag suNodeCell restAdTri (testEq 1) opk
           (testEq_skip_imp htag 2 1 opk w21 nieq_imp))
        (fork_true_to_fst_imp htag adCellTri restROTri (testEq 2) opk
           (testEq_fire_imp htag 2 opk nieq_imp))

triF_op_Ad_else_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (dtag p) dgAd)
                  (imp (neg (eqF (ap1 Fst (pL p)) (natCode 1)))
                       (imp (neg (eqF (dtag (pL p)) dgSu))
                            (eqF (ap1 triF p) (derAd (ap1 triF (pL p)) (ap1 triF (pR p))))))))
triF_op_Ad_else_imp p ne =
  let open AdNodeE p ne
      -- testLeafA skips from lc1 .
      tla_to : Deriv (eqF (ap1 testLeafA opk) (ap2 natEqF (ap1 Fst (pL p)) (natCode 1)))
      tla_to = ruleTrans (ax_C natEqF tagAidx (constN 1) opk)
                 (ruleTrans (congL natEqF (ap1 (constN 1) opk) (tagA_at p ne))
                            (congR natEqF (ap1 Fst (pL p)) (constN_eq 1 opk)))
      tla_skip : Deriv (imp lc1 (eqF (ap1 testLeafA opk) O))
      tla_skip = impEqTrans (ap1 testLeafA opk) (ap2 natEqF (ap1 Fst (pL p)) (natCode 1)) O
                   (impLift tla_to) (natEqF_complete (ap1 Fst (pL p)) (natCode 1))
      ad_to_rest : Deriv (imp lc1 (eqF (ap1 adCellTri opk) (ap1 restNodeAd opk)))
      ad_to_rest = fork_false_to_snd_imp lc1 adZeBranch restNodeAd testLeafA opk tla_skip
      -- testSuA skips from lc2 .  dgSu = natCode 1.
      tsa_to : Deriv (eqF (ap1 testSuA opk) (ap2 natEqF (dtag (pL p)) (natCode 1)))
      tsa_to = ruleTrans (ax_C natEqF labAidx (constN 1) opk)
                 (ruleTrans (congL natEqF (ap1 (constN 1) opk) (labA_at p ne))
                            (congR natEqF (ap1 Fst (ap1 Snd (pL p))) (constN_eq 1 opk)))
      tsa_skip : Deriv (imp lc2 (eqF (ap1 testSuA opk) O))
      tsa_skip = impEqTrans (ap1 testSuA opk) (ap2 natEqF (dtag (pL p)) (natCode 1)) O
                   (impLift tsa_to) (natEqF_complete (dtag (pL p)) (natCode 1))
      rest_to_else : Deriv (imp lc2 (eqF (ap1 restNodeAd opk) (ap1 adElseBranch opk)))
      rest_to_else = fork_false_to_snd_imp lc2 adSuBranch adElseBranch testSuA opk tsa_skip
      adElse_val_bare : Deriv (eqF (ap1 adElseBranch opk) (derAd (ap1 triF (pL p)) (ap1 triF (pR p))))
      adElse_val_bare = adElse_val opk (ap1 triF (pL p)) (ap1 triF (pR p)) (recPL p ne) (recPR p ne)
  in trans4c (ap1 triF p) (ap1 triStepU opk) (derAd (ap1 triF (pL p)) (ap1 triF (pR p)))
       (fromBare (opUnfold p ne))
       (trans4c (ap1 triStepU opk) (ap1 cellNodeTri opk) (derAd (ap1 triF (pL p)) (ap1 triF (pR p)))
         (fromNeg toNode_neg)
         (trans4c (ap1 cellNodeTri opk) (ap1 adCellTri opk) (derAd (ap1 triF (pL p)) (ap1 triF (pR p)))
           (fromHtag toAd_htag)
           (trans4c (ap1 adCellTri opk) (ap1 restNodeAd opk) (derAd (ap1 triF (pL p)) (ap1 triF (pR p)))
             (fromLC1 ad_to_rest)
             (trans4c (ap1 restNodeAd opk) (ap1 adElseBranch opk)
                  (derAd (ap1 triF (pL p)) (ap1 triF (pR p)))
               (fromLC2 rest_to_else) (fromBare adElse_val_bare)))))

------------------------------------------------------------------------
-- Ad_Su :  left node with  dtag (pL p) = dgSu  =>
--   triF p = derRS (triF (pL (pL p))) (triF (pR p)) .
-- Built over ONE Cnj-conjunction context  Gam  = [negLeaf, htag=dgAd,
-- lc1=neg(Fst(pL p)=1), htagLL=dtag(pL p)=dgSu], so the grandchild  pL (pL p)
-- is recovered by the Gam-polymorphic Su unfold (T4.DerTriUSuGam), with
-- ne(pL p) / nl(pL p) projected from htagLL / lc1.  Delivered in nested-imp form
-- by 3x cnjCurry, matching triF_op_Ad_Ze_imp / triF_op_Ad_else_imp.

triF_op_Ad_Su_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (dtag p) dgAd)
                  (imp (neg (eqF (ap1 Fst (pL p)) (natCode 1)))
                       (imp (eqF (dtag (pL p)) dgSu)
                            (eqF (ap1 triF p)
                                 (derRS (ap1 triF (pL (pL p))) (ap1 triF (pR p))))))))
triF_op_Ad_Su_imp p ne =
  let opk = opkg p
      Z2 : Term
      Z2 = ap1 triF (pL (pL p))
      R : Term
      R = ap1 triF (pR p)
      negLeaf : Formula
      negLeaf = neg (eqF (ap1 Fst p) (natCode 1))
      htag : Formula
      htag = eqF (dtag p) dgAd
      lc1 : Formula
      lc1 = neg (eqF (ap1 Fst (pL p)) (natCode 1))
      htagLL : Formula
      htagLL = eqF (dtag (pL p)) dgSu
      A3 : Formula
      A3 = Cnj negLeaf htag
      A4 : Formula
      A4 = Cnj A3 lc1
      Gam : Formula
      Gam = Cnj A4 htagLL
      ----------------------------------------------------------------
      -- projections of the conjuncts.
      pA4 : Deriv (imp Gam A4)
      pA4 = cnjL A4 htagLL
      pA3 : Deriv (imp Gam A3)
      pA3 = compI pA4 (cnjL A3 lc1)
      pNegLeaf : Deriv (imp Gam negLeaf)
      pNegLeaf = compI pA3 (cnjL negLeaf htag)
      pHtag : Deriv (imp Gam htag)
      pHtag = compI pA3 (cnjR negLeaf htag)
      pLc1 : Deriv (imp Gam lc1)
      pLc1 = compI pA4 (cnjR A3 lc1)
      pHtagLL : Deriv (imp Gam htagLL)
      pHtagLL = cnjR A4 htagLL
      ----------------------------------------------------------------
      -- the grandchild Su unfold at  q = pL p .
      gNeL : Deriv (imp Gam (neg (eqF (pL p) O)))
      gNeL = compI pHtagLL (neSu_imp (pL p))
      gNlL : Deriv (imp Gam (eqF (ap2 natEqF (ap1 Fst (pL p)) (natCode 1)) O))
      gNlL = compI pLc1 (natEqF_complete (ap1 Fst (pL p)) (natCode 1))
      grand : Deriv (imp Gam (eqF (ap1 triF (pL p)) (derSu Z2)))
      grand = triF_op_Su_gam Gam (pL p) gNeL gNlL pHtagLL
      ----------------------------------------------------------------
      -- p-level cascade under Gam :  triF p = adSuBranch opk .
      gNl_p : Deriv (imp Gam (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O))
      gNl_p = compI pNegLeaf (natEqF_complete (ap1 Fst p) (natCode 1))
      t1_O_p : Deriv (imp Gam (eqF (ap1 (C natEqF get_tag (constN 1)) opk) O))
      t1_O_p = impEqTrans (ap1 (C natEqF get_tag (constN 1)) opk)
                          (ap2 natEqF (ap1 Fst p) (natCode 1)) O
                 (liftP Gam (test1At p ne)) gNl_p
      toNode_g : Deriv (imp Gam (eqF (ap1 triStepU opk) (ap1 cellNodeTri opk)))
      toNode_g = fork_false_to_snd_imp Gam cellLeafTri cellNodeTri
                   (C natEqF get_tag (constN 1)) opk t1_O_p
      nieq_p : Deriv (imp Gam (eqF (ap1 nIdx opk) dgAd))
      nieq_p = impEqTrans (ap1 nIdx opk) (dtag p) dgAd (liftP Gam (op_nIdx p ne)) pHtag
      toAd_g : Deriv (imp Gam (eqF (ap1 cellNodeTri opk) (ap1 adCellTri opk)))
      toAd_g = impEqTrans (ap1 cellNodeTri opk) (ap1 restAdTri opk) (ap1 adCellTri opk)
                 (fork_false_to_snd_imp Gam suNodeCell restAdTri (testEq 1) opk
                    (testEq_skip_imp Gam 2 1 opk w21 nieq_p))
                 (fork_true_to_fst_imp Gam adCellTri restROTri (testEq 2) opk
                    (testEq_fire_imp Gam 2 opk nieq_p))
      -- adCellTri opk = adSuBranch opk  (left-leaf test skips, su test fires).
      tla_to : Deriv (eqF (ap1 testLeafA opk) (ap2 natEqF (ap1 Fst (pL p)) (natCode 1)))
      tla_to = ruleTrans (ax_C natEqF tagAidx (constN 1) opk)
                 (ruleTrans (congL natEqF (ap1 (constN 1) opk) (tagA_at p ne))
                            (congR natEqF (ap1 Fst (pL p)) (constN_eq 1 opk)))
      tla_skip_g : Deriv (imp Gam (eqF (ap1 testLeafA opk) O))
      tla_skip_g = impEqTrans (ap1 testLeafA opk)
                     (ap2 natEqF (ap1 Fst (pL p)) (natCode 1)) O
                     (liftP Gam tla_to) gNlL
      labA_eq_g : Deriv (imp Gam (eqF (ap1 labAidx opk) (natCode 1)))
      labA_eq_g = impEqTrans (ap1 labAidx opk) (dtag (pL p)) (natCode 1)
                    (liftP Gam (labA_at p ne)) pHtagLL
      ad_fires_g : Deriv (imp Gam (eqF (ap1 adCellTri opk) (ap1 adSuBranch opk)))
      ad_fires_g = impEqTrans (ap1 adCellTri opk) (ap1 restNodeAd opk) (ap1 adSuBranch opk)
                     (fork_false_to_snd_imp Gam adZeBranch restNodeAd testLeafA opk tla_skip_g)
                     (fork_true_to_fst_imp Gam adSuBranch adElseBranch testSuA opk
                        (natEqFire_imp Gam labAidx 1 opk labA_eq_g))
      ----------------------------------------------------------------
      -- adSuBranch opk = derRS Z2 R .
      dL_eq_g : Deriv (imp Gam (eqF (ap1 (compose1U derLF (lookupAt lIdx)) opk) Z2))
      dL_eq_g =
        impEqTrans (ap1 (compose1U derLF (lookupAt lIdx)) opk)
                   (ap1 derLF (ap1 (lookupAt lIdx) opk)) Z2
          (liftP Gam (compose1U_eq derLF (lookupAt lIdx) opk))
          (impEqTrans (ap1 derLF (ap1 (lookupAt lIdx) opk))
                      (ap1 derLF (ap1 triF (pL p))) Z2
             (liftP Gam (cong1 derLF (recPL p ne)))
             (impEqTrans (ap1 derLF (ap1 triF (pL p))) (ap1 derLF (derSu Z2)) Z2
                (impCong1 derLF (ap1 triF (pL p)) (derSu Z2) grand)
                (liftP Gam (ruleTrans (derLF_eq (derSu Z2)) (derChildL_Su Z2)))))
      inner_g : Deriv (imp Gam
        (eqF (ap1 (C pi (compose1U derLF (lookupAt lIdx)) (lookupAt rIdx)) opk) (ap2 pi Z2 R)))
      inner_g =
        impEqTrans (ap1 (C pi (compose1U derLF (lookupAt lIdx)) (lookupAt rIdx)) opk)
                   (ap2 pi (ap1 (compose1U derLF (lookupAt lIdx)) opk) (ap1 (lookupAt rIdx) opk))
                   (ap2 pi Z2 R)
          (liftP Gam (ax_C pi (compose1U derLF (lookupAt lIdx)) (lookupAt rIdx) opk))
          (impEqTrans (ap2 pi (ap1 (compose1U derLF (lookupAt lIdx)) opk) (ap1 (lookupAt rIdx) opk))
                      (ap2 pi Z2 (ap1 (lookupAt rIdx) opk)) (ap2 pi Z2 R)
             (impCongL pi (ap1 (compose1U derLF (lookupAt lIdx)) opk) Z2 (ap1 (lookupAt rIdx) opk) dL_eq_g)
             (liftP Gam (congR pi Z2 (recPR p ne))))
      midC : Term
      midC = ap1 (C pi (compose1U derLF (lookupAt lIdx)) (lookupAt rIdx)) opk
      mid_g : Deriv (imp Gam
        (eqF (ap1 (C pi (constN 4) (C pi (compose1U derLF (lookupAt lIdx)) (lookupAt rIdx))) opk)
             (ap2 pi dgRS (ap2 pi Z2 R))))
      mid_g =
        impEqTrans (ap1 (C pi (constN 4) (C pi (compose1U derLF (lookupAt lIdx)) (lookupAt rIdx))) opk)
                   (ap2 pi (ap1 (constN 4) opk) midC) (ap2 pi dgRS (ap2 pi Z2 R))
          (liftP Gam (ax_C pi (constN 4) (C pi (compose1U derLF (lookupAt lIdx)) (lookupAt rIdx)) opk))
          (impEqTrans (ap2 pi (ap1 (constN 4) opk) midC) (ap2 pi (natCode 4) midC)
                      (ap2 pi dgRS (ap2 pi Z2 R))
             (liftP Gam (congL pi midC (constN_eq 4 opk)))
             (impCongR pi midC (ap2 pi Z2 R) (natCode 4) inner_g))
      bigC4 : Term
      bigC4 = ap1 (C pi (constN 4) (C pi (compose1U derLF (lookupAt lIdx)) (lookupAt rIdx))) opk
      adSu_val_g : Deriv (imp Gam (eqF (ap1 adSuBranch opk) (derRS Z2 R)))
      adSu_val_g =
        impEqTrans (ap1 adSuBranch opk) (ap2 pi (ap1 (constN 2) opk) bigC4) (derRS Z2 R)
          (liftP Gam (ax_C pi (constN 2)
            (C pi (constN 4) (C pi (compose1U derLF (lookupAt lIdx)) (lookupAt rIdx))) opk))
          (impEqTrans (ap2 pi (ap1 (constN 2) opk) bigC4) (ap2 pi (natCode 2) bigC4) (derRS Z2 R)
             (liftP Gam (congL pi bigC4 (constN_eq 2 opk)))
             (impCongR pi bigC4 (ap2 pi dgRS (ap2 pi Z2 R)) (natCode 2) mid_g))
      ----------------------------------------------------------------
      resultG : Deriv (imp Gam (eqF (ap1 triF p) (derRS Z2 R)))
      resultG =
        impEqTrans (ap1 triF p) (ap1 triStepU opk) (derRS Z2 R)
          (liftP Gam (opUnfold p ne))
          (impEqTrans (ap1 triStepU opk) (ap1 cellNodeTri opk) (derRS Z2 R)
             toNode_g
             (impEqTrans (ap1 cellNodeTri opk) (ap1 adCellTri opk) (derRS Z2 R)
                toAd_g
                (impEqTrans (ap1 adCellTri opk) (ap1 adSuBranch opk) (derRS Z2 R)
                   ad_fires_g adSu_val_g)))
  in cnjCurry (cnjCurry (cnjCurry resultG))
