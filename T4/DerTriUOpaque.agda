{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.DerTriUOpaque -- the OPAQUE triF equations on the UNSIZED DerCode coding,
-- the analogue of T4.DerTriSOpaque (which is over the size-prefixed coding).
--
-- For an arbitrary code  p != O , dispatched on whether  p  is a leaf
-- (test1 = natEqF (Fst p) (natCode 1) fires) or a node (test1 skips), and on the
-- derivation label  dtag p = Fst (Snd p) , triF p reduces by the SAME cells as
-- the built equations (T4.DerTri), unfolded via the opaque harness
-- (T4.OpaqueHarness at triStepU) with child recovery via lookup_op + value
-- bounds (T4.WfRedExtract).
--
--   p!=O, Fst p = natCode 1                       => triF p = derZe            (leaf)
--   p!=O, test1 skips, dtag p = dgSu              => triF p = derSu (triF (pL p))
--   p!=O, test1 skips, dtag p = dgRO              => triF p = triF (pL p)
--   p!=O, test1 skips, dtag p = dgRS              => triF p = derSu (derAd (triF (pL p)) (triF (pR p)))
--   + the Ad critical pairs (depth-2 left-child dispatch).
--
-- NODE gating is "test1 skips" (nl : natEqF (Fst p) (natCode 1) = O), NOT
-- "Fst p = natCode 2": wfRed only distinguishes leaf from non-leaf, so the
-- bigC dispatch supplies nl (from neg (Fst p = natCode 1) via natEqF_complete).
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.DerTriUOpaque where

open import T4.Base

open import T4.DerCode
  using ( derZe ; derSu ; derAd ; derRO ; derRS
        ; dgZe ; dgSu ; dgAd ; dgRO ; dgRS ; filler ; derChildL_Su )
open import T4.DerCodeS using ( dtag ; pL ; pR )
open import T4.BinTree using ( nIdx ; lIdx ; rIdx )
open import T4.FoldRec using ( lookupAt ; fold ; get_newK )
open import T4.ParsObj using ( stepOf )
open import T4.ProgParse using ( get_tag )
open import T4.OpaqueLookup using ( lookup_op )
open import T4.WfRedExtract using ( pLValueBound ; pRValueBound )

open import T4.DerTri
  using ( triF ; cellLeafTri ; cellNodeTri ; suNodeCell ; roNodeCell ; rsNodeCell
        ; adCellTri ; restAdTri ; restROTri ; adExprRS ; cellLeafTri_at
        ; adZeBranch ; adSuBranch ; adElseBranch ; restNodeAd
        ; testLeafA ; testSuA ; tagAidx ; labAidx ; derLF )
open import T4.DerTri2
  using ( testLeafA_fire ; testSuA_fire ; testSuA_skip ; derLF_eq ; adElse_val )

open import T4.DerSrc
  using ( testEq ; fork_true_to_fst ; fork_false_to_snd ; testEq_fire ; testEq_skip
        ; w21 ; w31 ; w32 ; w41 ; w42 ; w43 )

open import BRA3.Church       using ( pi ; predecessor )
open import BRA3.PairAlgebra  using ( compose1U_eq )
open import BRA3.SubT.NatEq    using ( natEqF ; natEq_eq )
open import BRA3.SubT.V2NatNeq using ( natEqF_at_neq ; NatNeqWitness )

import T4.OpaqueHarness
private
  triStepU : Fun1
  triStepU = stepOf cellLeafTri cellNodeTri
open T4.OpaqueHarness.H triStepU

------------------------------------------------------------------------
-- SECTION 0.  The binary-tag accessor and the leaf/node test value.

-- op_tag : get_tag (opkg p) = Fst p   (get_tag = compose1U Fst get_newK).
op_tag : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap1 get_tag (opkg p)) (ap1 Fst p))
op_tag p ne =
  ruleTrans (compose1U_eq Fst get_newK (opkg p)) (cong1 Fst (op_newK p ne))

-- test1 (opkg p) = natEqF (Fst p) (natCode 1).
test1At : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap1 (C natEqF get_tag (constN 1)) (opkg p))
             (ap2 natEqF (ap1 Fst p) (natCode 1)))
test1At p ne =
  ruleTrans (ax_C natEqF get_tag (constN 1) (opkg p))
    (ruleTrans (congL natEqF (ap1 (constN 1) (opkg p)) (op_tag p ne))
               (congR natEqF (ap1 Fst p) (constN_eq 1 (opkg p))))

------------------------------------------------------------------------
-- SECTION 1.  The leaf case (Ze).

triF_op_Ze : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap1 Fst p) (natCode 1)) ->
  Deriv (eqF (ap1 triF p) derZe)
triF_op_Ze p ne htagB =
  let opk : Term
      opk = opkg p
      t1_fire : Deriv (eqF (ap1 (C natEqF get_tag (constN 1)) opk) (ap1 s O))
      t1_fire = ruleTrans (test1At p ne)
                  (ruleTrans (congL natEqF (natCode 1) htagB) (natEq_eq 1))
      cell_fires : Deriv (eqF (ap1 triStepU opk) (ap1 cellLeafTri opk))
      cell_fires = fork_true_to_fst cellLeafTri cellNodeTri
                     (C natEqF get_tag (constN 1)) opk t1_fire
  in ruleTrans (opUnfold p ne)
       (ruleTrans cell_fires (cellLeafTri_at opk))

------------------------------------------------------------------------
-- SECTION 2.  The node cases (Su / RO / RS).  Gated on "test1 skips" (nl).

private
  -- shared: the node-branch entry  triStepU opk = cellNodeTri opk .
  toNode : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) ->
    Deriv (eqF (ap1 triStepU (opkg p)) (ap1 cellNodeTri (opkg p)))
  toNode p ne nl =
    let opk = opkg p
        t1_O : Deriv (eqF (ap1 (C natEqF get_tag (constN 1)) opk) O)
        t1_O = ruleTrans (test1At p ne) nl
    in fork_false_to_snd cellLeafTri cellNodeTri
         (C natEqF get_tag (constN 1)) opk t1_O

  recLabel : (p : Term) -> Deriv (neg (eqF p O)) -> {tg : Term} ->
    Deriv (eqF (dtag p) tg) -> Deriv (eqF (ap1 nIdx (opkg p)) tg)
  recLabel p ne htag = ruleTrans (op_nIdx p ne) htag

  recPL : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 (lookupAt lIdx) (opkg p)) (ap1 triF (pL p)))
  recPL p ne =
    lookup_op Z triStepU lIdx (ap1 predecessor p) (pL p)
      (op_pL p ne) (pLValueBound p ne)

  recPR : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 (lookupAt rIdx) (opkg p)) (ap1 triF (pR p)))
  recPR p ne =
    lookup_op Z triStepU rIdx (ap1 predecessor p) (pR p)
      (op_pR p ne) (pRValueBound p ne)

------------------------------------------------------------------------
-- Su:  triF p = derSu (triF (pL p)) .

triF_op_Su : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) -> Deriv (eqF (dtag p) dgSu) ->
  Deriv (eqF (ap1 triF p) (derSu (ap1 triF (pL p))))
triF_op_Su p ne nl htag =
  let opk = opkg p
      nieq : Deriv (eqF (ap1 nIdx opk) dgSu)
      nieq = recLabel p ne htag
      node_fires : Deriv (eqF (ap1 cellNodeTri opk) (ap1 suNodeCell opk))
      node_fires = fork_true_to_fst suNodeCell restAdTri (testEq 1) opk
                     (testEq_fire 1 opk nieq)
      recL : Deriv (eqF (ap1 (lookupAt lIdx) opk) (ap1 triF (pL p)))
      recL = recPL p ne
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
          (ruleTrans (congL pi (ap1 (C pi (lookupAt lIdx) cellLeafTri) opk)
                         (constN_eq 1 opk))
                     (congR pi (natCode 1) inner_val))
      suNodeCell_val : Deriv (eqF (ap1 suNodeCell opk) (derSu (ap1 triF (pL p))))
      suNodeCell_val =
        ruleTrans (ax_C pi (constN 2) (C pi (constN 1) (C pi (lookupAt lIdx) cellLeafTri)) opk)
          (ruleTrans (congL pi (ap1 (C pi (constN 1) (C pi (lookupAt lIdx) cellLeafTri)) opk)
                         (constN_eq 2 opk))
                     (congR pi (natCode 2) mid_val))
  in ruleTrans (opUnfold p ne)
       (ruleTrans (toNode p ne nl)
         (ruleTrans node_fires suNodeCell_val))

------------------------------------------------------------------------
-- RO:  triF p = triF (pL p) .

triF_op_RO : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) -> Deriv (eqF (dtag p) dgRO) ->
  Deriv (eqF (ap1 triF p) (ap1 triF (pL p)))
triF_op_RO p ne nl htag =
  let opk = opkg p
      nieq : Deriv (eqF (ap1 nIdx opk) dgRO)
      nieq = recLabel p ne htag
      node_fires : Deriv (eqF (ap1 cellNodeTri opk) (ap1 roNodeCell opk))
      node_fires =
        ruleTrans (fork_false_to_snd suNodeCell restAdTri (testEq 1) opk
                     (testEq_skip 3 1 opk w31 nieq))
          (ruleTrans (fork_false_to_snd adCellTri restROTri (testEq 2) opk
                        (testEq_skip 3 2 opk w32 nieq))
                     (fork_true_to_fst roNodeCell rsNodeCell (testEq 3) opk
                        (testEq_fire 3 opk nieq)))
  in ruleTrans (opUnfold p ne)
       (ruleTrans (toNode p ne nl)
         (ruleTrans node_fires (recPL p ne)))

------------------------------------------------------------------------
-- RS:  triF p = derSu (derAd (triF (pL p)) (triF (pR p))) .

triF_op_RS : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) -> Deriv (eqF (dtag p) dgRS) ->
  Deriv (eqF (ap1 triF p) (derSu (derAd (ap1 triF (pL p)) (ap1 triF (pR p)))))
triF_op_RS p ne nl htag =
  let opk = opkg p
      nieq : Deriv (eqF (ap1 nIdx opk) dgRS)
      nieq = recLabel p ne htag
      node_fires : Deriv (eqF (ap1 cellNodeTri opk) (ap1 rsNodeCell opk))
      node_fires =
        ruleTrans (fork_false_to_snd suNodeCell restAdTri (testEq 1) opk
                     (testEq_skip 4 1 opk w41 nieq))
          (ruleTrans (fork_false_to_snd adCellTri restROTri (testEq 2) opk
                        (testEq_skip 4 2 opk w42 nieq))
                     (fork_false_to_snd roNodeCell rsNodeCell (testEq 3) opk
                        (testEq_skip 4 3 opk w43 nieq)))
      recL : Deriv (eqF (ap1 (lookupAt lIdx) opk) (ap1 triF (pL p)))
      recL = recPL p ne
      recR : Deriv (eqF (ap1 (lookupAt rIdx) opk) (ap1 triF (pR p)))
      recR = recPR p ne
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
          (ruleTrans (congL pi (ap1 (C pi (lookupAt lIdx) (lookupAt rIdx)) opk)
                         (constN_eq 2 opk))
                     (congR pi (natCode 2) innerAd_val))
      adExprRS_val : Deriv (eqF (ap1 adExprRS opk)
                               (derAd (ap1 triF (pL p)) (ap1 triF (pR p))))
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
  in ruleTrans (opUnfold p ne)
       (ruleTrans (toNode p ne nl)
         (ruleTrans node_fires rsNodeCell_val))

------------------------------------------------------------------------
-- SECTION 3.  The Ad critical pairs (depth-2 left-child dispatch).
-- dtag p = dgAd: cascade to adCellTri, then dispatch on the left child pL p
-- via testLeafA (Fst (pL p) = 1 ? leaf) and testSuA (dtag (pL p) = 1 ?).

private
  toAd : (p : Term) -> Deriv (neg (eqF p O)) -> Deriv (eqF (dtag p) dgAd) ->
    Deriv (eqF (ap1 cellNodeTri (opkg p)) (ap1 adCellTri (opkg p)))
  toAd p ne htag =
    let opk = opkg p
        nieq : Deriv (eqF (ap1 nIdx opk) dgAd)
        nieq = recLabel p ne htag
    in ruleTrans (fork_false_to_snd suNodeCell restAdTri (testEq 1) opk
                    (testEq_skip 2 1 opk w21 nieq))
                 (fork_true_to_fst adCellTri restROTri (testEq 2) opk
                    (testEq_fire 2 opk nieq))

  -- left-child binary tag:  tagAidx opk = Fst (pL p) .
  tagA_at : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 tagAidx (opkg p)) (ap1 Fst (pL p)))
  tagA_at p ne =
    ruleTrans (compose1U_eq Fst lIdx (opkg p)) (cong1 Fst (op_pL p ne))

  -- left-child deriv-label:  labAidx opk = dtag (pL p) = Fst (Snd (pL p)) .
  labA_at : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 labAidx (opkg p)) (ap1 Fst (ap1 Snd (pL p))))
  labA_at p ne =
    ruleTrans (compose1U_eq Fst (compose1U Snd lIdx) (opkg p))
      (ruleTrans (cong1 Fst (compose1U_eq Snd lIdx (opkg p)))
                 (cong1 Fst (cong1 Snd (op_pL p ne))))

  -- testLeafA skips, from "left child is not a leaf"  (nlL : natEqF (Fst (pL p)) 1 = O).
  testLeafA_skip_nl : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap2 natEqF (ap1 Fst (pL p)) (natCode 1)) O) ->
    Deriv (eqF (ap1 testLeafA (opkg p)) O)
  testLeafA_skip_nl p ne nlL =
    let opk = opkg p in
    ruleTrans (ax_C natEqF tagAidx (constN 1) opk)
      (ruleTrans (congL natEqF (ap1 (constN 1) opk) (tagA_at p ne))
        (ruleTrans (congR natEqF (ap1 Fst (pL p)) (constN_eq 1 opk)) nlL))

------------------------------------------------------------------------
-- Ad_Ze:  pL p is a leaf  =>  triF p = derRO (triF (pR p)) .

triF_op_Ad_Ze : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) -> Deriv (eqF (dtag p) dgAd) ->
  Deriv (eqF (ap1 Fst (pL p)) (natCode 1)) ->
  Deriv (eqF (ap1 triF p) (derRO (ap1 triF (pR p))))
triF_op_Ad_Ze p ne nl htag htagBL =
  let opk = opkg p
      tagA_eq : Deriv (eqF (ap1 tagAidx opk) (natCode 1))
      tagA_eq = ruleTrans (tagA_at p ne) htagBL
      ad_fires : Deriv (eqF (ap1 adCellTri opk) (ap1 adZeBranch opk))
      ad_fires = fork_true_to_fst adZeBranch restNodeAd testLeafA opk
                   (testLeafA_fire opk tagA_eq)
      recR : Deriv (eqF (ap1 (lookupAt rIdx) opk) (ap1 triF (pR p)))
      recR = recPR p ne
      inner_val : Deriv (eqF (ap1 (C pi (lookupAt rIdx) cellLeafTri) opk)
                             (ap2 pi (ap1 triF (pR p)) filler))
      inner_val =
        ruleTrans (ax_C pi (lookupAt rIdx) cellLeafTri opk)
          (ruleTrans (congL pi (ap1 cellLeafTri opk) recR)
                     (congR pi (ap1 triF (pR p)) (cellLeafTri_at opk)))
      mid_val : Deriv (eqF (ap1 (C pi (constN 3) (C pi (lookupAt rIdx) cellLeafTri)) opk)
                           (ap2 pi dgRO (ap2 pi (ap1 triF (pR p)) filler)))
      mid_val =
        ruleTrans (ax_C pi (constN 3) (C pi (lookupAt rIdx) cellLeafTri) opk)
          (ruleTrans (congL pi (ap1 (C pi (lookupAt rIdx) cellLeafTri) opk)
                         (constN_eq 3 opk))
                     (congR pi (natCode 3) inner_val))
      adZe_val : Deriv (eqF (ap1 adZeBranch opk) (derRO (ap1 triF (pR p))))
      adZe_val =
        ruleTrans (ax_C pi (constN 2) (C pi (constN 3) (C pi (lookupAt rIdx) cellLeafTri)) opk)
          (ruleTrans (congL pi (ap1 (C pi (constN 3) (C pi (lookupAt rIdx) cellLeafTri)) opk)
                         (constN_eq 2 opk))
                     (congR pi (natCode 2) mid_val))
  in ruleTrans (opUnfold p ne)
       (ruleTrans (toNode p ne nl)
         (ruleTrans (toAd p ne htag) (ruleTrans ad_fires adZe_val)))

------------------------------------------------------------------------
-- Ad_Su:  pL p has label dgSu  =>  triF p = derRS (triF (pL (pL p))) (triF (pR p)) .

triF_op_Ad_Su : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) -> Deriv (eqF (dtag p) dgAd) ->
  Deriv (neg (eqF (pL p) O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst (pL p)) (natCode 1)) O) -> Deriv (eqF (dtag (pL p)) dgSu) ->
  Deriv (eqF (ap1 triF p) (derRS (ap1 triF (pL (pL p))) (ap1 triF (pR p))))
triF_op_Ad_Su p ne nl htag neL nlL htagLL =
  let opk = opkg p
      labA_eq : Deriv (eqF (ap1 labAidx opk) (natCode 1))
      labA_eq = ruleTrans (labA_at p ne) htagLL
      ad_fires : Deriv (eqF (ap1 adCellTri opk) (ap1 adSuBranch opk))
      ad_fires =
        ruleTrans (fork_false_to_snd adZeBranch restNodeAd testLeafA opk
                     (testLeafA_skip_nl p ne nlL))
                  (fork_true_to_fst adSuBranch adElseBranch testSuA opk
                     (testSuA_fire opk labA_eq))
      recA : Deriv (eqF (ap1 (lookupAt lIdx) opk) (ap1 triF (pL p)))
      recA = recPL p ne
      recR : Deriv (eqF (ap1 (lookupAt rIdx) opk) (ap1 triF (pR p)))
      recR = recPR p ne
      dL_eq : Deriv (eqF (ap1 (compose1U derLF (lookupAt lIdx)) opk) (ap1 triF (pL (pL p))))
      dL_eq =
        ruleTrans (compose1U_eq derLF (lookupAt lIdx) opk)
          (ruleTrans (cong1 derLF recA)
            (ruleTrans (cong1 derLF (triF_op_Su (pL p) neL nlL htagLL))
              (ruleTrans (derLF_eq (derSu (ap1 triF (pL (pL p)))))
                         (derChildL_Su (ap1 triF (pL (pL p)))))))
      inner_val : Deriv (eqF (ap1 (C pi (compose1U derLF (lookupAt lIdx)) (lookupAt rIdx)) opk)
                             (ap2 pi (ap1 triF (pL (pL p))) (ap1 triF (pR p))))
      inner_val =
        ruleTrans (ax_C pi (compose1U derLF (lookupAt lIdx)) (lookupAt rIdx) opk)
          (ruleTrans (congL pi (ap1 (lookupAt rIdx) opk) dL_eq)
                     (congR pi (ap1 triF (pL (pL p))) recR))
      mid_val : Deriv (eqF (ap1 (C pi (constN 4) (C pi (compose1U derLF (lookupAt lIdx)) (lookupAt rIdx))) opk)
                           (ap2 pi dgRS (ap2 pi (ap1 triF (pL (pL p))) (ap1 triF (pR p)))))
      mid_val =
        ruleTrans (ax_C pi (constN 4) (C pi (compose1U derLF (lookupAt lIdx)) (lookupAt rIdx)) opk)
          (ruleTrans (congL pi (ap1 (C pi (compose1U derLF (lookupAt lIdx)) (lookupAt rIdx)) opk)
                         (constN_eq 4 opk))
                     (congR pi (natCode 4) inner_val))
      adSu_val : Deriv (eqF (ap1 adSuBranch opk)
                            (derRS (ap1 triF (pL (pL p))) (ap1 triF (pR p))))
      adSu_val =
        ruleTrans (ax_C pi (constN 2) (C pi (constN 4) (C pi (compose1U derLF (lookupAt lIdx)) (lookupAt rIdx))) opk)
          (ruleTrans (congL pi (ap1 (C pi (constN 4) (C pi (compose1U derLF (lookupAt lIdx)) (lookupAt rIdx))) opk)
                         (constN_eq 2 opk))
                     (congR pi (natCode 2) mid_val))
  in ruleTrans (opUnfold p ne)
       (ruleTrans (toNode p ne nl)
         (ruleTrans (toAd p ne htag) (ruleTrans ad_fires adSu_val)))

------------------------------------------------------------------------
-- Ad_else:  pL p is a node with label k != 1 (Ad/RO/RS)  =>
--   triF p = derAd (triF (pL p)) (triF (pR p)) .

triF_op_Ad_else : (p : Term) (k : Nat) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) -> Deriv (eqF (dtag p) dgAd) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst (pL p)) (natCode 1)) O) ->
  NatNeqWitness k 1 -> Deriv (eqF (dtag (pL p)) (natCode k)) ->
  Deriv (eqF (ap1 triF p) (derAd (ap1 triF (pL p)) (ap1 triF (pR p))))
triF_op_Ad_else p k ne nl htag nlL wk htagLL =
  let opk = opkg p
      labA_eq : Deriv (eqF (ap1 labAidx opk) (natCode k))
      labA_eq = ruleTrans (labA_at p ne) htagLL
      ad_fires : Deriv (eqF (ap1 adCellTri opk) (ap1 adElseBranch opk))
      ad_fires =
        ruleTrans (fork_false_to_snd adZeBranch restNodeAd testLeafA opk
                     (testLeafA_skip_nl p ne nlL))
                  (fork_false_to_snd adSuBranch adElseBranch testSuA opk
                     (testSuA_skip k opk wk labA_eq))
      recA : Deriv (eqF (ap1 (lookupAt lIdx) opk) (ap1 triF (pL p)))
      recA = recPL p ne
      recR : Deriv (eqF (ap1 (lookupAt rIdx) opk) (ap1 triF (pR p)))
      recR = recPR p ne
  in ruleTrans (opUnfold p ne)
       (ruleTrans (toNode p ne nl)
         (ruleTrans (toAd p ne htag)
           (ruleTrans ad_fires
             (adElse_val opk (ap1 triF (pL p)) (ap1 triF (pR p)) recA recR))))
