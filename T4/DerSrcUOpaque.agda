{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.DerSrcUOpaque -- the OPAQUE srcF equations on the UNSIZED DerCode coding,
-- the source-endpoint analogue of T4.DerTriUOpaque.  Same opaque harness
-- (T4.OpaqueHarness at srcStepU = stepOf ze#F cellNode) and decoder; srcF has
-- no depth-2 dispatch so all five cases are flat.
--
--   p!=O, Fst p = 1                 => srcF p = ze#                            (leaf)
--   p!=O, Fst p = 2, dtag p = dgSu  => srcF p = su# (srcF (pL p))
--   p!=O, Fst p = 2, dtag p = dgAd  => srcF p = ad# (srcF (pL p)) (srcF (pR p))
--   p!=O, Fst p = 2, dtag p = dgRO  => srcF p = ad# ze# (srcF (pL p))
--   p!=O, Fst p = 2, dtag p = dgRS  => srcF p = ad# (su# (srcF (pL p))) (srcF (pR p))
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.DerSrcUOpaque where

open import T4.Base

open import T4.DerCode using ( dgZe ; dgSu ; dgAd ; dgRO ; dgRS )
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
        ; ze#F_at
        ; testEq ; fork_true_to_fst ; fork_false_to_snd ; testEq_fire ; testEq_skip
        ; w21 ; w31 ; w32 ; w41 ; w42 ; w43 )

open import BRA3.Church       using ( pi ; predecessor )
open import BRA3.PairAlgebra  using ( compose1U_eq )
open import BRA3.SubT.NatEq    using ( natEqF ; natEq_eq )
open import BRA3.SubT.V2NatNeq using ( natEqF_at_neq )

import T4.OpaqueHarness
private
  srcStepU : Fun1
  srcStepU = stepOf ze#F cellNode
open T4.OpaqueHarness.H srcStepU

------------------------------------------------------------------------
-- SECTION 0.  Leaf/node dispatch helpers (shared with DerTriUOpaque pattern).

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

  toNode : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) ->
    Deriv (eqF (ap1 srcStepU (opkg p)) (ap1 cellNode (opkg p)))
  toNode p ne nl =
    let opk = opkg p
        t1_O : Deriv (eqF (ap1 (C natEqF get_tag (constN 1)) opk) O)
        t1_O = ruleTrans (test1At p ne) nl
    in fork_false_to_snd ze#F cellNode (C natEqF get_tag (constN 1)) opk t1_O

  recLabel : (p : Term) -> Deriv (neg (eqF p O)) -> {tg : Term} ->
    Deriv (eqF (dtag p) tg) -> Deriv (eqF (ap1 nIdx (opkg p)) tg)
  recLabel p ne htag = ruleTrans (op_nIdx p ne) htag

  recPL : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 (lookupAt lIdx) (opkg p)) (ap1 srcF (pL p)))
  recPL p ne =
    lookup_op Z srcStepU lIdx (ap1 predecessor p) (pL p)
      (op_pL p ne) (pLValueBound p ne)

  recPR : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 (lookupAt rIdx) (opkg p)) (ap1 srcF (pR p)))
  recPR p ne =
    lookup_op Z srcStepU rIdx (ap1 predecessor p) (pR p)
      (op_pR p ne) (pRValueBound p ne)

------------------------------------------------------------------------
-- SECTION 1.  Leaf:  srcF p = ze# .

srcF_op_Ze : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap1 Fst p) (natCode 1)) ->
  Deriv (eqF (ap1 srcF p) ze#)
srcF_op_Ze p ne htagB =
  let opk = opkg p
      t1_fire : Deriv (eqF (ap1 (C natEqF get_tag (constN 1)) opk) (ap1 s O))
      t1_fire = ruleTrans (test1At p ne)
                  (ruleTrans (congL natEqF (natCode 1) htagB) (natEq_eq 1))
      cell_fires : Deriv (eqF (ap1 srcStepU opk) (ap1 ze#F opk))
      cell_fires = fork_true_to_fst ze#F cellNode (C natEqF get_tag (constN 1)) opk t1_fire
  in ruleTrans (opUnfold p ne) (ruleTrans cell_fires (ze#F_at opk))

------------------------------------------------------------------------
-- SECTION 2.  Node cases.

srcF_op_Su : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) -> Deriv (eqF (dtag p) dgSu) ->
  Deriv (eqF (ap1 srcF p) (su# (ap1 srcF (pL p))))
srcF_op_Su p ne htagB htag =
  let opk = opkg p
      nieq = recLabel p ne htag
      cell_fires : Deriv (eqF (ap1 cellNode opk) (ap1 suCell opk))
      cell_fires = fork_true_to_fst suCell restAd (testEq 1) opk (testEq_fire 1 opk nieq)
      suCell_val : Deriv (eqF (ap1 suCell opk) (su# (ap1 srcF (pL p))))
      suCell_val =
        ruleTrans (ax_C pi (constN 1) (lookupAt lIdx) opk)
          (ruleTrans (congL pi (ap1 (lookupAt lIdx) opk) (constN_eq 1 opk))
                     (congR pi (natCode 1) (recPL p ne)))
  in ruleTrans (opUnfold p ne)
       (ruleTrans (toNode p ne htagB) (ruleTrans cell_fires suCell_val))

srcF_op_Ad : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) -> Deriv (eqF (dtag p) dgAd) ->
  Deriv (eqF (ap1 srcF p) (ad# (ap1 srcF (pL p)) (ap1 srcF (pR p))))
srcF_op_Ad p ne htagB htag =
  let opk = opkg p
      nieq = recLabel p ne htag
      cell_fires : Deriv (eqF (ap1 cellNode opk) (ap1 adCell opk))
      cell_fires =
        ruleTrans (fork_false_to_snd suCell restAd (testEq 1) opk
                     (testEq_skip 2 1 opk w21 nieq))
                  (fork_true_to_fst adCell restRO (testEq 2) opk
                     (testEq_fire 2 opk nieq))
      inner_val : Deriv (eqF (ap1 (C pi (lookupAt lIdx) (lookupAt rIdx)) opk)
                             (ap2 pi (ap1 srcF (pL p)) (ap1 srcF (pR p))))
      inner_val =
        ruleTrans (ax_C pi (lookupAt lIdx) (lookupAt rIdx) opk)
          (ruleTrans (congL pi (ap1 (lookupAt rIdx) opk) (recPL p ne))
                     (congR pi (ap1 srcF (pL p)) (recPR p ne)))
      adCell_val : Deriv (eqF (ap1 adCell opk) (ad# (ap1 srcF (pL p)) (ap1 srcF (pR p))))
      adCell_val =
        ruleTrans (ax_C pi (constN 2) (C pi (lookupAt lIdx) (lookupAt rIdx)) opk)
          (ruleTrans (congL pi (ap1 (C pi (lookupAt lIdx) (lookupAt rIdx)) opk)
                         (constN_eq 2 opk))
                     (congR pi (natCode 2) inner_val))
  in ruleTrans (opUnfold p ne)
       (ruleTrans (toNode p ne htagB) (ruleTrans cell_fires adCell_val))

srcF_op_RO : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) -> Deriv (eqF (dtag p) dgRO) ->
  Deriv (eqF (ap1 srcF p) (ad# ze# (ap1 srcF (pL p))))
srcF_op_RO p ne htagB htag =
  let opk = opkg p
      nieq = recLabel p ne htag
      cell_fires : Deriv (eqF (ap1 cellNode opk) (ap1 roCell opk))
      cell_fires =
        ruleTrans (fork_false_to_snd suCell restAd (testEq 1) opk
                     (testEq_skip 3 1 opk w31 nieq))
          (ruleTrans (fork_false_to_snd adCell restRO (testEq 2) opk
                        (testEq_skip 3 2 opk w32 nieq))
                     (fork_true_to_fst roCell rsCell (testEq 3) opk
                        (testEq_fire 3 opk nieq)))
      inner_val : Deriv (eqF (ap1 (C pi ze#F (lookupAt lIdx)) opk)
                             (ap2 pi ze# (ap1 srcF (pL p))))
      inner_val =
        ruleTrans (ax_C pi ze#F (lookupAt lIdx) opk)
          (ruleTrans (congL pi (ap1 (lookupAt lIdx) opk) (ze#F_at opk))
                     (congR pi ze# (recPL p ne)))
      roCell_val : Deriv (eqF (ap1 roCell opk) (ad# ze# (ap1 srcF (pL p))))
      roCell_val =
        ruleTrans (ax_C pi (constN 2) (C pi ze#F (lookupAt lIdx)) opk)
          (ruleTrans (congL pi (ap1 (C pi ze#F (lookupAt lIdx)) opk) (constN_eq 2 opk))
                     (congR pi (natCode 2) inner_val))
  in ruleTrans (opUnfold p ne)
       (ruleTrans (toNode p ne htagB) (ruleTrans cell_fires roCell_val))

srcF_op_RS : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) -> Deriv (eqF (dtag p) dgRS) ->
  Deriv (eqF (ap1 srcF p) (ad# (su# (ap1 srcF (pL p))) (ap1 srcF (pR p))))
srcF_op_RS p ne htagB htag =
  let opk = opkg p
      nieq = recLabel p ne htag
      cell_fires : Deriv (eqF (ap1 cellNode opk) (ap1 rsCell opk))
      cell_fires =
        ruleTrans (fork_false_to_snd suCell restAd (testEq 1) opk
                     (testEq_skip 4 1 opk w41 nieq))
          (ruleTrans (fork_false_to_snd adCell restRO (testEq 2) opk
                        (testEq_skip 4 2 opk w42 nieq))
                     (fork_false_to_snd roCell rsCell (testEq 3) opk
                        (testEq_skip 4 3 opk w43 nieq)))
      left_val : Deriv (eqF (ap1 (C pi (constN 1) (lookupAt lIdx)) opk)
                            (su# (ap1 srcF (pL p))))
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
  in ruleTrans (opUnfold p ne)
       (ruleTrans (toNode p ne htagB) (ruleTrans cell_fires rsCell_val))
