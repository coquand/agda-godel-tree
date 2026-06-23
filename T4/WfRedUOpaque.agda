{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.WfRedUOpaque -- the OPAQUE wfRed equations on the UNSIZED DerCode coding.
-- Same opaque harness (T4.OpaqueHarness at wfStepU = stepOf Z wfCellNode) and
-- decoder; gives the child-validity EXTRACTION direction for the bigC dispatch,
-- plus the REJECT equation (junk label => wfRed = s O) that closes the
-- tag-exhaustiveness of the dispatch.
--
--   p!=O, Fst p = natCode 1                       => wfRed p = O               (leaf)
--   p!=O, test1 skips, dtag p = dgSu / dgRO       => wfRed p = wfRed (pL p)
--   p!=O, test1 skips, dtag p = dgAd / dgRS       => wfRed p = pi (wfRed (pL p)) (wfRed (pR p))
--   p!=O, test1 skips, dtag p not in {1,2,3,4}    => wfRed p = s O             (reject)
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.WfRedUOpaque where

open import T4.Base

open import T4.DerCodeS using ( dtag ; pL ; pR )
open import T4.BinTree using ( nIdx ; lIdx ; rIdx )
open import T4.FoldRec using ( lookupAt ; fold ; get_newK ; fold_at_O )
open import T4.ParsObj using ( stepOf )
open import T4.ProgParse using ( get_tag )
open import T4.OpaqueLookup using ( lookup_op )
open import T4.WfRedExtract using ( pLValueBound ; pRValueBound )
open import T4.NatEqReflect using ( natEqF_complete )

open import T4.WfRed
  using ( wfRed ; wfAdCell ; rejectCell ; wfRestRS ; wfRestRO ; wfRestAd ; wfCellNode )
open import T4.DerCode using ( dgSu ; dgAd ; dgRO ; dgRS )

open import T4.DerSrc
  using ( testEq ; fork_true_to_fst ; fork_false_to_snd ; testEq_fire ; testEq_skip
        ; w21 ; w31 ; w32 ; w41 ; w42 ; w43 )

open import BRA3.Church       using ( pi ; predecessor )
open import BRA3.PairAlgebra  using ( compose1U_eq ; Post )
open import BRA3.SubT.NatEq    using ( natEqF ; natEq_eq )
open import BRA3.SubT.V2NatNeq using ( natEqF_at_neq )

import T4.OpaqueHarness
private
  wfStepU : Fun1
  wfStepU = stepOf Z wfCellNode
open T4.OpaqueHarness.HBase rejectCell wfStepU

-- O is NOT valid:  wfRed O = s O  (the fold base is rejectCell = constN 1).
wfRed_O : Deriv (eqF (ap1 wfRed O) (ap1 s O))
wfRed_O = ruleTrans (fold_at_O rejectCell (Post wfStepU pi)) (constN_eq 1 O)

------------------------------------------------------------------------
-- SECTION 0.  Dispatch helpers.

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
    Deriv (eqF (ap1 wfStepU (opkg p)) (ap1 wfCellNode (opkg p)))
  toNode p ne nl =
    let opk = opkg p
        t1_O : Deriv (eqF (ap1 (C natEqF get_tag (constN 1)) opk) O)
        t1_O = ruleTrans (test1At p ne) nl
    in fork_false_to_snd Z wfCellNode (C natEqF get_tag (constN 1)) opk t1_O

  recLabel : (p : Term) -> Deriv (neg (eqF p O)) -> {tg : Term} ->
    Deriv (eqF (dtag p) tg) -> Deriv (eqF (ap1 nIdx (opkg p)) tg)
  recLabel p ne htag = ruleTrans (op_nIdx p ne) htag

  recPL : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 (lookupAt lIdx) (opkg p)) (ap1 wfRed (pL p)))
  recPL p ne =
    lookup_op rejectCell wfStepU lIdx (ap1 predecessor p) (pL p)
      (op_pL p ne) (pLValueBound p ne)

  recPR : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 (lookupAt rIdx) (opkg p)) (ap1 wfRed (pR p)))
  recPR p ne =
    lookup_op rejectCell wfStepU rIdx (ap1 predecessor p) (pR p)
      (op_pR p ne) (pRValueBound p ne)

  -- testEq k skips, from  neg (dtag p = natCode k) .
  skipNeg : (p : Term) (k : Nat) -> Deriv (neg (eqF p O)) ->
    Deriv (neg (eqF (dtag p) (natCode k))) ->
    Deriv (eqF (ap1 (testEq k) (opkg p)) O)
  skipNeg p k ne hneg =
    let opk = opkg p in
    ruleTrans (ax_C natEqF nIdx (constN k) opk)
      (ruleTrans (congL natEqF (ap1 (constN k) opk) (op_nIdx p ne))
        (ruleTrans (congR natEqF (dtag p) (constN_eq k opk))
                   (mp (natEqF_complete (dtag p) (natCode k)) hneg)))

  -- the pi-cell value  wfAdCell opk = pi (wfRed (pL p)) (wfRed (pR p)) .
  adCell_val : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 wfAdCell (opkg p)) (ap2 pi (ap1 wfRed (pL p)) (ap1 wfRed (pR p))))
  adCell_val p ne =
    let opk = opkg p in
    ruleTrans (ax_C pi (lookupAt lIdx) (lookupAt rIdx) opk)
      (ruleTrans (congL pi (ap1 (lookupAt rIdx) opk) (recPL p ne))
                 (congR pi (ap1 wfRed (pL p)) (recPR p ne)))

------------------------------------------------------------------------
-- SECTION 1.  Leaf:  wfRed p = O .

wfRed_op_Ze : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap1 Fst p) (natCode 1)) ->
  Deriv (eqF (ap1 wfRed p) O)
wfRed_op_Ze p ne htagB =
  let opk = opkg p
      t1_fire : Deriv (eqF (ap1 (C natEqF get_tag (constN 1)) opk) (ap1 s O))
      t1_fire = ruleTrans (test1At p ne)
                  (ruleTrans (congL natEqF (natCode 1) htagB) (natEq_eq 1))
      cell_fires : Deriv (eqF (ap1 wfStepU opk) (ap1 Z opk))
      cell_fires = fork_true_to_fst Z wfCellNode (C natEqF get_tag (constN 1)) opk t1_fire
  in ruleTrans (opUnfold p ne) (ruleTrans cell_fires (axZ opk))

------------------------------------------------------------------------
-- SECTION 2.  Node cases.

wfRed_op_Su : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) -> Deriv (eqF (dtag p) dgSu) ->
  Deriv (eqF (ap1 wfRed p) (ap1 wfRed (pL p)))
wfRed_op_Su p ne nl htag =
  let opk = opkg p
      nieq = recLabel p ne htag
      cell_fires : Deriv (eqF (ap1 wfCellNode opk) (ap1 (lookupAt lIdx) opk))
      cell_fires = fork_true_to_fst (lookupAt lIdx) wfRestAd (testEq 1) opk
                     (testEq_fire 1 opk nieq)
  in ruleTrans (opUnfold p ne)
       (ruleTrans (toNode p ne nl) (ruleTrans cell_fires (recPL p ne)))

wfRed_op_Ad : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) -> Deriv (eqF (dtag p) dgAd) ->
  Deriv (eqF (ap1 wfRed p) (ap2 pi (ap1 wfRed (pL p)) (ap1 wfRed (pR p))))
wfRed_op_Ad p ne nl htag =
  let opk = opkg p
      nieq = recLabel p ne htag
      cell_fires : Deriv (eqF (ap1 wfCellNode opk) (ap1 wfAdCell opk))
      cell_fires =
        ruleTrans (fork_false_to_snd (lookupAt lIdx) wfRestAd (testEq 1) opk
                     (testEq_skip 2 1 opk w21 nieq))
                  (fork_true_to_fst wfAdCell wfRestRO (testEq 2) opk
                     (testEq_fire 2 opk nieq))
  in ruleTrans (opUnfold p ne)
       (ruleTrans (toNode p ne nl) (ruleTrans cell_fires (adCell_val p ne)))

wfRed_op_RO : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) -> Deriv (eqF (dtag p) dgRO) ->
  Deriv (eqF (ap1 wfRed p) (ap1 wfRed (pL p)))
wfRed_op_RO p ne nl htag =
  let opk = opkg p
      nieq = recLabel p ne htag
      cell_fires : Deriv (eqF (ap1 wfCellNode opk) (ap1 (lookupAt lIdx) opk))
      cell_fires =
        ruleTrans (fork_false_to_snd (lookupAt lIdx) wfRestAd (testEq 1) opk
                     (testEq_skip 3 1 opk w31 nieq))
          (ruleTrans (fork_false_to_snd wfAdCell wfRestRO (testEq 2) opk
                        (testEq_skip 3 2 opk w32 nieq))
                     (fork_true_to_fst (lookupAt lIdx) wfRestRS (testEq 3) opk
                        (testEq_fire 3 opk nieq)))
  in ruleTrans (opUnfold p ne)
       (ruleTrans (toNode p ne nl) (ruleTrans cell_fires (recPL p ne)))

wfRed_op_RS : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) -> Deriv (eqF (dtag p) dgRS) ->
  Deriv (eqF (ap1 wfRed p) (ap2 pi (ap1 wfRed (pL p)) (ap1 wfRed (pR p))))
wfRed_op_RS p ne nl htag =
  let opk = opkg p
      nieq = recLabel p ne htag
      cell_fires : Deriv (eqF (ap1 wfCellNode opk) (ap1 wfAdCell opk))
      cell_fires =
        ruleTrans (fork_false_to_snd (lookupAt lIdx) wfRestAd (testEq 1) opk
                     (testEq_skip 4 1 opk w41 nieq))
          (ruleTrans (fork_false_to_snd wfAdCell wfRestRO (testEq 2) opk
                        (testEq_skip 4 2 opk w42 nieq))
            (ruleTrans (fork_false_to_snd (lookupAt lIdx) wfRestRS (testEq 3) opk
                          (testEq_skip 4 3 opk w43 nieq))
                       (fork_true_to_fst wfAdCell rejectCell (testEq 4) opk
                          (testEq_fire 4 opk nieq))))
  in ruleTrans (opUnfold p ne)
       (ruleTrans (toNode p ne nl) (ruleTrans cell_fires (adCell_val p ne)))

------------------------------------------------------------------------
-- SECTION 3.  Reject:  dtag p not in {1,2,3,4}  =>  wfRed p = s O .

wfRed_op_reject : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) ->
  Deriv (neg (eqF (dtag p) (natCode 1))) -> Deriv (neg (eqF (dtag p) (natCode 2))) ->
  Deriv (neg (eqF (dtag p) (natCode 3))) -> Deriv (neg (eqF (dtag p) (natCode 4))) ->
  Deriv (eqF (ap1 wfRed p) (ap1 s O))
wfRed_op_reject p ne nl n1 n2 n3 n4 =
  let opk = opkg p
      cell_fires : Deriv (eqF (ap1 wfCellNode opk) (ap1 rejectCell opk))
      cell_fires =
        ruleTrans (fork_false_to_snd (lookupAt lIdx) wfRestAd (testEq 1) opk
                     (skipNeg p 1 ne n1))
          (ruleTrans (fork_false_to_snd wfAdCell wfRestRO (testEq 2) opk
                        (skipNeg p 2 ne n2))
            (ruleTrans (fork_false_to_snd (lookupAt lIdx) wfRestRS (testEq 3) opk
                          (skipNeg p 3 ne n3))
                       (fork_false_to_snd wfAdCell rejectCell (testEq 4) opk
                          (skipNeg p 4 ne n4))))
  in ruleTrans (opUnfold p ne)
       (ruleTrans (toNode p ne nl)
         (ruleTrans cell_fires (constN_eq 1 opk)))
