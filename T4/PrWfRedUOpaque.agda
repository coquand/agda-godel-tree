{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.PrWfRedUOpaque -- the OPAQUE wfRed equations over arbitrary codes p : Term,
-- the validity analogue of T4.PrSrcUOpaque.  wfRed = binRec rejectCell Z
-- wfCellNode = fold rejectCell (Post (stepOf Z wfCellNode) pi), so the harness
-- is  HBase rejectCell wfStepU  (base = reject).  wfRed reads no fun-codes.
--
--   reflO  => wfRed p = O
--   unary (ap1c/rO/rU/rC/rRb) => wfRed p = wfRed (pL p)
--   binary (ap2c/rV/rRs)      => wfRed p = pi (wfRed (pL p)) (wfRed (pR p))
--   reject (tag not in 1..8)  => wfRed p = s O
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.PrWfRedUOpaque where

open import T4.Base

open import T4.PrDerCode using ( dgAp1c ; dgAp2c ; dgRo ; dgRu ; dgRv ; dgRC ; dgRb ; dgRs )
open import T4.PrDev using ( idxTest_fire ; idxTest_skip )
open import T4.PrWfRed
  using ( wfRed ; derTagIdx ; wfAdCell ; unaryCell ; rejectCell
        ; w_l2 ; w_l3 ; w_l4 ; w_l5 ; w_l6 ; w_l7 ; w_l8 ; wfCellNode ; testTag )

open import T4.DerCodeS using ( dtag ; pL ; pR )
open import T4.BinTree using ( nIdx ; lIdx ; rIdx )
open import T4.FoldRec using ( lookupAt ; fold ; get_newK )
open import T4.ParsObj using ( stepOf )
open import T4.ProgParse using ( get_tag )
open import T4.OpaqueLookup using ( lookup_op )
open import T4.WfRedExtract using ( pLValueBound ; pRValueBound )
open import T4.DerSrc using ( fork_true_to_fst ; fork_false_to_snd )

open import BRA3.Church       using ( pi ; predecessor )
open import BRA3.PairAlgebra  using ( compose1U ; compose1U_eq )
open import BRA3.SubT.NatEq    using ( natEqF ; natEq_eq )
open import BRA3.SubT.V2NatNeq using ( NatNeqWitness ; natEqF_at_neq ; decideNatNeq )

import T4.OpaqueHarness
private
  wfStepU : Fun1
  wfStepU = stepOf Z wfCellNode
open T4.OpaqueHarness.HBase rejectCell wfStepU

------------------------------------------------------------------------
-- SECTION 1.  Recovery helpers.

private
  op_tag : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 get_tag (opkg p)) (ap1 Fst p))
  op_tag p ne = ruleTrans (compose1U_eq Fst get_newK (opkg p)) (cong1 Fst (op_newK p ne))

  test1At : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 (C natEqF get_tag (constN 1)) (opkg p)) (ap2 natEqF (ap1 Fst p) (natCode 1)))
  test1At p ne =
    ruleTrans (ax_C natEqF get_tag (constN 1) (opkg p))
      (ruleTrans (congL natEqF (ap1 (constN 1) (opkg p)) (op_tag p ne))
                 (congR natEqF (ap1 Fst p) (constN_eq 1 (opkg p))))

  toNode : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) ->
    Deriv (eqF (ap1 wfStepU (opkg p)) (ap1 wfCellNode (opkg p)))
  toNode p ne nl =
    fork_false_to_snd Z wfCellNode (C natEqF get_tag (constN 1)) (opkg p)
      (ruleTrans (test1At p ne) nl)

  recTag : (p : Term) -> Deriv (neg (eqF p O)) -> {tg : Term} ->
    Deriv (eqF (ap1 Fst (dtag p)) tg) -> Deriv (eqF (ap1 derTagIdx (opkg p)) tg)
  recTag p ne htag =
    ruleTrans (compose1U_eq Fst nIdx (opkg p)) (ruleTrans (cong1 Fst (op_nIdx p ne)) htag)

  recPL : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 unaryCell (opkg p)) (ap1 wfRed (pL p)))
  recPL p ne = lookup_op rejectCell wfStepU lIdx (ap1 predecessor p) (pL p) (op_pL p ne) (pLValueBound p ne)
  recPR : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 (lookupAt rIdx) (opkg p)) (ap1 wfRed (pR p)))
  recPR p ne = lookup_op rejectCell wfStepU rIdx (ap1 predecessor p) (pR p) (op_pR p ne) (pRValueBound p ne)

  ad_val : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 wfAdCell (opkg p)) (ap2 pi (ap1 wfRed (pL p)) (ap1 wfRed (pR p))))
  ad_val p ne =
    let opk = opkg p
    in ruleTrans (ax_C pi (lookupAt lIdx) (lookupAt rIdx) opk)
         (ruleTrans (congL pi (ap1 (lookupAt rIdx) opk) (recPL p ne))
                    (congR pi (ap1 wfRed (pL p)) (recPR p ne)))

  toCell : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) ->
    Deriv (eqF (ap1 wfRed p) (ap1 wfCellNode (opkg p)))
  toCell p ne nl = ruleTrans (opUnfold p ne) (toNode p ne nl)

  wn : (m k : Nat) -> ((Eq m k) -> Empty) -> NatNeqWitness m k
  wn m k pf = decideNatNeq m k pf
  w21 : NatNeqWitness 2 1
  w21 = decideNatNeq 2 1 (\ ())

------------------------------------------------------------------------
-- SECTION 2.  Leaf.

wfRed_op_reflO : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap1 Fst p) (natCode 1)) -> Deriv (eqF (ap1 wfRed p) O)
wfRed_op_reflO p ne htagB =
  let opk = opkg p
      t1_fire = ruleTrans (test1At p ne) (ruleTrans (congL natEqF (natCode 1) htagB) (natEq_eq 1))
      cell_fires = fork_true_to_fst Z wfCellNode (C natEqF get_tag (constN 1)) opk t1_fire
  in ruleTrans (opUnfold p ne) (ruleTrans cell_fires (axZ opk))

------------------------------------------------------------------------
-- SECTION 3.  Unary-node equations.

wfRed_op_ap1c : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) -> Deriv (eqF (ap1 Fst (dtag p)) dgAp1c) ->
  Deriv (eqF (ap1 wfRed p) (ap1 wfRed (pL p)))
wfRed_op_ap1c p ne nl htag =
  let opk = opkg p
      tg = recTag p ne htag
      fires = fork_true_to_fst unaryCell w_l2 (testTag 1) opk (idxTest_fire derTagIdx 1 opk tg)
  in ruleTrans (toCell p ne nl) (ruleTrans fires (recPL p ne))

wfRed_op_rO : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) -> Deriv (eqF (ap1 Fst (dtag p)) dgRo) ->
  Deriv (eqF (ap1 wfRed p) (ap1 wfRed (pL p)))
wfRed_op_rO p ne nl htag =
  let opk = opkg p
      tg = recTag p ne htag
      fires =
        ruleTrans (fork_false_to_snd unaryCell w_l2 (testTag 1) opk (idxTest_skip derTagIdx 3 1 opk (wn 3 1 (\ ())) tg))
          (ruleTrans (fork_false_to_snd wfAdCell w_l3 (testTag 2) opk (idxTest_skip derTagIdx 3 2 opk (wn 3 2 (\ ())) tg))
                     (fork_true_to_fst unaryCell w_l4 (testTag 3) opk (idxTest_fire derTagIdx 3 opk tg)))
  in ruleTrans (toCell p ne nl) (ruleTrans fires (recPL p ne))

wfRed_op_rU : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) -> Deriv (eqF (ap1 Fst (dtag p)) dgRu) ->
  Deriv (eqF (ap1 wfRed p) (ap1 wfRed (pL p)))
wfRed_op_rU p ne nl htag =
  let opk = opkg p
      tg = recTag p ne htag
      fires =
        ruleTrans (fork_false_to_snd unaryCell w_l2 (testTag 1) opk (idxTest_skip derTagIdx 4 1 opk (wn 4 1 (\ ())) tg))
          (ruleTrans (fork_false_to_snd wfAdCell w_l3 (testTag 2) opk (idxTest_skip derTagIdx 4 2 opk (wn 4 2 (\ ())) tg))
            (ruleTrans (fork_false_to_snd unaryCell w_l4 (testTag 3) opk (idxTest_skip derTagIdx 4 3 opk (wn 4 3 (\ ())) tg))
                       (fork_true_to_fst unaryCell w_l5 (testTag 4) opk (idxTest_fire derTagIdx 4 opk tg))))
  in ruleTrans (toCell p ne nl) (ruleTrans fires (recPL p ne))

wfRed_op_rC : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) -> Deriv (eqF (ap1 Fst (dtag p)) dgRC) ->
  Deriv (eqF (ap1 wfRed p) (ap1 wfRed (pL p)))
wfRed_op_rC p ne nl htag =
  let opk = opkg p
      tg = recTag p ne htag
      fires =
        ruleTrans (fork_false_to_snd unaryCell w_l2 (testTag 1) opk (idxTest_skip derTagIdx 6 1 opk (wn 6 1 (\ ())) tg))
          (ruleTrans (fork_false_to_snd wfAdCell w_l3 (testTag 2) opk (idxTest_skip derTagIdx 6 2 opk (wn 6 2 (\ ())) tg))
            (ruleTrans (fork_false_to_snd unaryCell w_l4 (testTag 3) opk (idxTest_skip derTagIdx 6 3 opk (wn 6 3 (\ ())) tg))
              (ruleTrans (fork_false_to_snd unaryCell w_l5 (testTag 4) opk (idxTest_skip derTagIdx 6 4 opk (wn 6 4 (\ ())) tg))
                (ruleTrans (fork_false_to_snd wfAdCell w_l6 (testTag 5) opk (idxTest_skip derTagIdx 6 5 opk (wn 6 5 (\ ())) tg))
                           (fork_true_to_fst unaryCell w_l7 (testTag 6) opk (idxTest_fire derTagIdx 6 opk tg))))))
  in ruleTrans (toCell p ne nl) (ruleTrans fires (recPL p ne))

wfRed_op_rRb : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) -> Deriv (eqF (ap1 Fst (dtag p)) dgRb) ->
  Deriv (eqF (ap1 wfRed p) (ap1 wfRed (pL p)))
wfRed_op_rRb p ne nl htag =
  let opk = opkg p
      tg = recTag p ne htag
      fires =
        ruleTrans (fork_false_to_snd unaryCell w_l2 (testTag 1) opk (idxTest_skip derTagIdx 7 1 opk (wn 7 1 (\ ())) tg))
          (ruleTrans (fork_false_to_snd wfAdCell w_l3 (testTag 2) opk (idxTest_skip derTagIdx 7 2 opk (wn 7 2 (\ ())) tg))
            (ruleTrans (fork_false_to_snd unaryCell w_l4 (testTag 3) opk (idxTest_skip derTagIdx 7 3 opk (wn 7 3 (\ ())) tg))
              (ruleTrans (fork_false_to_snd unaryCell w_l5 (testTag 4) opk (idxTest_skip derTagIdx 7 4 opk (wn 7 4 (\ ())) tg))
                (ruleTrans (fork_false_to_snd wfAdCell w_l6 (testTag 5) opk (idxTest_skip derTagIdx 7 5 opk (wn 7 5 (\ ())) tg))
                  (ruleTrans (fork_false_to_snd unaryCell w_l7 (testTag 6) opk (idxTest_skip derTagIdx 7 6 opk (wn 7 6 (\ ())) tg))
                             (fork_true_to_fst unaryCell w_l8 (testTag 7) opk (idxTest_fire derTagIdx 7 opk tg)))))))
  in ruleTrans (toCell p ne nl) (ruleTrans fires (recPL p ne))

------------------------------------------------------------------------
-- SECTION 4.  Binary-node equations.

wfRed_op_ap2c : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) -> Deriv (eqF (ap1 Fst (dtag p)) dgAp2c) ->
  Deriv (eqF (ap1 wfRed p) (ap2 pi (ap1 wfRed (pL p)) (ap1 wfRed (pR p))))
wfRed_op_ap2c p ne nl htag =
  let opk = opkg p
      tg = recTag p ne htag
      fires =
        ruleTrans (fork_false_to_snd unaryCell w_l2 (testTag 1) opk (idxTest_skip derTagIdx 2 1 opk w21 tg))
                  (fork_true_to_fst wfAdCell w_l3 (testTag 2) opk (idxTest_fire derTagIdx 2 opk tg))
  in ruleTrans (toCell p ne nl) (ruleTrans fires (ad_val p ne))

wfRed_op_rV : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) -> Deriv (eqF (ap1 Fst (dtag p)) dgRv) ->
  Deriv (eqF (ap1 wfRed p) (ap2 pi (ap1 wfRed (pL p)) (ap1 wfRed (pR p))))
wfRed_op_rV p ne nl htag =
  let opk = opkg p
      tg = recTag p ne htag
      fires =
        ruleTrans (fork_false_to_snd unaryCell w_l2 (testTag 1) opk (idxTest_skip derTagIdx 5 1 opk (wn 5 1 (\ ())) tg))
          (ruleTrans (fork_false_to_snd wfAdCell w_l3 (testTag 2) opk (idxTest_skip derTagIdx 5 2 opk (wn 5 2 (\ ())) tg))
            (ruleTrans (fork_false_to_snd unaryCell w_l4 (testTag 3) opk (idxTest_skip derTagIdx 5 3 opk (wn 5 3 (\ ())) tg))
              (ruleTrans (fork_false_to_snd unaryCell w_l5 (testTag 4) opk (idxTest_skip derTagIdx 5 4 opk (wn 5 4 (\ ())) tg))
                         (fork_true_to_fst wfAdCell w_l6 (testTag 5) opk (idxTest_fire derTagIdx 5 opk tg)))))
  in ruleTrans (toCell p ne nl) (ruleTrans fires (ad_val p ne))

wfRed_op_rRs : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) -> Deriv (eqF (ap1 Fst (dtag p)) dgRs) ->
  Deriv (eqF (ap1 wfRed p) (ap2 pi (ap1 wfRed (pL p)) (ap1 wfRed (pR p))))
wfRed_op_rRs p ne nl htag =
  let opk = opkg p
      tg = recTag p ne htag
      fires =
        ruleTrans (fork_false_to_snd unaryCell w_l2 (testTag 1) opk (idxTest_skip derTagIdx 8 1 opk (wn 8 1 (\ ())) tg))
          (ruleTrans (fork_false_to_snd wfAdCell w_l3 (testTag 2) opk (idxTest_skip derTagIdx 8 2 opk (wn 8 2 (\ ())) tg))
            (ruleTrans (fork_false_to_snd unaryCell w_l4 (testTag 3) opk (idxTest_skip derTagIdx 8 3 opk (wn 8 3 (\ ())) tg))
              (ruleTrans (fork_false_to_snd unaryCell w_l5 (testTag 4) opk (idxTest_skip derTagIdx 8 4 opk (wn 8 4 (\ ())) tg))
                (ruleTrans (fork_false_to_snd wfAdCell w_l6 (testTag 5) opk (idxTest_skip derTagIdx 8 5 opk (wn 8 5 (\ ())) tg))
                  (ruleTrans (fork_false_to_snd unaryCell w_l7 (testTag 6) opk (idxTest_skip derTagIdx 8 6 opk (wn 8 6 (\ ())) tg))
                    (ruleTrans (fork_false_to_snd unaryCell w_l8 (testTag 7) opk (idxTest_skip derTagIdx 8 7 opk (wn 8 7 (\ ())) tg))
                               (fork_true_to_fst wfAdCell rejectCell (testTag 8) opk (idxTest_fire derTagIdx 8 opk tg))))))))
  in ruleTrans (toCell p ne nl) (ruleTrans fires (ad_val p ne))

------------------------------------------------------------------------
-- SECTION 5.  Reject: junk tag (none of 1..8) => wfRed p = s O.

wfRed_op_reject : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) ->
  ((k : Nat) -> Deriv (eqF (ap1 (testTag k) (opkg p)) O)) ->  -- every tag-test skips
  Deriv (eqF (ap1 wfRed p) (ap1 s O))
wfRed_op_reject p ne nl skip =
  let opk = opkg p
      fires =
        ruleTrans (fork_false_to_snd unaryCell w_l2 (testTag 1) opk (skip 1))
          (ruleTrans (fork_false_to_snd wfAdCell w_l3 (testTag 2) opk (skip 2))
            (ruleTrans (fork_false_to_snd unaryCell w_l4 (testTag 3) opk (skip 3))
              (ruleTrans (fork_false_to_snd unaryCell w_l5 (testTag 4) opk (skip 4))
                (ruleTrans (fork_false_to_snd wfAdCell w_l6 (testTag 5) opk (skip 5))
                  (ruleTrans (fork_false_to_snd unaryCell w_l7 (testTag 6) opk (skip 6))
                    (ruleTrans (fork_false_to_snd unaryCell w_l8 (testTag 7) opk (skip 7))
                               (fork_false_to_snd wfAdCell rejectCell (testTag 8) opk (skip 8))))))))
  in ruleTrans (toCell p ne nl) (ruleTrans fires (constN_eq 1 opk))
