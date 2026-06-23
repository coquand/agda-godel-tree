{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.PrWfRedUOpaqueImp -- IMP-FORM opaque wfRed equations for the full p.r.
-- calculus, carried under [negLeaf, htag] (nodes) / Hleaf (leaf).  Same flat
-- dispatch as srcF/tgtF; base = rejectCell (HBase rejectCell).  Used in the
-- cov-dispatch to extract child validity from  wfRed p = O .
--
--   reflO  => wfRed p = O
--   unary (ap1c/rO/rU/rC/rRb) => wfRed p = wfRed (pL p)
--   binary (ap2c/rV/rRs)      => wfRed p = pi (wfRed (pL p)) (wfRed (pR p))
--
-- No holes, no postulates, no termination warnings (only the benign
-- RuleInst3:328 unreachable-clauses warning); --safe --without-K --exact-split.

module T4.PrWfRedUOpaqueImp where

open import T4.Base

open import T4.PrDerCode using ( dgAp1c ; dgAp2c ; dgRo ; dgRu ; dgRv ; dgRC ; dgRb ; dgRs )
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

open import T4.ForkImp
  using ( fork_true_to_fst_imp ; fork_false_to_snd_imp ; natEqFire_imp ; natEqSkip_imp )
open import T4.CtxKit using ( lift2 ; trans2c )
open import T4.NatEqReflect using ( natEqF_complete )
open import T4.Thm12.ImpHelpers using ( impLift ; impEqTrans )

open import BRA3.Church       using ( pi ; predecessor )
open import BRA3.PairAlgebra  using ( compose1U ; compose1U_eq )
open import BRA3.SubT.NatEq    using ( natEqF )
open import BRA3.SubT.V2NatNeq using ( NatNeqWitness ; decideNatNeq )
open import BRA3.Contrapositive using ( compI ; liftP ; identP )

import T4.OpaqueHarness
private
  wfStepU : Fun1
  wfStepU = stepOf Z wfCellNode
open T4.OpaqueHarness.HBase rejectCell wfStepU

private
  wn : (m k : Nat) -> ((Eq m k) -> Empty) -> NatNeqWitness m k
  wn m k pf = decideNatNeq m k pf

  op_tag : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 get_tag (opkg p)) (ap1 Fst p))
  op_tag p ne = ruleTrans (compose1U_eq Fst get_newK (opkg p)) (cong1 Fst (op_newK p ne))

  test1At : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 (C natEqF get_tag (constN 1)) (opkg p)) (ap2 natEqF (ap1 Fst p) (natCode 1)))
  test1At p ne =
    ruleTrans (ax_C natEqF get_tag (constN 1) (opkg p))
      (ruleTrans (congL natEqF (ap1 (constN 1) (opkg p)) (op_tag p ne))
                 (congR natEqF (ap1 Fst p) (constN_eq 1 (opkg p))))

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

  module Node (p : Term) (ne : Deriv (neg (eqF p O))) (lbl : Term) where
    opk = opkg p
    negLeaf : Formula
    negLeaf = neg (eqF (ap1 Fst p) (natCode 1))
    htag : Formula
    htag = eqF (ap1 Fst (dtag p)) lbl
    t1f : Term
    t1f = ap1 (C natEqF get_tag (constN 1)) opk
    nl_neg : Deriv (imp negLeaf (eqF t1f O))
    nl_neg = impEqTrans t1f (ap2 natEqF (ap1 Fst p) (natCode 1)) O
               (impLift (test1At p ne)) (natEqF_complete (ap1 Fst p) (natCode 1))
    step2 : Deriv (imp negLeaf (imp htag (eqF (ap1 wfStepU opk) (ap1 wfCellNode opk))))
    step2 = compI (fork_false_to_snd_imp negLeaf Z wfCellNode
                     (C natEqF get_tag (constN 1)) opk nl_neg)
                  (axK (eqF (ap1 wfStepU opk) (ap1 wfCellNode opk)) htag)
    derTag_bare : Deriv (eqF (ap1 derTagIdx opk) (ap1 Fst (dtag p)))
    derTag_bare = ruleTrans (compose1U_eq Fst nIdx opk) (cong1 Fst (op_nIdx p ne))
    nieq_imp : Deriv (imp htag (eqF (ap1 derTagIdx opk) lbl))
    nieq_imp = impEqTrans (ap1 derTagIdx opk) (ap1 Fst (dtag p)) lbl
                 (impLift derTag_bare) (identP htag)

  mkChain : (p : Term) (ne : Deriv (neg (eqF p O))) (negLeaf htag : Formula) (cell : Fun1) (rhs : Term) ->
    Deriv (imp negLeaf (imp htag (eqF (ap1 wfStepU (opkg p)) (ap1 wfCellNode (opkg p))))) ->
    Deriv (imp htag (eqF (ap1 wfCellNode (opkg p)) (ap1 cell (opkg p)))) ->
    Deriv (eqF (ap1 cell (opkg p)) rhs) ->
    Deriv (imp negLeaf (imp htag (eqF (ap1 wfRed p) rhs)))
  mkChain p ne negLeaf htag cell rhs step2 node_fires cell_val =
    let opk = opkg p
    in trans2c (ap1 wfRed p) (ap1 wfStepU opk) rhs
         (lift2 negLeaf htag (opUnfold p ne))
         (trans2c (ap1 wfStepU opk) (ap1 wfCellNode opk) rhs step2
           (trans2c (ap1 wfCellNode opk) (ap1 cell opk) rhs
             (liftP negLeaf node_fires) (lift2 negLeaf htag cell_val)))

------------------------------------------------------------------------
-- SECTION 2.  Leaf.

wfRed_op_reflO_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (eqF (ap1 Fst p) (natCode 1)) (eqF (ap1 wfRed p) O))
wfRed_op_reflO_imp p ne =
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
-- SECTION 3.  Unary-node equations  (cell = unaryCell, rhs = wfRed (pL p)).

wfRed_op_ap1c_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (ap1 Fst (dtag p)) dgAp1c) (eqF (ap1 wfRed p) (ap1 wfRed (pL p)))))
wfRed_op_ap1c_imp p ne =
  let open Node p ne dgAp1c
      node_fires = fork_true_to_fst_imp htag unaryCell w_l2 (testTag 1) opk
                     (natEqFire_imp htag derTagIdx 1 opk nieq_imp)
  in mkChain p ne negLeaf htag unaryCell (ap1 wfRed (pL p)) step2 node_fires (recPL p ne)

wfRed_op_rO_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (ap1 Fst (dtag p)) dgRo) (eqF (ap1 wfRed p) (ap1 wfRed (pL p)))))
wfRed_op_rO_imp p ne =
  let open Node p ne dgRo
      node_fires =
        impEqTrans (ap1 wfCellNode opk) (ap1 w_l2 opk) (ap1 unaryCell opk)
          (fork_false_to_snd_imp htag unaryCell w_l2 (testTag 1) opk
             (natEqSkip_imp htag derTagIdx 3 1 opk (wn 3 1 (\ ())) nieq_imp))
          (impEqTrans (ap1 w_l2 opk) (ap1 w_l3 opk) (ap1 unaryCell opk)
            (fork_false_to_snd_imp htag wfAdCell w_l3 (testTag 2) opk
               (natEqSkip_imp htag derTagIdx 3 2 opk (wn 3 2 (\ ())) nieq_imp))
            (fork_true_to_fst_imp htag unaryCell w_l4 (testTag 3) opk
               (natEqFire_imp htag derTagIdx 3 opk nieq_imp)))
  in mkChain p ne negLeaf htag unaryCell (ap1 wfRed (pL p)) step2 node_fires (recPL p ne)

wfRed_op_rU_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (ap1 Fst (dtag p)) dgRu) (eqF (ap1 wfRed p) (ap1 wfRed (pL p)))))
wfRed_op_rU_imp p ne =
  let open Node p ne dgRu
      node_fires =
        impEqTrans (ap1 wfCellNode opk) (ap1 w_l2 opk) (ap1 unaryCell opk)
          (fork_false_to_snd_imp htag unaryCell w_l2 (testTag 1) opk
             (natEqSkip_imp htag derTagIdx 4 1 opk (wn 4 1 (\ ())) nieq_imp))
          (impEqTrans (ap1 w_l2 opk) (ap1 w_l3 opk) (ap1 unaryCell opk)
            (fork_false_to_snd_imp htag wfAdCell w_l3 (testTag 2) opk
               (natEqSkip_imp htag derTagIdx 4 2 opk (wn 4 2 (\ ())) nieq_imp))
            (impEqTrans (ap1 w_l3 opk) (ap1 w_l4 opk) (ap1 unaryCell opk)
              (fork_false_to_snd_imp htag unaryCell w_l4 (testTag 3) opk
                 (natEqSkip_imp htag derTagIdx 4 3 opk (wn 4 3 (\ ())) nieq_imp))
              (fork_true_to_fst_imp htag unaryCell w_l5 (testTag 4) opk
                 (natEqFire_imp htag derTagIdx 4 opk nieq_imp))))
  in mkChain p ne negLeaf htag unaryCell (ap1 wfRed (pL p)) step2 node_fires (recPL p ne)

wfRed_op_rC_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (ap1 Fst (dtag p)) dgRC) (eqF (ap1 wfRed p) (ap1 wfRed (pL p)))))
wfRed_op_rC_imp p ne =
  let open Node p ne dgRC
      node_fires =
        impEqTrans (ap1 wfCellNode opk) (ap1 w_l2 opk) (ap1 unaryCell opk)
          (fork_false_to_snd_imp htag unaryCell w_l2 (testTag 1) opk
             (natEqSkip_imp htag derTagIdx 6 1 opk (wn 6 1 (\ ())) nieq_imp))
          (impEqTrans (ap1 w_l2 opk) (ap1 w_l3 opk) (ap1 unaryCell opk)
            (fork_false_to_snd_imp htag wfAdCell w_l3 (testTag 2) opk
               (natEqSkip_imp htag derTagIdx 6 2 opk (wn 6 2 (\ ())) nieq_imp))
            (impEqTrans (ap1 w_l3 opk) (ap1 w_l4 opk) (ap1 unaryCell opk)
              (fork_false_to_snd_imp htag unaryCell w_l4 (testTag 3) opk
                 (natEqSkip_imp htag derTagIdx 6 3 opk (wn 6 3 (\ ())) nieq_imp))
              (impEqTrans (ap1 w_l4 opk) (ap1 w_l5 opk) (ap1 unaryCell opk)
                (fork_false_to_snd_imp htag unaryCell w_l5 (testTag 4) opk
                   (natEqSkip_imp htag derTagIdx 6 4 opk (wn 6 4 (\ ())) nieq_imp))
                (impEqTrans (ap1 w_l5 opk) (ap1 w_l6 opk) (ap1 unaryCell opk)
                  (fork_false_to_snd_imp htag wfAdCell w_l6 (testTag 5) opk
                     (natEqSkip_imp htag derTagIdx 6 5 opk (wn 6 5 (\ ())) nieq_imp))
                  (fork_true_to_fst_imp htag unaryCell w_l7 (testTag 6) opk
                     (natEqFire_imp htag derTagIdx 6 opk nieq_imp))))))
  in mkChain p ne negLeaf htag unaryCell (ap1 wfRed (pL p)) step2 node_fires (recPL p ne)

wfRed_op_rRb_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (ap1 Fst (dtag p)) dgRb) (eqF (ap1 wfRed p) (ap1 wfRed (pL p)))))
wfRed_op_rRb_imp p ne =
  let open Node p ne dgRb
      node_fires =
        impEqTrans (ap1 wfCellNode opk) (ap1 w_l2 opk) (ap1 unaryCell opk)
          (fork_false_to_snd_imp htag unaryCell w_l2 (testTag 1) opk
             (natEqSkip_imp htag derTagIdx 7 1 opk (wn 7 1 (\ ())) nieq_imp))
          (impEqTrans (ap1 w_l2 opk) (ap1 w_l3 opk) (ap1 unaryCell opk)
            (fork_false_to_snd_imp htag wfAdCell w_l3 (testTag 2) opk
               (natEqSkip_imp htag derTagIdx 7 2 opk (wn 7 2 (\ ())) nieq_imp))
            (impEqTrans (ap1 w_l3 opk) (ap1 w_l4 opk) (ap1 unaryCell opk)
              (fork_false_to_snd_imp htag unaryCell w_l4 (testTag 3) opk
                 (natEqSkip_imp htag derTagIdx 7 3 opk (wn 7 3 (\ ())) nieq_imp))
              (impEqTrans (ap1 w_l4 opk) (ap1 w_l5 opk) (ap1 unaryCell opk)
                (fork_false_to_snd_imp htag unaryCell w_l5 (testTag 4) opk
                   (natEqSkip_imp htag derTagIdx 7 4 opk (wn 7 4 (\ ())) nieq_imp))
                (impEqTrans (ap1 w_l5 opk) (ap1 w_l6 opk) (ap1 unaryCell opk)
                  (fork_false_to_snd_imp htag wfAdCell w_l6 (testTag 5) opk
                     (natEqSkip_imp htag derTagIdx 7 5 opk (wn 7 5 (\ ())) nieq_imp))
                  (impEqTrans (ap1 w_l6 opk) (ap1 w_l7 opk) (ap1 unaryCell opk)
                    (fork_false_to_snd_imp htag unaryCell w_l7 (testTag 6) opk
                       (natEqSkip_imp htag derTagIdx 7 6 opk (wn 7 6 (\ ())) nieq_imp))
                    (fork_true_to_fst_imp htag unaryCell w_l8 (testTag 7) opk
                       (natEqFire_imp htag derTagIdx 7 opk nieq_imp)))))))
  in mkChain p ne negLeaf htag unaryCell (ap1 wfRed (pL p)) step2 node_fires (recPL p ne)

------------------------------------------------------------------------
-- SECTION 4.  Binary-node equations  (cell = wfAdCell, rhs = pi (wfRed pL) (wfRed pR)).

wfRed_op_ap2c_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (ap1 Fst (dtag p)) dgAp2c)
                  (eqF (ap1 wfRed p) (ap2 pi (ap1 wfRed (pL p)) (ap1 wfRed (pR p))))))
wfRed_op_ap2c_imp p ne =
  let open Node p ne dgAp2c
      node_fires =
        impEqTrans (ap1 wfCellNode opk) (ap1 w_l2 opk) (ap1 wfAdCell opk)
          (fork_false_to_snd_imp htag unaryCell w_l2 (testTag 1) opk
             (natEqSkip_imp htag derTagIdx 2 1 opk (wn 2 1 (\ ())) nieq_imp))
          (fork_true_to_fst_imp htag wfAdCell w_l3 (testTag 2) opk
             (natEqFire_imp htag derTagIdx 2 opk nieq_imp))
  in mkChain p ne negLeaf htag wfAdCell (ap2 pi (ap1 wfRed (pL p)) (ap1 wfRed (pR p))) step2 node_fires (ad_val p ne)

wfRed_op_rV_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (ap1 Fst (dtag p)) dgRv)
                  (eqF (ap1 wfRed p) (ap2 pi (ap1 wfRed (pL p)) (ap1 wfRed (pR p))))))
wfRed_op_rV_imp p ne =
  let open Node p ne dgRv
      node_fires =
        impEqTrans (ap1 wfCellNode opk) (ap1 w_l2 opk) (ap1 wfAdCell opk)
          (fork_false_to_snd_imp htag unaryCell w_l2 (testTag 1) opk
             (natEqSkip_imp htag derTagIdx 5 1 opk (wn 5 1 (\ ())) nieq_imp))
          (impEqTrans (ap1 w_l2 opk) (ap1 w_l3 opk) (ap1 wfAdCell opk)
            (fork_false_to_snd_imp htag wfAdCell w_l3 (testTag 2) opk
               (natEqSkip_imp htag derTagIdx 5 2 opk (wn 5 2 (\ ())) nieq_imp))
            (impEqTrans (ap1 w_l3 opk) (ap1 w_l4 opk) (ap1 wfAdCell opk)
              (fork_false_to_snd_imp htag unaryCell w_l4 (testTag 3) opk
                 (natEqSkip_imp htag derTagIdx 5 3 opk (wn 5 3 (\ ())) nieq_imp))
              (impEqTrans (ap1 w_l4 opk) (ap1 w_l5 opk) (ap1 wfAdCell opk)
                (fork_false_to_snd_imp htag unaryCell w_l5 (testTag 4) opk
                   (natEqSkip_imp htag derTagIdx 5 4 opk (wn 5 4 (\ ())) nieq_imp))
                (fork_true_to_fst_imp htag wfAdCell w_l6 (testTag 5) opk
                   (natEqFire_imp htag derTagIdx 5 opk nieq_imp)))))
  in mkChain p ne negLeaf htag wfAdCell (ap2 pi (ap1 wfRed (pL p)) (ap1 wfRed (pR p))) step2 node_fires (ad_val p ne)

wfRed_op_rRs_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (ap1 Fst (dtag p)) dgRs)
                  (eqF (ap1 wfRed p) (ap2 pi (ap1 wfRed (pL p)) (ap1 wfRed (pR p))))))
wfRed_op_rRs_imp p ne =
  let open Node p ne dgRs
      node_fires =
        impEqTrans (ap1 wfCellNode opk) (ap1 w_l2 opk) (ap1 wfAdCell opk)
          (fork_false_to_snd_imp htag unaryCell w_l2 (testTag 1) opk
             (natEqSkip_imp htag derTagIdx 8 1 opk (wn 8 1 (\ ())) nieq_imp))
          (impEqTrans (ap1 w_l2 opk) (ap1 w_l3 opk) (ap1 wfAdCell opk)
            (fork_false_to_snd_imp htag wfAdCell w_l3 (testTag 2) opk
               (natEqSkip_imp htag derTagIdx 8 2 opk (wn 8 2 (\ ())) nieq_imp))
            (impEqTrans (ap1 w_l3 opk) (ap1 w_l4 opk) (ap1 wfAdCell opk)
              (fork_false_to_snd_imp htag unaryCell w_l4 (testTag 3) opk
                 (natEqSkip_imp htag derTagIdx 8 3 opk (wn 8 3 (\ ())) nieq_imp))
              (impEqTrans (ap1 w_l4 opk) (ap1 w_l5 opk) (ap1 wfAdCell opk)
                (fork_false_to_snd_imp htag unaryCell w_l5 (testTag 4) opk
                   (natEqSkip_imp htag derTagIdx 8 4 opk (wn 8 4 (\ ())) nieq_imp))
                (impEqTrans (ap1 w_l5 opk) (ap1 w_l6 opk) (ap1 wfAdCell opk)
                  (fork_false_to_snd_imp htag wfAdCell w_l6 (testTag 5) opk
                     (natEqSkip_imp htag derTagIdx 8 5 opk (wn 8 5 (\ ())) nieq_imp))
                  (impEqTrans (ap1 w_l6 opk) (ap1 w_l7 opk) (ap1 wfAdCell opk)
                    (fork_false_to_snd_imp htag unaryCell w_l7 (testTag 6) opk
                       (natEqSkip_imp htag derTagIdx 8 6 opk (wn 8 6 (\ ())) nieq_imp))
                    (impEqTrans (ap1 w_l7 opk) (ap1 w_l8 opk) (ap1 wfAdCell opk)
                      (fork_false_to_snd_imp htag unaryCell w_l8 (testTag 7) opk
                         (natEqSkip_imp htag derTagIdx 8 7 opk (wn 8 7 (\ ())) nieq_imp))
                      (fork_true_to_fst_imp htag wfAdCell rejectCell (testTag 8) opk
                         (natEqFire_imp htag derTagIdx 8 opk nieq_imp))))))))
  in mkChain p ne negLeaf htag wfAdCell (ap2 pi (ap1 wfRed (pL p)) (ap1 wfRed (pR p))) step2 node_fires (ad_val p ne)
