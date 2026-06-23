{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.PrTgtUOpaqueImp -- IMP-FORM opaque tgtF equations for the full p.r. calculus
-- (9 tags), the target-endpoint analogue of T4.PrSrcUOpaqueImp (same dispatch
-- skeleton; cell values encode the rule RIGHT-hand sides).
--
-- No holes, no postulates, no termination warnings (only the benign
-- RuleInst3:328 unreachable-clauses warning); --safe --without-K --exact-split.

module T4.PrTgtUOpaqueImp where

open import T4.Base

open import T4.PrDerCode using ( dgReflO ; dgAp1c ; dgAp2c ; dgRo ; dgRu ; dgRv ; dgRC ; dgRb ; dgRs )
open import T4.PrCodeObj using ( tmO ; tmAp1 ; tmAp2 ; cRec )
open import T4.PrDev using ( mkAp1 ; mkAp2 ; mkRec ; tmOF
                           ; mkAp1_val ; mkAp2_val ; mkRec_val ; tmOF_val )
open import T4.PrTgt
  using ( tgtF ; derTagIdx ; derBunIdx ; bunF ; bunG ; bunH1 ; bunH2 ; tgtL ; tgtR
        ; ap1cCell ; ap2cCell ; rOCell ; rUCell ; rVCell ; rCCell ; rRbCell ; rRsCell
        ; tgt_l2 ; tgt_l3 ; tgt_l4 ; tgt_l5 ; tgt_l6 ; tgt_l7 ; cellNodeTgt ; testTag )
open import T4.PrTgtUOpaque using ( funP ; gP ; h1P ; h2P )

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
  tgtStepU : Fun1
  tgtStepU = stepOf tmOF cellNodeTgt
open T4.OpaqueHarness.H tgtStepU

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

  recBun : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 derBunIdx (opkg p)) (funP p))
  recBun p ne = ruleTrans (compose1U_eq Snd nIdx (opkg p)) (cong1 Snd (op_nIdx p ne))
  recG : (p : Term) -> Deriv (neg (eqF p O)) -> Deriv (eqF (ap1 bunG (opkg p)) (gP p))
  recG p ne = ruleTrans (compose1U_eq Fst derBunIdx (opkg p)) (cong1 Fst (recBun p ne))
  recH1 : (p : Term) -> Deriv (neg (eqF p O)) -> Deriv (eqF (ap1 bunH1 (opkg p)) (h1P p))
  recH1 p ne = ruleTrans (compose1U_eq Fst (compose1U Snd derBunIdx) (opkg p))
                 (cong1 Fst (ruleTrans (compose1U_eq Snd derBunIdx (opkg p)) (cong1 Snd (recBun p ne))))
  recH2 : (p : Term) -> Deriv (neg (eqF p O)) -> Deriv (eqF (ap1 bunH2 (opkg p)) (h2P p))
  recH2 p ne = ruleTrans (compose1U_eq Snd (compose1U Snd derBunIdx) (opkg p))
                 (cong1 Snd (ruleTrans (compose1U_eq Snd derBunIdx (opkg p)) (cong1 Snd (recBun p ne))))

  recPL : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 tgtL (opkg p)) (ap1 tgtF (pL p)))
  recPL p ne = lookup_op Z tgtStepU lIdx (ap1 predecessor p) (pL p) (op_pL p ne) (pLValueBound p ne)
  recPR : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 tgtR (opkg p)) (ap1 tgtF (pR p)))
  recPR p ne = lookup_op Z tgtStepU rIdx (ap1 predecessor p) (pR p) (op_pR p ne) (pRValueBound p ne)

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
    step2 : Deriv (imp negLeaf (imp htag (eqF (ap1 tgtStepU opk) (ap1 cellNodeTgt opk))))
    step2 = compI (fork_false_to_snd_imp negLeaf tmOF cellNodeTgt
                     (C natEqF get_tag (constN 1)) opk nl_neg)
                  (axK (eqF (ap1 tgtStepU opk) (ap1 cellNodeTgt opk)) htag)
    derTag_bare : Deriv (eqF (ap1 derTagIdx opk) (ap1 Fst (dtag p)))
    derTag_bare = ruleTrans (compose1U_eq Fst nIdx opk) (cong1 Fst (op_nIdx p ne))
    nieq_imp : Deriv (imp htag (eqF (ap1 derTagIdx opk) lbl))
    nieq_imp = impEqTrans (ap1 derTagIdx opk) (ap1 Fst (dtag p)) lbl
                 (impLift derTag_bare) (identP htag)

  mkChain : (p : Term) (ne : Deriv (neg (eqF p O))) (negLeaf htag : Formula) (cell : Fun1) (rhs : Term) ->
    Deriv (imp negLeaf (imp htag (eqF (ap1 tgtStepU (opkg p)) (ap1 cellNodeTgt (opkg p))))) ->
    Deriv (imp htag (eqF (ap1 cellNodeTgt (opkg p)) (ap1 cell (opkg p)))) ->
    Deriv (eqF (ap1 cell (opkg p)) rhs) ->
    Deriv (imp negLeaf (imp htag (eqF (ap1 tgtF p) rhs)))
  mkChain p ne negLeaf htag cell rhs step2 node_fires cell_val =
    let opk = opkg p
    in trans2c (ap1 tgtF p) (ap1 tgtStepU opk) rhs
         (lift2 negLeaf htag (opUnfold p ne))
         (trans2c (ap1 tgtStepU opk) (ap1 cellNodeTgt opk) rhs step2
           (trans2c (ap1 cellNodeTgt opk) (ap1 cell opk) rhs
             (liftP negLeaf node_fires) (lift2 negLeaf htag cell_val)))

------------------------------------------------------------------------
-- SECTION 2.  Leaf.

tgtF_op_reflO_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (eqF (ap1 Fst p) (natCode 1)) (eqF (ap1 tgtF p) tmO))
tgtF_op_reflO_imp p ne =
  let opk = opkg p
      Hleaf : Formula
      Hleaf = eqF (ap1 Fst p) (natCode 1)
      gtag : Deriv (imp Hleaf (eqF (ap1 get_tag opk) (natCode 1)))
      gtag = impEqTrans (ap1 get_tag opk) (ap1 Fst p) (natCode 1)
               (impLift (op_tag p ne)) (identP Hleaf)
      cell_fires : Deriv (imp Hleaf (eqF (ap1 tgtStepU opk) (ap1 tmOF opk)))
      cell_fires = fork_true_to_fst_imp Hleaf tmOF cellNodeTgt (C natEqF get_tag (constN 1)) opk
                     (natEqFire_imp Hleaf get_tag 1 opk gtag)
  in impEqTrans (ap1 tgtF p) (ap1 tgtStepU opk) tmO
       (impLift (opUnfold p ne))
       (impEqTrans (ap1 tgtStepU opk) (ap1 tmOF opk) tmO cell_fires (impLift (tmOF_val opk)))

------------------------------------------------------------------------
-- SECTION 3.  Congruences ap1c / ap2c.

tgtF_op_ap1c_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (ap1 Fst (dtag p)) dgAp1c) (eqF (ap1 tgtF p) (tmAp1 (funP p) (ap1 tgtF (pL p))))))
tgtF_op_ap1c_imp p ne =
  let open Node p ne dgAp1c
      node_fires = fork_true_to_fst_imp htag ap1cCell tgt_l2 (testTag 1) opk
                     (natEqFire_imp htag derTagIdx 1 opk nieq_imp)
      cell_val = mkAp1_val bunF tgtL opk (funP p) (ap1 tgtF (pL p)) (recBun p ne) (recPL p ne)
  in mkChain p ne negLeaf htag ap1cCell (tmAp1 (funP p) (ap1 tgtF (pL p))) step2 node_fires cell_val

tgtF_op_ap2c_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (ap1 Fst (dtag p)) dgAp2c)
                  (eqF (ap1 tgtF p) (tmAp2 (funP p) (ap1 tgtF (pL p)) (ap1 tgtF (pR p))))))
tgtF_op_ap2c_imp p ne =
  let open Node p ne dgAp2c
      node_fires =
        impEqTrans (ap1 cellNodeTgt opk) (ap1 tgt_l2 opk) (ap1 ap2cCell opk)
          (fork_false_to_snd_imp htag ap1cCell tgt_l2 (testTag 1) opk
             (natEqSkip_imp htag derTagIdx 2 1 opk (wn 2 1 (\ ())) nieq_imp))
          (fork_true_to_fst_imp htag ap2cCell tgt_l3 (testTag 2) opk
             (natEqFire_imp htag derTagIdx 2 opk nieq_imp))
      cell_val = mkAp2_val bunF tgtL tgtR opk (funP p) (ap1 tgtF (pL p)) (ap1 tgtF (pR p))
                   (recBun p ne) (recPL p ne) (recPR p ne)
  in mkChain p ne negLeaf htag ap2cCell (tmAp2 (funP p) (ap1 tgtF (pL p)) (ap1 tgtF (pR p))) step2 node_fires cell_val

------------------------------------------------------------------------
-- SECTION 4.  o / u / v redexes.

tgtF_op_rO_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (ap1 Fst (dtag p)) dgRo) (eqF (ap1 tgtF p) tmO)))
tgtF_op_rO_imp p ne =
  let open Node p ne dgRo
      node_fires =
        impEqTrans (ap1 cellNodeTgt opk) (ap1 tgt_l2 opk) (ap1 rOCell opk)
          (fork_false_to_snd_imp htag ap1cCell tgt_l2 (testTag 1) opk
             (natEqSkip_imp htag derTagIdx 3 1 opk (wn 3 1 (\ ())) nieq_imp))
          (impEqTrans (ap1 tgt_l2 opk) (ap1 tgt_l3 opk) (ap1 rOCell opk)
            (fork_false_to_snd_imp htag ap2cCell tgt_l3 (testTag 2) opk
               (natEqSkip_imp htag derTagIdx 3 2 opk (wn 3 2 (\ ())) nieq_imp))
            (fork_true_to_fst_imp htag rOCell tgt_l4 (testTag 3) opk
               (natEqFire_imp htag derTagIdx 3 opk nieq_imp)))
      cell_val = tmOF_val opk
  in mkChain p ne negLeaf htag rOCell tmO step2 node_fires cell_val

tgtF_op_rU_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (ap1 Fst (dtag p)) dgRu) (eqF (ap1 tgtF p) (ap1 tgtF (pL p)))))
tgtF_op_rU_imp p ne =
  let open Node p ne dgRu
      node_fires =
        impEqTrans (ap1 cellNodeTgt opk) (ap1 tgt_l2 opk) (ap1 rUCell opk)
          (fork_false_to_snd_imp htag ap1cCell tgt_l2 (testTag 1) opk
             (natEqSkip_imp htag derTagIdx 4 1 opk (wn 4 1 (\ ())) nieq_imp))
          (impEqTrans (ap1 tgt_l2 opk) (ap1 tgt_l3 opk) (ap1 rUCell opk)
            (fork_false_to_snd_imp htag ap2cCell tgt_l3 (testTag 2) opk
               (natEqSkip_imp htag derTagIdx 4 2 opk (wn 4 2 (\ ())) nieq_imp))
            (impEqTrans (ap1 tgt_l3 opk) (ap1 tgt_l4 opk) (ap1 rUCell opk)
              (fork_false_to_snd_imp htag rOCell tgt_l4 (testTag 3) opk
                 (natEqSkip_imp htag derTagIdx 4 3 opk (wn 4 3 (\ ())) nieq_imp))
              (fork_true_to_fst_imp htag rUCell tgt_l5 (testTag 4) opk
                 (natEqFire_imp htag derTagIdx 4 opk nieq_imp))))
      cell_val = recPL p ne
  in mkChain p ne negLeaf htag rUCell (ap1 tgtF (pL p)) step2 node_fires cell_val

tgtF_op_rV_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (ap1 Fst (dtag p)) dgRv) (eqF (ap1 tgtF p) (ap1 tgtF (pR p)))))
tgtF_op_rV_imp p ne =
  let open Node p ne dgRv
      node_fires =
        impEqTrans (ap1 cellNodeTgt opk) (ap1 tgt_l2 opk) (ap1 rVCell opk)
          (fork_false_to_snd_imp htag ap1cCell tgt_l2 (testTag 1) opk
             (natEqSkip_imp htag derTagIdx 5 1 opk (wn 5 1 (\ ())) nieq_imp))
          (impEqTrans (ap1 tgt_l2 opk) (ap1 tgt_l3 opk) (ap1 rVCell opk)
            (fork_false_to_snd_imp htag ap2cCell tgt_l3 (testTag 2) opk
               (natEqSkip_imp htag derTagIdx 5 2 opk (wn 5 2 (\ ())) nieq_imp))
            (impEqTrans (ap1 tgt_l3 opk) (ap1 tgt_l4 opk) (ap1 rVCell opk)
              (fork_false_to_snd_imp htag rOCell tgt_l4 (testTag 3) opk
                 (natEqSkip_imp htag derTagIdx 5 3 opk (wn 5 3 (\ ())) nieq_imp))
              (impEqTrans (ap1 tgt_l4 opk) (ap1 tgt_l5 opk) (ap1 rVCell opk)
                (fork_false_to_snd_imp htag rUCell tgt_l5 (testTag 4) opk
                   (natEqSkip_imp htag derTagIdx 5 4 opk (wn 5 4 (\ ())) nieq_imp))
                (fork_true_to_fst_imp htag rVCell tgt_l6 (testTag 5) opk
                   (natEqFire_imp htag derTagIdx 5 opk nieq_imp)))))
      cell_val = recPR p ne
  in mkChain p ne negLeaf htag rVCell (ap1 tgtF (pR p)) step2 node_fires cell_val

------------------------------------------------------------------------
-- SECTION 5.  C / Rb / Rs redexes.

tgtF_op_rC_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (ap1 Fst (dtag p)) dgRC)
                  (eqF (ap1 tgtF p)
                       (tmAp2 (gP p) (tmAp1 (h1P p) (ap1 tgtF (pL p))) (tmAp1 (h2P p) (ap1 tgtF (pL p)))))))
tgtF_op_rC_imp p ne =
  let open Node p ne dgRC
      node_fires =
        impEqTrans (ap1 cellNodeTgt opk) (ap1 tgt_l2 opk) (ap1 rCCell opk)
          (fork_false_to_snd_imp htag ap1cCell tgt_l2 (testTag 1) opk
             (natEqSkip_imp htag derTagIdx 6 1 opk (wn 6 1 (\ ())) nieq_imp))
          (impEqTrans (ap1 tgt_l2 opk) (ap1 tgt_l3 opk) (ap1 rCCell opk)
            (fork_false_to_snd_imp htag ap2cCell tgt_l3 (testTag 2) opk
               (natEqSkip_imp htag derTagIdx 6 2 opk (wn 6 2 (\ ())) nieq_imp))
            (impEqTrans (ap1 tgt_l3 opk) (ap1 tgt_l4 opk) (ap1 rCCell opk)
              (fork_false_to_snd_imp htag rOCell tgt_l4 (testTag 3) opk
                 (natEqSkip_imp htag derTagIdx 6 3 opk (wn 6 3 (\ ())) nieq_imp))
              (impEqTrans (ap1 tgt_l4 opk) (ap1 tgt_l5 opk) (ap1 rCCell opk)
                (fork_false_to_snd_imp htag rUCell tgt_l5 (testTag 4) opk
                   (natEqSkip_imp htag derTagIdx 6 4 opk (wn 6 4 (\ ())) nieq_imp))
                (impEqTrans (ap1 tgt_l5 opk) (ap1 tgt_l6 opk) (ap1 rCCell opk)
                  (fork_false_to_snd_imp htag rVCell tgt_l6 (testTag 5) opk
                     (natEqSkip_imp htag derTagIdx 6 5 opk (wn 6 5 (\ ())) nieq_imp))
                  (fork_true_to_fst_imp htag rCCell tgt_l7 (testTag 6) opk
                     (natEqFire_imp htag derTagIdx 6 opk nieq_imp))))))
      armH1 = mkAp1_val bunH1 tgtL opk (h1P p) (ap1 tgtF (pL p)) (recH1 p ne) (recPL p ne)
      armH2 = mkAp1_val bunH2 tgtL opk (h2P p) (ap1 tgtF (pL p)) (recH2 p ne) (recPL p ne)
      cell_val = mkAp2_val bunG (mkAp1 bunH1 tgtL) (mkAp1 bunH2 tgtL) opk
                   (gP p) (tmAp1 (h1P p) (ap1 tgtF (pL p))) (tmAp1 (h2P p) (ap1 tgtF (pL p))) (recG p ne) armH1 armH2
  in mkChain p ne negLeaf htag rCCell
       (tmAp2 (gP p) (tmAp1 (h1P p) (ap1 tgtF (pL p))) (tmAp1 (h2P p) (ap1 tgtF (pL p)))) step2 node_fires cell_val

tgtF_op_rRb_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (ap1 Fst (dtag p)) dgRb) (eqF (ap1 tgtF p) (tmAp1 (gP p) (ap1 tgtF (pL p))))))
tgtF_op_rRb_imp p ne =
  let open Node p ne dgRb
      node_fires =
        impEqTrans (ap1 cellNodeTgt opk) (ap1 tgt_l2 opk) (ap1 rRbCell opk)
          (fork_false_to_snd_imp htag ap1cCell tgt_l2 (testTag 1) opk
             (natEqSkip_imp htag derTagIdx 7 1 opk (wn 7 1 (\ ())) nieq_imp))
          (impEqTrans (ap1 tgt_l2 opk) (ap1 tgt_l3 opk) (ap1 rRbCell opk)
            (fork_false_to_snd_imp htag ap2cCell tgt_l3 (testTag 2) opk
               (natEqSkip_imp htag derTagIdx 7 2 opk (wn 7 2 (\ ())) nieq_imp))
            (impEqTrans (ap1 tgt_l3 opk) (ap1 tgt_l4 opk) (ap1 rRbCell opk)
              (fork_false_to_snd_imp htag rOCell tgt_l4 (testTag 3) opk
                 (natEqSkip_imp htag derTagIdx 7 3 opk (wn 7 3 (\ ())) nieq_imp))
              (impEqTrans (ap1 tgt_l4 opk) (ap1 tgt_l5 opk) (ap1 rRbCell opk)
                (fork_false_to_snd_imp htag rUCell tgt_l5 (testTag 4) opk
                   (natEqSkip_imp htag derTagIdx 7 4 opk (wn 7 4 (\ ())) nieq_imp))
                (impEqTrans (ap1 tgt_l5 opk) (ap1 tgt_l6 opk) (ap1 rRbCell opk)
                  (fork_false_to_snd_imp htag rVCell tgt_l6 (testTag 5) opk
                     (natEqSkip_imp htag derTagIdx 7 5 opk (wn 7 5 (\ ())) nieq_imp))
                  (impEqTrans (ap1 tgt_l6 opk) (ap1 tgt_l7 opk) (ap1 rRbCell opk)
                    (fork_false_to_snd_imp htag rCCell tgt_l7 (testTag 6) opk
                       (natEqSkip_imp htag derTagIdx 7 6 opk (wn 7 6 (\ ())) nieq_imp))
                    (fork_true_to_fst_imp htag rRbCell rRsCell (testTag 7) opk
                       (natEqFire_imp htag derTagIdx 7 opk nieq_imp)))))))
      cell_val = mkAp1_val bunG tgtL opk (gP p) (ap1 tgtF (pL p)) (recG p ne) (recPL p ne)
  in mkChain p ne negLeaf htag rRbCell (tmAp1 (gP p) (ap1 tgtF (pL p))) step2 node_fires cell_val

tgtF_op_rRs_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (ap1 Fst (dtag p)) dgRs)
                  (eqF (ap1 tgtF p)
                       (tmAp2 (h1P p) (tmAp2 (h2P p) (ap1 tgtF (pL p)) (ap1 tgtF (pR p)))
                                      (tmAp2 (cRec (gP p) (h1P p) (h2P p)) (ap1 tgtF (pL p)) (ap1 tgtF (pR p)))))))
tgtF_op_rRs_imp p ne =
  let open Node p ne dgRs
      node_fires =
        impEqTrans (ap1 cellNodeTgt opk) (ap1 tgt_l2 opk) (ap1 rRsCell opk)
          (fork_false_to_snd_imp htag ap1cCell tgt_l2 (testTag 1) opk
             (natEqSkip_imp htag derTagIdx 8 1 opk (wn 8 1 (\ ())) nieq_imp))
          (impEqTrans (ap1 tgt_l2 opk) (ap1 tgt_l3 opk) (ap1 rRsCell opk)
            (fork_false_to_snd_imp htag ap2cCell tgt_l3 (testTag 2) opk
               (natEqSkip_imp htag derTagIdx 8 2 opk (wn 8 2 (\ ())) nieq_imp))
            (impEqTrans (ap1 tgt_l3 opk) (ap1 tgt_l4 opk) (ap1 rRsCell opk)
              (fork_false_to_snd_imp htag rOCell tgt_l4 (testTag 3) opk
                 (natEqSkip_imp htag derTagIdx 8 3 opk (wn 8 3 (\ ())) nieq_imp))
              (impEqTrans (ap1 tgt_l4 opk) (ap1 tgt_l5 opk) (ap1 rRsCell opk)
                (fork_false_to_snd_imp htag rUCell tgt_l5 (testTag 4) opk
                   (natEqSkip_imp htag derTagIdx 8 4 opk (wn 8 4 (\ ())) nieq_imp))
                (impEqTrans (ap1 tgt_l5 opk) (ap1 tgt_l6 opk) (ap1 rRsCell opk)
                  (fork_false_to_snd_imp htag rVCell tgt_l6 (testTag 5) opk
                     (natEqSkip_imp htag derTagIdx 8 5 opk (wn 8 5 (\ ())) nieq_imp))
                  (impEqTrans (ap1 tgt_l6 opk) (ap1 tgt_l7 opk) (ap1 rRsCell opk)
                    (fork_false_to_snd_imp htag rCCell tgt_l7 (testTag 6) opk
                       (natEqSkip_imp htag derTagIdx 8 6 opk (wn 8 6 (\ ())) nieq_imp))
                    (fork_false_to_snd_imp htag rRbCell rRsCell (testTag 7) opk
                       (natEqSkip_imp htag derTagIdx 8 7 opk (wn 8 7 (\ ())) nieq_imp)))))))
      arm2 = mkAp2_val bunH2 tgtL tgtR opk (h2P p) (ap1 tgtF (pL p)) (ap1 tgtF (pR p)) (recH2 p ne) (recPL p ne) (recPR p ne)
      recFun = mkRec_val bunG bunH1 bunH2 opk (gP p) (h1P p) (h2P p) (recG p ne) (recH1 p ne) (recH2 p ne)
      arm3 = mkAp2_val (mkRec bunG bunH1 bunH2) tgtL tgtR opk (cRec (gP p) (h1P p) (h2P p)) (ap1 tgtF (pL p)) (ap1 tgtF (pR p)) recFun (recPL p ne) (recPR p ne)
      cell_val = mkAp2_val bunH1 (mkAp2 bunH2 tgtL tgtR) (mkAp2 (mkRec bunG bunH1 bunH2) tgtL tgtR) opk
                   (h1P p) (tmAp2 (h2P p) (ap1 tgtF (pL p)) (ap1 tgtF (pR p)))
                   (tmAp2 (cRec (gP p) (h1P p) (h2P p)) (ap1 tgtF (pL p)) (ap1 tgtF (pR p))) (recH1 p ne) arm2 arm3
  in mkChain p ne negLeaf htag rRsCell
       (tmAp2 (h1P p) (tmAp2 (h2P p) (ap1 tgtF (pL p)) (ap1 tgtF (pR p)))
                      (tmAp2 (cRec (gP p) (h1P p) (h2P p)) (ap1 tgtF (pL p)) (ap1 tgtF (pR p)))) step2 node_fires cell_val
