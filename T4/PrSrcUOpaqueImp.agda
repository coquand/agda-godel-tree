{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.PrSrcUOpaqueImp -- IMP-FORM opaque srcF equations for the full p.r. calculus
-- (9 tags), carried under [negLeaf, htag] (nodes) / Hleaf (leaf) for the tag
-- dispatch.  srcF is flat (dispatch only on Fst(dtag p)); every case follows the
-- toy T4.DerSrcUOpaqueImp pattern (Node module + node_fires cascade + bare cell
-- value lifted via lift2, chained with trans2c).
--
-- No holes, no postulates, no termination warnings (only the benign
-- RuleInst3:328 unreachable-clauses warning); --safe --without-K --exact-split.

module T4.PrSrcUOpaqueImp where

open import T4.Base

open import T4.PrDerCode using ( dgReflO ; dgAp1c ; dgAp2c ; dgRo ; dgRu ; dgRv ; dgRC ; dgRb ; dgRs )
open import T4.PrCodeObj using ( tmO ; tmAp1 ; tmAp2 ; cSuc ; cZero ; cId ; cComp ; cProj ; cRec )
open import T4.PrDev using ( mkAp1 ; mkAp2 ; mkRec ; tmOF ; cSucF
                           ; mkAp1_val ; mkAp2_val ; mkRec_val ; tmOF_val ; cSucF_val )
open import T4.PrSrc
  using ( srcF ; cZeroF ; cIdF ; cProjF ; mkComp
        ; cZeroF_val ; cIdF_val ; cProjF_val ; mkComp_val
        ; derTagIdx ; derBunIdx ; bunF ; bunG ; bunH1 ; bunH2 ; srcL ; srcR
        ; ap1cCell ; ap2cCell ; rOCell ; rUCell ; rVCell ; rCCell ; rRbCell ; rRsCell
        ; src_l2 ; src_l3 ; src_l4 ; src_l5 ; src_l6 ; src_l7 ; cellNodeSrc ; testTag )
open import T4.PrSrcUOpaque using ( funP ; gP ; h1P ; h2P )

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
  srcStepU : Fun1
  srcStepU = stepOf tmOF cellNodeSrc
open T4.OpaqueHarness.H srcStepU

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
    Deriv (eqF (ap1 srcL (opkg p)) (ap1 srcF (pL p)))
  recPL p ne = lookup_op Z srcStepU lIdx (ap1 predecessor p) (pL p) (op_pL p ne) (pLValueBound p ne)
  recPR : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 srcR (opkg p)) (ap1 srcF (pR p)))
  recPR p ne = lookup_op Z srcStepU rIdx (ap1 predecessor p) (pR p) (op_pR p ne) (pRValueBound p ne)

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
    step2 : Deriv (imp negLeaf (imp htag (eqF (ap1 srcStepU opk) (ap1 cellNodeSrc opk))))
    step2 = compI (fork_false_to_snd_imp negLeaf tmOF cellNodeSrc
                     (C natEqF get_tag (constN 1)) opk nl_neg)
                  (axK (eqF (ap1 srcStepU opk) (ap1 cellNodeSrc opk)) htag)
    derTag_bare : Deriv (eqF (ap1 derTagIdx opk) (ap1 Fst (dtag p)))
    derTag_bare = ruleTrans (compose1U_eq Fst nIdx opk) (cong1 Fst (op_nIdx p ne))
    nieq_imp : Deriv (imp htag (eqF (ap1 derTagIdx opk) lbl))
    nieq_imp = impEqTrans (ap1 derTagIdx opk) (ap1 Fst (dtag p)) lbl
                 (impLift derTag_bare) (identP htag)

  -- generic node assembler (fully parameterized to avoid re-opening Node in the type).
  mkChain : (p : Term) (ne : Deriv (neg (eqF p O))) (negLeaf htag : Formula) (cell : Fun1) (rhs : Term) ->
    Deriv (imp negLeaf (imp htag (eqF (ap1 srcStepU (opkg p)) (ap1 cellNodeSrc (opkg p))))) ->
    Deriv (imp htag (eqF (ap1 cellNodeSrc (opkg p)) (ap1 cell (opkg p)))) ->
    Deriv (eqF (ap1 cell (opkg p)) rhs) ->
    Deriv (imp negLeaf (imp htag (eqF (ap1 srcF p) rhs)))
  mkChain p ne negLeaf htag cell rhs step2 node_fires cell_val =
    let opk = opkg p
    in trans2c (ap1 srcF p) (ap1 srcStepU opk) rhs
         (lift2 negLeaf htag (opUnfold p ne))
         (trans2c (ap1 srcStepU opk) (ap1 cellNodeSrc opk) rhs step2
           (trans2c (ap1 cellNodeSrc opk) (ap1 cell opk) rhs
             (liftP negLeaf node_fires) (lift2 negLeaf htag cell_val)))

------------------------------------------------------------------------
-- SECTION 2.  Leaf.

srcF_op_reflO_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (eqF (ap1 Fst p) (natCode 1)) (eqF (ap1 srcF p) tmO))
srcF_op_reflO_imp p ne =
  let opk = opkg p
      Hleaf : Formula
      Hleaf = eqF (ap1 Fst p) (natCode 1)
      gtag : Deriv (imp Hleaf (eqF (ap1 get_tag opk) (natCode 1)))
      gtag = impEqTrans (ap1 get_tag opk) (ap1 Fst p) (natCode 1)
               (impLift (op_tag p ne)) (identP Hleaf)
      cell_fires : Deriv (imp Hleaf (eqF (ap1 srcStepU opk) (ap1 tmOF opk)))
      cell_fires = fork_true_to_fst_imp Hleaf tmOF cellNodeSrc (C natEqF get_tag (constN 1)) opk
                     (natEqFire_imp Hleaf get_tag 1 opk gtag)
  in impEqTrans (ap1 srcF p) (ap1 srcStepU opk) tmO
       (impLift (opUnfold p ne))
       (impEqTrans (ap1 srcStepU opk) (ap1 tmOF opk) tmO cell_fires (impLift (tmOF_val opk)))

------------------------------------------------------------------------
-- SECTION 3.  Congruences ap1c / ap2c.

srcF_op_ap1c_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (ap1 Fst (dtag p)) dgAp1c) (eqF (ap1 srcF p) (tmAp1 (funP p) (ap1 srcF (pL p))))))
srcF_op_ap1c_imp p ne =
  let open Node p ne dgAp1c
      node_fires = fork_true_to_fst_imp htag ap1cCell src_l2 (testTag 1) opk
                     (natEqFire_imp htag derTagIdx 1 opk nieq_imp)
      cell_val = mkAp1_val bunF srcL opk (funP p) (ap1 srcF (pL p)) (recBun p ne) (recPL p ne)
  in mkChain p ne negLeaf htag ap1cCell ((tmAp1 (funP p) (ap1 srcF (pL p)))) step2 node_fires cell_val

srcF_op_ap2c_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (ap1 Fst (dtag p)) dgAp2c)
                  (eqF (ap1 srcF p) (tmAp2 (funP p) (ap1 srcF (pL p)) (ap1 srcF (pR p))))))
srcF_op_ap2c_imp p ne =
  let open Node p ne dgAp2c
      node_fires =
        impEqTrans (ap1 cellNodeSrc opk) (ap1 src_l2 opk) (ap1 ap2cCell opk)
          (fork_false_to_snd_imp htag ap1cCell src_l2 (testTag 1) opk
             (natEqSkip_imp htag derTagIdx 2 1 opk (wn 2 1 (\ ())) nieq_imp))
          (fork_true_to_fst_imp htag ap2cCell src_l3 (testTag 2) opk
             (natEqFire_imp htag derTagIdx 2 opk nieq_imp))
      cell_val = mkAp2_val bunF srcL srcR opk (funP p) (ap1 srcF (pL p)) (ap1 srcF (pR p))
                   (recBun p ne) (recPL p ne) (recPR p ne)
  in mkChain p ne negLeaf htag ap2cCell ((tmAp2 (funP p) (ap1 srcF (pL p)) (ap1 srcF (pR p)))) step2 node_fires cell_val

------------------------------------------------------------------------
-- SECTION 4.  o / u / v redexes.

srcF_op_rO_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (ap1 Fst (dtag p)) dgRo) (eqF (ap1 srcF p) (tmAp1 cZero (ap1 srcF (pL p))))))
srcF_op_rO_imp p ne =
  let open Node p ne dgRo
      node_fires =
        impEqTrans (ap1 cellNodeSrc opk) (ap1 src_l2 opk) (ap1 rOCell opk)
          (fork_false_to_snd_imp htag ap1cCell src_l2 (testTag 1) opk
             (natEqSkip_imp htag derTagIdx 3 1 opk (wn 3 1 (\ ())) nieq_imp))
          (impEqTrans (ap1 src_l2 opk) (ap1 src_l3 opk) (ap1 rOCell opk)
            (fork_false_to_snd_imp htag ap2cCell src_l3 (testTag 2) opk
               (natEqSkip_imp htag derTagIdx 3 2 opk (wn 3 2 (\ ())) nieq_imp))
            (fork_true_to_fst_imp htag rOCell src_l4 (testTag 3) opk
               (natEqFire_imp htag derTagIdx 3 opk nieq_imp)))
      cell_val = mkAp1_val cZeroF srcL opk cZero (ap1 srcF (pL p)) (cZeroF_val opk) (recPL p ne)
  in mkChain p ne negLeaf htag rOCell ((tmAp1 cZero (ap1 srcF (pL p)))) step2 node_fires cell_val

srcF_op_rU_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (ap1 Fst (dtag p)) dgRu) (eqF (ap1 srcF p) (tmAp1 cId (ap1 srcF (pL p))))))
srcF_op_rU_imp p ne =
  let open Node p ne dgRu
      node_fires =
        impEqTrans (ap1 cellNodeSrc opk) (ap1 src_l2 opk) (ap1 rUCell opk)
          (fork_false_to_snd_imp htag ap1cCell src_l2 (testTag 1) opk
             (natEqSkip_imp htag derTagIdx 4 1 opk (wn 4 1 (\ ())) nieq_imp))
          (impEqTrans (ap1 src_l2 opk) (ap1 src_l3 opk) (ap1 rUCell opk)
            (fork_false_to_snd_imp htag ap2cCell src_l3 (testTag 2) opk
               (natEqSkip_imp htag derTagIdx 4 2 opk (wn 4 2 (\ ())) nieq_imp))
            (impEqTrans (ap1 src_l3 opk) (ap1 src_l4 opk) (ap1 rUCell opk)
              (fork_false_to_snd_imp htag rOCell src_l4 (testTag 3) opk
                 (natEqSkip_imp htag derTagIdx 4 3 opk (wn 4 3 (\ ())) nieq_imp))
              (fork_true_to_fst_imp htag rUCell src_l5 (testTag 4) opk
                 (natEqFire_imp htag derTagIdx 4 opk nieq_imp))))
      cell_val = mkAp1_val cIdF srcL opk cId (ap1 srcF (pL p)) (cIdF_val opk) (recPL p ne)
  in mkChain p ne negLeaf htag rUCell ((tmAp1 cId (ap1 srcF (pL p)))) step2 node_fires cell_val

srcF_op_rV_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (ap1 Fst (dtag p)) dgRv)
                  (eqF (ap1 srcF p) (tmAp2 cProj (ap1 srcF (pL p)) (ap1 srcF (pR p))))))
srcF_op_rV_imp p ne =
  let open Node p ne dgRv
      node_fires =
        impEqTrans (ap1 cellNodeSrc opk) (ap1 src_l2 opk) (ap1 rVCell opk)
          (fork_false_to_snd_imp htag ap1cCell src_l2 (testTag 1) opk
             (natEqSkip_imp htag derTagIdx 5 1 opk (wn 5 1 (\ ())) nieq_imp))
          (impEqTrans (ap1 src_l2 opk) (ap1 src_l3 opk) (ap1 rVCell opk)
            (fork_false_to_snd_imp htag ap2cCell src_l3 (testTag 2) opk
               (natEqSkip_imp htag derTagIdx 5 2 opk (wn 5 2 (\ ())) nieq_imp))
            (impEqTrans (ap1 src_l3 opk) (ap1 src_l4 opk) (ap1 rVCell opk)
              (fork_false_to_snd_imp htag rOCell src_l4 (testTag 3) opk
                 (natEqSkip_imp htag derTagIdx 5 3 opk (wn 5 3 (\ ())) nieq_imp))
              (impEqTrans (ap1 src_l4 opk) (ap1 src_l5 opk) (ap1 rVCell opk)
                (fork_false_to_snd_imp htag rUCell src_l5 (testTag 4) opk
                   (natEqSkip_imp htag derTagIdx 5 4 opk (wn 5 4 (\ ())) nieq_imp))
                (fork_true_to_fst_imp htag rVCell src_l6 (testTag 5) opk
                   (natEqFire_imp htag derTagIdx 5 opk nieq_imp)))))
      cell_val = mkAp2_val cProjF srcL srcR opk cProj (ap1 srcF (pL p)) (ap1 srcF (pR p))
                   (cProjF_val opk) (recPL p ne) (recPR p ne)
  in mkChain p ne negLeaf htag rVCell ((tmAp2 cProj (ap1 srcF (pL p)) (ap1 srcF (pR p)))) step2 node_fires cell_val

------------------------------------------------------------------------
-- SECTION 5.  C / Rb / Rs redexes (carried funs gP/h1P/h2P).

srcF_op_rC_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (ap1 Fst (dtag p)) dgRC)
                  (eqF (ap1 srcF p) (tmAp1 (cComp (gP p) (h1P p) (h2P p)) (ap1 srcF (pL p))))))
srcF_op_rC_imp p ne =
  let open Node p ne dgRC
      node_fires =
        impEqTrans (ap1 cellNodeSrc opk) (ap1 src_l2 opk) (ap1 rCCell opk)
          (fork_false_to_snd_imp htag ap1cCell src_l2 (testTag 1) opk
             (natEqSkip_imp htag derTagIdx 6 1 opk (wn 6 1 (\ ())) nieq_imp))
          (impEqTrans (ap1 src_l2 opk) (ap1 src_l3 opk) (ap1 rCCell opk)
            (fork_false_to_snd_imp htag ap2cCell src_l3 (testTag 2) opk
               (natEqSkip_imp htag derTagIdx 6 2 opk (wn 6 2 (\ ())) nieq_imp))
            (impEqTrans (ap1 src_l3 opk) (ap1 src_l4 opk) (ap1 rCCell opk)
              (fork_false_to_snd_imp htag rOCell src_l4 (testTag 3) opk
                 (natEqSkip_imp htag derTagIdx 6 3 opk (wn 6 3 (\ ())) nieq_imp))
              (impEqTrans (ap1 src_l4 opk) (ap1 src_l5 opk) (ap1 rCCell opk)
                (fork_false_to_snd_imp htag rUCell src_l5 (testTag 4) opk
                   (natEqSkip_imp htag derTagIdx 6 4 opk (wn 6 4 (\ ())) nieq_imp))
                (impEqTrans (ap1 src_l5 opk) (ap1 src_l6 opk) (ap1 rCCell opk)
                  (fork_false_to_snd_imp htag rVCell src_l6 (testTag 5) opk
                     (natEqSkip_imp htag derTagIdx 6 5 opk (wn 6 5 (\ ())) nieq_imp))
                  (fork_true_to_fst_imp htag rCCell src_l7 (testTag 6) opk
                     (natEqFire_imp htag derTagIdx 6 opk nieq_imp))))))
      cell_val = mkAp1_val (mkComp bunG bunH1 bunH2) srcL opk
                   (cComp (gP p) (h1P p) (h2P p)) (ap1 srcF (pL p))
                   (mkComp_val bunG bunH1 bunH2 opk (gP p) (h1P p) (h2P p) (recG p ne) (recH1 p ne) (recH2 p ne))
                   (recPL p ne)
  in mkChain p ne negLeaf htag rCCell ((tmAp1 (cComp (gP p) (h1P p) (h2P p)) (ap1 srcF (pL p)))) step2 node_fires cell_val

srcF_op_rRb_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (ap1 Fst (dtag p)) dgRb)
                  (eqF (ap1 srcF p) (tmAp2 (cRec (gP p) (h1P p) (h2P p)) (ap1 srcF (pL p)) tmO))))
srcF_op_rRb_imp p ne =
  let open Node p ne dgRb
      node_fires =
        impEqTrans (ap1 cellNodeSrc opk) (ap1 src_l2 opk) (ap1 rRbCell opk)
          (fork_false_to_snd_imp htag ap1cCell src_l2 (testTag 1) opk
             (natEqSkip_imp htag derTagIdx 7 1 opk (wn 7 1 (\ ())) nieq_imp))
          (impEqTrans (ap1 src_l2 opk) (ap1 src_l3 opk) (ap1 rRbCell opk)
            (fork_false_to_snd_imp htag ap2cCell src_l3 (testTag 2) opk
               (natEqSkip_imp htag derTagIdx 7 2 opk (wn 7 2 (\ ())) nieq_imp))
            (impEqTrans (ap1 src_l3 opk) (ap1 src_l4 opk) (ap1 rRbCell opk)
              (fork_false_to_snd_imp htag rOCell src_l4 (testTag 3) opk
                 (natEqSkip_imp htag derTagIdx 7 3 opk (wn 7 3 (\ ())) nieq_imp))
              (impEqTrans (ap1 src_l4 opk) (ap1 src_l5 opk) (ap1 rRbCell opk)
                (fork_false_to_snd_imp htag rUCell src_l5 (testTag 4) opk
                   (natEqSkip_imp htag derTagIdx 7 4 opk (wn 7 4 (\ ())) nieq_imp))
                (impEqTrans (ap1 src_l5 opk) (ap1 src_l6 opk) (ap1 rRbCell opk)
                  (fork_false_to_snd_imp htag rVCell src_l6 (testTag 5) opk
                     (natEqSkip_imp htag derTagIdx 7 5 opk (wn 7 5 (\ ())) nieq_imp))
                  (impEqTrans (ap1 src_l6 opk) (ap1 src_l7 opk) (ap1 rRbCell opk)
                    (fork_false_to_snd_imp htag rCCell src_l7 (testTag 6) opk
                       (natEqSkip_imp htag derTagIdx 7 6 opk (wn 7 6 (\ ())) nieq_imp))
                    (fork_true_to_fst_imp htag rRbCell rRsCell (testTag 7) opk
                       (natEqFire_imp htag derTagIdx 7 opk nieq_imp)))))))
      cell_val = mkAp2_val (mkRec bunG bunH1 bunH2) srcL tmOF opk
                   (cRec (gP p) (h1P p) (h2P p)) (ap1 srcF (pL p)) tmO
                   (mkRec_val bunG bunH1 bunH2 opk (gP p) (h1P p) (h2P p) (recG p ne) (recH1 p ne) (recH2 p ne))
                   (recPL p ne) (tmOF_val opk)
  in mkChain p ne negLeaf htag rRbCell ((tmAp2 (cRec (gP p) (h1P p) (h2P p)) (ap1 srcF (pL p)) tmO)) step2 node_fires cell_val

srcF_op_rRs_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (ap1 Fst (dtag p)) dgRs)
                  (eqF (ap1 srcF p)
                       (tmAp2 (cRec (gP p) (h1P p) (h2P p)) (ap1 srcF (pL p)) (tmAp1 cSuc (ap1 srcF (pR p)))))))
srcF_op_rRs_imp p ne =
  let open Node p ne dgRs
      node_fires =
        impEqTrans (ap1 cellNodeSrc opk) (ap1 src_l2 opk) (ap1 rRsCell opk)
          (fork_false_to_snd_imp htag ap1cCell src_l2 (testTag 1) opk
             (natEqSkip_imp htag derTagIdx 8 1 opk (wn 8 1 (\ ())) nieq_imp))
          (impEqTrans (ap1 src_l2 opk) (ap1 src_l3 opk) (ap1 rRsCell opk)
            (fork_false_to_snd_imp htag ap2cCell src_l3 (testTag 2) opk
               (natEqSkip_imp htag derTagIdx 8 2 opk (wn 8 2 (\ ())) nieq_imp))
            (impEqTrans (ap1 src_l3 opk) (ap1 src_l4 opk) (ap1 rRsCell opk)
              (fork_false_to_snd_imp htag rOCell src_l4 (testTag 3) opk
                 (natEqSkip_imp htag derTagIdx 8 3 opk (wn 8 3 (\ ())) nieq_imp))
              (impEqTrans (ap1 src_l4 opk) (ap1 src_l5 opk) (ap1 rRsCell opk)
                (fork_false_to_snd_imp htag rUCell src_l5 (testTag 4) opk
                   (natEqSkip_imp htag derTagIdx 8 4 opk (wn 8 4 (\ ())) nieq_imp))
                (impEqTrans (ap1 src_l5 opk) (ap1 src_l6 opk) (ap1 rRsCell opk)
                  (fork_false_to_snd_imp htag rVCell src_l6 (testTag 5) opk
                     (natEqSkip_imp htag derTagIdx 8 5 opk (wn 8 5 (\ ())) nieq_imp))
                  (impEqTrans (ap1 src_l6 opk) (ap1 src_l7 opk) (ap1 rRsCell opk)
                    (fork_false_to_snd_imp htag rCCell src_l7 (testTag 6) opk
                       (natEqSkip_imp htag derTagIdx 8 6 opk (wn 8 6 (\ ())) nieq_imp))
                    (fork_false_to_snd_imp htag rRbCell rRsCell (testTag 7) opk
                       (natEqSkip_imp htag derTagIdx 8 7 opk (wn 8 7 (\ ())) nieq_imp)))))))
      srcSuc = mkAp1_val cSucF srcR opk cSuc (ap1 srcF (pR p)) (cSucF_val opk) (recPR p ne)
      cell_val = mkAp2_val (mkRec bunG bunH1 bunH2) srcL (mkAp1 cSucF srcR) opk
                   (cRec (gP p) (h1P p) (h2P p)) (ap1 srcF (pL p)) (tmAp1 cSuc (ap1 srcF (pR p)))
                   (mkRec_val bunG bunH1 bunH2 opk (gP p) (h1P p) (h2P p) (recG p ne) (recH1 p ne) (recH2 p ne))
                   (recPL p ne) srcSuc
  in mkChain p ne negLeaf htag rRsCell
       (tmAp2 (cRec (gP p) (h1P p) (h2P p)) (ap1 srcF (pL p)) (tmAp1 cSuc (ap1 srcF (pR p)))) step2 node_fires cell_val
