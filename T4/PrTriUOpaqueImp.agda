{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.PrTriUOpaqueImp -- IMP-FORM opaque triF equations for the full p.r. calculus.
-- Depth-2 cases (reflO + redex O/U/V/C/Rb/Rs, dispatch on derTagIdx only) follow
-- the srcF/tgtF mkChain template; depth-3 cases (ap1c sub-dispatch on the carried
-- funhead Fst(funP p), and ap2c-v) thread an extra funhead antecedent via a
-- depth-3 context.  The depth-2 ap2c-cRec critical pair (Fst(funP p)=8) is in the
-- follow-up T4.PrTriUOpaque2Imp.
--
-- No holes, no postulates, no termination warnings (only the benign
-- RuleInst3:328 unreachable-clauses warning); --safe --without-K --exact-split.

module T4.PrTriUOpaqueImp where

open import T4.Base

open import T4.PrDerCode using ( derLeaf ; ap1c ; ap2c ; derO ; derU ; derV ; dgAp1c ; dgAp2c ; dgRo ; dgRu ; dgRv ; dgRC ; dgRb ; dgRs )
open import T4.PrCodeObj using ( cSuc )
open import T4.PrDev using ( mkAp2 ; mkAp2_val ; cSucF ; cSucF_val )
open import T4.PrTri
  using ( triF ; mkLabel ; mkLeafD ; mkLabel_val ; mkLeafD_val
        ; derTagIdx ; derBunIdx ; funHd ; bunSnd ; bunH1' ; bunH2' ; triFL ; triFR
        ; br_s_cell ; br_o_cell ; br_u_cell ; br_C_cell ; ap1_l2 ; ap1_l3 ; ap1Cell
        ; br_v_cell ; R_disp ; ap2Cell
        ; o_cell ; u_cell ; v_cell ; C_cell ; Rb_cell ; Rs_cell
        ; testTag ; tri_l2 ; tri_l3 ; tri_l4 ; tri_l5 ; tri_l6 ; tri_l7 ; cellNodeTri )
open import T4.PrTriUOpaque using ( funP ; gP ; h1P ; h2P ; recBunSnd )

open import T4.DerCodeS using ( dtag ; pL ; pR )
open import T4.BinTree using ( binNode ; nIdx ; lIdx ; rIdx )
open import T4.FoldRec using ( lookupAt ; fold ; get_newK )
open import T4.ParsObj using ( stepOf )
open import T4.ProgParse using ( get_tag )
open import T4.OpaqueLookup using ( lookup_op )
open import T4.WfRedExtract using ( pLValueBound ; pRValueBound )

open import T4.ForkImp
  using ( fork_true_to_fst_imp ; fork_false_to_snd_imp ; natEqFire_imp ; natEqSkip_imp )
open import T4.CtxKit using ( lift2 ; trans2c ; lift3 ; trans3c ; get3a ; get3b ; get3c ; ap3c )
open import T4.NatEqReflect using ( natEqF_complete )
open import T4.Thm12.ImpHelpers using ( impLift ; impEqTrans )

open import BRA3.Church       using ( pi ; predecessor )
open import BRA3.PairAlgebra  using ( compose1U ; compose1U_eq )
open import BRA3.SubT.NatEq    using ( natEqF )
open import BRA3.SubT.V2NatNeq using ( NatNeqWitness ; decideNatNeq )
open import BRA3.Contrapositive using ( compI ; liftP ; identP )
open import T4.GammaCtx using ( Cnj ; cnjL ; cnjR ; cnjUncurry ; cnjCurry ; gWeak )

import T4.OpaqueHarness
private
  triStepU : Fun1
  triStepU = stepOf mkLeafD cellNodeTri
open T4.OpaqueHarness.H triStepU

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
  recG : (p : Term) -> Deriv (neg (eqF p O)) -> Deriv (eqF (ap1 funHd (opkg p)) (gP p))
  recG p ne = ruleTrans (compose1U_eq Fst derBunIdx (opkg p)) (cong1 Fst (recBun p ne))
  recH1 : (p : Term) -> Deriv (neg (eqF p O)) -> Deriv (eqF (ap1 bunH1' (opkg p)) (h1P p))
  recH1 p ne = ruleTrans (compose1U_eq Fst bunSnd (opkg p))
                 (cong1 Fst (ruleTrans (compose1U_eq Snd derBunIdx (opkg p)) (cong1 Snd (recBun p ne))))
  recH2 : (p : Term) -> Deriv (neg (eqF p O)) -> Deriv (eqF (ap1 bunH2' (opkg p)) (h2P p))
  recH2 p ne = ruleTrans (compose1U_eq Snd bunSnd (opkg p))
                 (cong1 Snd (ruleTrans (compose1U_eq Snd derBunIdx (opkg p)) (cong1 Snd (recBun p ne))))
  -- funhead recovery (the carried fun's head, for the ap1c sub-dispatch).
  recFunHd : (p : Term) -> Deriv (neg (eqF p O)) -> {hh : Term} ->
    Deriv (eqF (ap1 Fst (funP p)) hh) -> Deriv (eqF (ap1 funHd (opkg p)) hh)
  recFunHd p ne hf = ruleTrans (compose1U_eq Fst derBunIdx (opkg p)) (ruleTrans (cong1 Fst (recBun p ne)) hf)

  recPL : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 triFL (opkg p)) (ap1 triF (pL p)))
  recPL p ne = lookup_op Z triStepU lIdx (ap1 predecessor p) (pL p) (op_pL p ne) (pLValueBound p ne)
  recPR : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 triFR (opkg p)) (ap1 triF (pR p)))
  recPR p ne = lookup_op Z triStepU rIdx (ap1 predecessor p) (pR p) (op_pR p ne) (pRValueBound p ne)

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
    step2 : Deriv (imp negLeaf (imp htag (eqF (ap1 triStepU opk) (ap1 cellNodeTri opk))))
    step2 = compI (fork_false_to_snd_imp negLeaf mkLeafD cellNodeTri
                     (C natEqF get_tag (constN 1)) opk nl_neg)
                  (axK (eqF (ap1 triStepU opk) (ap1 cellNodeTri opk)) htag)
    derTag_bare : Deriv (eqF (ap1 derTagIdx opk) (ap1 Fst (dtag p)))
    derTag_bare = ruleTrans (compose1U_eq Fst nIdx opk) (cong1 Fst (op_nIdx p ne))
    nieq_imp : Deriv (imp htag (eqF (ap1 derTagIdx opk) lbl))
    nieq_imp = impEqTrans (ap1 derTagIdx opk) (ap1 Fst (dtag p)) lbl
                 (impLift derTag_bare) (identP htag)

  mkChain : (p : Term) (ne : Deriv (neg (eqF p O))) (negLeaf htag : Formula) (cell : Fun1) (rhs : Term) ->
    Deriv (imp negLeaf (imp htag (eqF (ap1 triStepU (opkg p)) (ap1 cellNodeTri (opkg p))))) ->
    Deriv (imp htag (eqF (ap1 cellNodeTri (opkg p)) (ap1 cell (opkg p)))) ->
    Deriv (eqF (ap1 cell (opkg p)) rhs) ->
    Deriv (imp negLeaf (imp htag (eqF (ap1 triF p) rhs)))
  mkChain p ne negLeaf htag cell rhs step2 node_fires cell_val =
    let opk = opkg p
    in trans2c (ap1 triF p) (ap1 triStepU opk) rhs
         (lift2 negLeaf htag (opUnfold p ne))
         (trans2c (ap1 triStepU opk) (ap1 cellNodeTri opk) rhs step2
           (trans2c (ap1 cellNodeTri opk) (ap1 cell opk) rhs
             (liftP negLeaf node_fires) (lift2 negLeaf htag cell_val)))

------------------------------------------------------------------------
-- SECTION 2.  Leaf.

triF_op_reflO_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (eqF (ap1 Fst p) (natCode 1)) (eqF (ap1 triF p) derLeaf))
triF_op_reflO_imp p ne =
  let opk = opkg p
      Hleaf : Formula
      Hleaf = eqF (ap1 Fst p) (natCode 1)
      gtag : Deriv (imp Hleaf (eqF (ap1 get_tag opk) (natCode 1)))
      gtag = impEqTrans (ap1 get_tag opk) (ap1 Fst p) (natCode 1)
               (impLift (op_tag p ne)) (identP Hleaf)
      cell_fires : Deriv (imp Hleaf (eqF (ap1 triStepU opk) (ap1 mkLeafD opk)))
      cell_fires = fork_true_to_fst_imp Hleaf mkLeafD cellNodeTri (C natEqF get_tag (constN 1)) opk
                     (natEqFire_imp Hleaf get_tag 1 opk gtag)
  in impEqTrans (ap1 triF p) (ap1 triStepU opk) derLeaf
       (impLift (opUnfold p ne))
       (impEqTrans (ap1 triStepU opk) (ap1 mkLeafD opk) derLeaf cell_fires (impLift (mkLeafD_val opk)))

------------------------------------------------------------------------
-- SECTION 3.  Redex tags O / U / V (depth-2).

triF_op_O_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (ap1 Fst (dtag p)) dgRo) (eqF (ap1 triF p) derLeaf)))
triF_op_O_imp p ne =
  let open Node p ne dgRo
      node_fires =
        impEqTrans (ap1 cellNodeTri opk) (ap1 tri_l2 opk) (ap1 o_cell opk)
          (fork_false_to_snd_imp htag ap1Cell tri_l2 (testTag 1) opk
             (natEqSkip_imp htag derTagIdx 3 1 opk (wn 3 1 (\ ())) nieq_imp))
          (impEqTrans (ap1 tri_l2 opk) (ap1 tri_l3 opk) (ap1 o_cell opk)
            (fork_false_to_snd_imp htag ap2Cell tri_l3 (testTag 2) opk
               (natEqSkip_imp htag derTagIdx 3 2 opk (wn 3 2 (\ ())) nieq_imp))
            (fork_true_to_fst_imp htag o_cell tri_l4 (testTag 3) opk
               (natEqFire_imp htag derTagIdx 3 opk nieq_imp)))
  in mkChain p ne negLeaf htag o_cell derLeaf step2 node_fires (mkLeafD_val opk)

triF_op_U_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (ap1 Fst (dtag p)) dgRu) (eqF (ap1 triF p) (ap1 triF (pL p)))))
triF_op_U_imp p ne =
  let open Node p ne dgRu
      node_fires =
        impEqTrans (ap1 cellNodeTri opk) (ap1 tri_l2 opk) (ap1 u_cell opk)
          (fork_false_to_snd_imp htag ap1Cell tri_l2 (testTag 1) opk
             (natEqSkip_imp htag derTagIdx 4 1 opk (wn 4 1 (\ ())) nieq_imp))
          (impEqTrans (ap1 tri_l2 opk) (ap1 tri_l3 opk) (ap1 u_cell opk)
            (fork_false_to_snd_imp htag ap2Cell tri_l3 (testTag 2) opk
               (natEqSkip_imp htag derTagIdx 4 2 opk (wn 4 2 (\ ())) nieq_imp))
            (impEqTrans (ap1 tri_l3 opk) (ap1 tri_l4 opk) (ap1 u_cell opk)
              (fork_false_to_snd_imp htag o_cell tri_l4 (testTag 3) opk
                 (natEqSkip_imp htag derTagIdx 4 3 opk (wn 4 3 (\ ())) nieq_imp))
              (fork_true_to_fst_imp htag u_cell tri_l5 (testTag 4) opk
                 (natEqFire_imp htag derTagIdx 4 opk nieq_imp))))
  in mkChain p ne negLeaf htag u_cell (ap1 triF (pL p)) step2 node_fires (recPL p ne)

triF_op_V_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (ap1 Fst (dtag p)) dgRv) (eqF (ap1 triF p) (ap1 triF (pR p)))))
triF_op_V_imp p ne =
  let open Node p ne dgRv
      node_fires =
        impEqTrans (ap1 cellNodeTri opk) (ap1 tri_l2 opk) (ap1 v_cell opk)
          (fork_false_to_snd_imp htag ap1Cell tri_l2 (testTag 1) opk
             (natEqSkip_imp htag derTagIdx 5 1 opk (wn 5 1 (\ ())) nieq_imp))
          (impEqTrans (ap1 tri_l2 opk) (ap1 tri_l3 opk) (ap1 v_cell opk)
            (fork_false_to_snd_imp htag ap2Cell tri_l3 (testTag 2) opk
               (natEqSkip_imp htag derTagIdx 5 2 opk (wn 5 2 (\ ())) nieq_imp))
            (impEqTrans (ap1 tri_l3 opk) (ap1 tri_l4 opk) (ap1 v_cell opk)
              (fork_false_to_snd_imp htag o_cell tri_l4 (testTag 3) opk
                 (natEqSkip_imp htag derTagIdx 5 3 opk (wn 5 3 (\ ())) nieq_imp))
              (impEqTrans (ap1 tri_l4 opk) (ap1 tri_l5 opk) (ap1 v_cell opk)
                (fork_false_to_snd_imp htag u_cell tri_l5 (testTag 4) opk
                   (natEqSkip_imp htag derTagIdx 5 4 opk (wn 5 4 (\ ())) nieq_imp))
                (fork_true_to_fst_imp htag v_cell tri_l6 (testTag 5) opk
                   (natEqFire_imp htag derTagIdx 5 opk nieq_imp)))))
  in mkChain p ne negLeaf htag v_cell (ap1 triF (pR p)) step2 node_fires (recPR p ne)

------------------------------------------------------------------------
-- SECTION 4.  Redex tags C / Rb / Rs (depth-2; residual cells).

triF_op_C_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (ap1 Fst (dtag p)) dgRC)
                  (eqF (ap1 triF p)
                       (ap2c (gP p) (ap1c (h1P p) (ap1 triF (pL p))) (ap1c (h2P p) (ap1 triF (pL p)))))))
triF_op_C_imp p ne =
  let open Node p ne dgRC
      node_fires =
        impEqTrans (ap1 cellNodeTri opk) (ap1 tri_l2 opk) (ap1 C_cell opk)
          (fork_false_to_snd_imp htag ap1Cell tri_l2 (testTag 1) opk
             (natEqSkip_imp htag derTagIdx 6 1 opk (wn 6 1 (\ ())) nieq_imp))
          (impEqTrans (ap1 tri_l2 opk) (ap1 tri_l3 opk) (ap1 C_cell opk)
            (fork_false_to_snd_imp htag ap2Cell tri_l3 (testTag 2) opk
               (natEqSkip_imp htag derTagIdx 6 2 opk (wn 6 2 (\ ())) nieq_imp))
            (impEqTrans (ap1 tri_l3 opk) (ap1 tri_l4 opk) (ap1 C_cell opk)
              (fork_false_to_snd_imp htag o_cell tri_l4 (testTag 3) opk
                 (natEqSkip_imp htag derTagIdx 6 3 opk (wn 6 3 (\ ())) nieq_imp))
              (impEqTrans (ap1 tri_l4 opk) (ap1 tri_l5 opk) (ap1 C_cell opk)
                (fork_false_to_snd_imp htag u_cell tri_l5 (testTag 4) opk
                   (natEqSkip_imp htag derTagIdx 6 4 opk (wn 6 4 (\ ())) nieq_imp))
                (impEqTrans (ap1 tri_l5 opk) (ap1 tri_l6 opk) (ap1 C_cell opk)
                  (fork_false_to_snd_imp htag v_cell tri_l6 (testTag 5) opk
                     (natEqSkip_imp htag derTagIdx 6 5 opk (wn 6 5 (\ ())) nieq_imp))
                  (fork_true_to_fst_imp htag C_cell tri_l7 (testTag 6) opk
                     (natEqFire_imp htag derTagIdx 6 opk nieq_imp))))))
      armH1 = mkAp2_val (mkLabel 1 bunH1') triFL mkLeafD opk (ap2 Pair (natCode 1) (h1P p)) (ap1 triF (pL p)) derLeaf
                (mkLabel_val 1 bunH1' opk (h1P p) (recH1 p ne)) (recPL p ne) (mkLeafD_val opk)
      armH2 = mkAp2_val (mkLabel 1 bunH2') triFL mkLeafD opk (ap2 Pair (natCode 1) (h2P p)) (ap1 triF (pL p)) derLeaf
                (mkLabel_val 1 bunH2' opk (h2P p) (recH2 p ne)) (recPL p ne) (mkLeafD_val opk)
      cell_val = mkAp2_val (mkLabel 2 funHd) (mkAp2 (mkLabel 1 bunH1') triFL mkLeafD) (mkAp2 (mkLabel 1 bunH2') triFL mkLeafD) opk
                   (ap2 Pair (natCode 2) (gP p)) (ap1c (h1P p) (ap1 triF (pL p))) (ap1c (h2P p) (ap1 triF (pL p)))
                   (mkLabel_val 2 funHd opk (gP p) (recG p ne)) armH1 armH2
  in mkChain p ne negLeaf htag C_cell
       (ap2c (gP p) (ap1c (h1P p) (ap1 triF (pL p))) (ap1c (h2P p) (ap1 triF (pL p)))) step2 node_fires cell_val

triF_op_Rb_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (ap1 Fst (dtag p)) dgRb) (eqF (ap1 triF p) (ap1c (gP p) (ap1 triF (pL p))))))
triF_op_Rb_imp p ne =
  let open Node p ne dgRb
      node_fires =
        impEqTrans (ap1 cellNodeTri opk) (ap1 tri_l2 opk) (ap1 Rb_cell opk)
          (fork_false_to_snd_imp htag ap1Cell tri_l2 (testTag 1) opk
             (natEqSkip_imp htag derTagIdx 7 1 opk (wn 7 1 (\ ())) nieq_imp))
          (impEqTrans (ap1 tri_l2 opk) (ap1 tri_l3 opk) (ap1 Rb_cell opk)
            (fork_false_to_snd_imp htag ap2Cell tri_l3 (testTag 2) opk
               (natEqSkip_imp htag derTagIdx 7 2 opk (wn 7 2 (\ ())) nieq_imp))
            (impEqTrans (ap1 tri_l3 opk) (ap1 tri_l4 opk) (ap1 Rb_cell opk)
              (fork_false_to_snd_imp htag o_cell tri_l4 (testTag 3) opk
                 (natEqSkip_imp htag derTagIdx 7 3 opk (wn 7 3 (\ ())) nieq_imp))
              (impEqTrans (ap1 tri_l4 opk) (ap1 tri_l5 opk) (ap1 Rb_cell opk)
                (fork_false_to_snd_imp htag u_cell tri_l5 (testTag 4) opk
                   (natEqSkip_imp htag derTagIdx 7 4 opk (wn 7 4 (\ ())) nieq_imp))
                (impEqTrans (ap1 tri_l5 opk) (ap1 tri_l6 opk) (ap1 Rb_cell opk)
                  (fork_false_to_snd_imp htag v_cell tri_l6 (testTag 5) opk
                     (natEqSkip_imp htag derTagIdx 7 5 opk (wn 7 5 (\ ())) nieq_imp))
                  (impEqTrans (ap1 tri_l6 opk) (ap1 tri_l7 opk) (ap1 Rb_cell opk)
                    (fork_false_to_snd_imp htag C_cell tri_l7 (testTag 6) opk
                       (natEqSkip_imp htag derTagIdx 7 6 opk (wn 7 6 (\ ())) nieq_imp))
                    (fork_true_to_fst_imp htag Rb_cell Rs_cell (testTag 7) opk
                       (natEqFire_imp htag derTagIdx 7 opk nieq_imp)))))))
      cell_val = mkAp2_val (mkLabel 1 funHd) triFL mkLeafD opk (ap2 Pair (natCode 1) (gP p)) (ap1 triF (pL p)) derLeaf
                   (mkLabel_val 1 funHd opk (gP p) (recG p ne)) (recPL p ne) (mkLeafD_val opk)
  in mkChain p ne negLeaf htag Rb_cell (ap1c (gP p) (ap1 triF (pL p))) step2 node_fires cell_val

triF_op_Rs_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (ap1 Fst (dtag p)) dgRs)
                  (eqF (ap1 triF p)
                       (ap2c (h1P p) (ap2c (h2P p) (ap1 triF (pL p)) (ap1 triF (pR p)))
                                     (ap2c (ap2 Pair (natCode 8) (funP p)) (ap1 triF (pL p)) (ap1 triF (pR p)))))))
triF_op_Rs_imp p ne =
  let open Node p ne dgRs
      node_fires =
        impEqTrans (ap1 cellNodeTri opk) (ap1 tri_l2 opk) (ap1 Rs_cell opk)
          (fork_false_to_snd_imp htag ap1Cell tri_l2 (testTag 1) opk
             (natEqSkip_imp htag derTagIdx 8 1 opk (wn 8 1 (\ ())) nieq_imp))
          (impEqTrans (ap1 tri_l2 opk) (ap1 tri_l3 opk) (ap1 Rs_cell opk)
            (fork_false_to_snd_imp htag ap2Cell tri_l3 (testTag 2) opk
               (natEqSkip_imp htag derTagIdx 8 2 opk (wn 8 2 (\ ())) nieq_imp))
            (impEqTrans (ap1 tri_l3 opk) (ap1 tri_l4 opk) (ap1 Rs_cell opk)
              (fork_false_to_snd_imp htag o_cell tri_l4 (testTag 3) opk
                 (natEqSkip_imp htag derTagIdx 8 3 opk (wn 8 3 (\ ())) nieq_imp))
              (impEqTrans (ap1 tri_l4 opk) (ap1 tri_l5 opk) (ap1 Rs_cell opk)
                (fork_false_to_snd_imp htag u_cell tri_l5 (testTag 4) opk
                   (natEqSkip_imp htag derTagIdx 8 4 opk (wn 8 4 (\ ())) nieq_imp))
                (impEqTrans (ap1 tri_l5 opk) (ap1 tri_l6 opk) (ap1 Rs_cell opk)
                  (fork_false_to_snd_imp htag v_cell tri_l6 (testTag 5) opk
                     (natEqSkip_imp htag derTagIdx 8 5 opk (wn 8 5 (\ ())) nieq_imp))
                  (impEqTrans (ap1 tri_l6 opk) (ap1 tri_l7 opk) (ap1 Rs_cell opk)
                    (fork_false_to_snd_imp htag C_cell tri_l7 (testTag 6) opk
                       (natEqSkip_imp htag derTagIdx 8 6 opk (wn 8 6 (\ ())) nieq_imp))
                    (fork_false_to_snd_imp htag Rb_cell Rs_cell (testTag 7) opk
                       (natEqSkip_imp htag derTagIdx 8 7 opk (wn 8 7 (\ ())) nieq_imp)))))))
      arm2 = mkAp2_val (mkLabel 2 bunH2') triFL triFR opk (ap2 Pair (natCode 2) (h2P p)) (ap1 triF (pL p)) (ap1 triF (pR p))
               (mkLabel_val 2 bunH2' opk (h2P p) (recH2 p ne)) (recPL p ne) (recPR p ne)
      recFun = mkLabel_val 2 (mkLabel 8 derBunIdx) opk (ap2 Pair (natCode 8) (funP p))
                 (mkLabel_val 8 derBunIdx opk (funP p) (recBun p ne))
      arm3 = mkAp2_val (mkLabel 2 (mkLabel 8 derBunIdx)) triFL triFR opk (ap2 Pair (natCode 2) (ap2 Pair (natCode 8) (funP p))) (ap1 triF (pL p)) (ap1 triF (pR p))
               recFun (recPL p ne) (recPR p ne)
      cell_val = mkAp2_val (mkLabel 2 bunH1') (mkAp2 (mkLabel 2 bunH2') triFL triFR) (mkAp2 (mkLabel 2 (mkLabel 8 derBunIdx)) triFL triFR) opk
                   (ap2 Pair (natCode 2) (h1P p)) (ap2c (h2P p) (ap1 triF (pL p)) (ap1 triF (pR p)))
                   (ap2c (ap2 Pair (natCode 8) (funP p)) (ap1 triF (pL p)) (ap1 triF (pR p)))
                   (mkLabel_val 2 bunH1' opk (h1P p) (recH1 p ne)) arm2 arm3
  in mkChain p ne negLeaf htag Rs_cell
       (ap2c (h1P p) (ap2c (h2P p) (ap1 triF (pL p)) (ap1 triF (pR p)))
                     (ap2c (ap2 Pair (natCode 8) (funP p)) (ap1 triF (pL p)) (ap1 triF (pR p)))) step2 node_fires cell_val

------------------------------------------------------------------------
-- SECTION 5.  Depth-3 cases: ap1c funhead sub-dispatch + ap2c-v.
-- Context = Cnj (Cnj negLeaf htag) funhead, threaded with GammaCtx.

private
  -- ap1c: enter ap1Cell (htag = dgAp1c) under [negLeaf, htag].
  module Ap1c (p : Term) (ne : Deriv (neg (eqF p O))) where
    open Node p ne dgAp1c public
    fireTag1 : Deriv (imp htag (eqF (ap1 cellNodeTri opk) (ap1 ap1Cell opk)))
    fireTag1 = fork_true_to_fst_imp htag ap1Cell tri_l2 (testTag 1) opk
                 (natEqFire_imp htag derTagIdx 1 opk nieq_imp)
    toAp1Cell_NH : Deriv (imp negLeaf (imp htag (eqF (ap1 triF p) (ap1 ap1Cell opk))))
    toAp1Cell_NH =
      trans2c (ap1 triF p) (ap1 triStepU opk) (ap1 ap1Cell opk)
        (lift2 negLeaf htag (opUnfold p ne))
        (trans2c (ap1 triStepU opk) (ap1 cellNodeTri opk) (ap1 ap1Cell opk)
          step2 (liftP negLeaf fireTag1))

  -- assemble an ap1c eq from the funhead-dispatch+cellval fact under Gamma.
  mkAp1Eq : (p : Term) (negLeaf htag funhead : Formula) (rhs : Term) ->
    Deriv (imp negLeaf (imp htag (eqF (ap1 triF p) (ap1 ap1Cell (opkg p))))) ->
    Deriv (imp (Cnj (Cnj negLeaf htag) funhead) (eqF (ap1 ap1Cell (opkg p)) rhs)) ->
    Deriv (imp negLeaf (imp htag (imp funhead (eqF (ap1 triF p) rhs))))
  mkAp1Eq p negLeaf htag funhead rhs toCellNH funDisp =
    let gToAp1 = compI (cnjL (Cnj negLeaf htag) funhead) (cnjUncurry toCellNH)
        full = impEqTrans (ap1 triF p) (ap1 ap1Cell (opkg p)) rhs gToAp1 funDisp
    in cnjCurry (cnjCurry full)

-- ap1c, funhead = 4 (o)  =>  triF p = derO (triF (pL p)).
triF_op_ap1c_o_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (ap1 Fst (dtag p)) dgAp1c)
                  (imp (eqF (ap1 Fst (funP p)) (natCode 4)) (eqF (ap1 triF p) (derO (ap1 triF (pL p)))))))
triF_op_ap1c_o_imp p ne =
  let open Ap1c p ne
      funhead = eqF (ap1 Fst (funP p)) (natCode 4)
      Gam = Cnj (Cnj negLeaf htag) funhead
      pFun = cnjR (Cnj negLeaf htag) funhead
      gFn = impEqTrans (ap1 funHd opk) (gP p) (natCode 4) (gWeak Gam (recG p ne)) pFun
      funCascade = fork_true_to_fst_imp Gam br_o_cell ap1_l2 (C natEqF funHd (constN 4)) opk
                     (natEqFire_imp Gam funHd 4 opk gFn)
      cell_val = mkAp2_val (mkLabel 3 Z) triFL mkLeafD opk (ap2 Pair (natCode 3) O) (ap1 triF (pL p)) derLeaf
                   (mkLabel_val 3 Z opk O (axZ opk)) (recPL p ne) (mkLeafD_val opk)
      funDisp = impEqTrans (ap1 ap1Cell opk) (ap1 br_o_cell opk) (derO (ap1 triF (pL p)))
                  funCascade (gWeak Gam cell_val)
  in mkAp1Eq p negLeaf htag funhead (derO (ap1 triF (pL p))) toAp1Cell_NH funDisp

-- ap1c, funhead = 5 (u)  =>  triF p = derU (triF (pL p)).
triF_op_ap1c_u_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (ap1 Fst (dtag p)) dgAp1c)
                  (imp (eqF (ap1 Fst (funP p)) (natCode 5)) (eqF (ap1 triF p) (derU (ap1 triF (pL p)))))))
triF_op_ap1c_u_imp p ne =
  let open Ap1c p ne
      funhead = eqF (ap1 Fst (funP p)) (natCode 5)
      Gam = Cnj (Cnj negLeaf htag) funhead
      pFun = cnjR (Cnj negLeaf htag) funhead
      gFn = impEqTrans (ap1 funHd opk) (gP p) (natCode 5) (gWeak Gam (recG p ne)) pFun
      funCascade =
        impEqTrans (ap1 ap1Cell opk) (ap1 ap1_l2 opk) (ap1 br_u_cell opk)
          (fork_false_to_snd_imp Gam br_o_cell ap1_l2 (C natEqF funHd (constN 4)) opk
             (natEqSkip_imp Gam funHd 5 4 opk (wn 5 4 (\ ())) gFn))
          (fork_true_to_fst_imp Gam br_u_cell ap1_l3 (C natEqF funHd (constN 5)) opk
             (natEqFire_imp Gam funHd 5 opk gFn))
      cell_val = mkAp2_val (mkLabel 4 Z) triFL mkLeafD opk (ap2 Pair (natCode 4) O) (ap1 triF (pL p)) derLeaf
                   (mkLabel_val 4 Z opk O (axZ opk)) (recPL p ne) (mkLeafD_val opk)
      funDisp = impEqTrans (ap1 ap1Cell opk) (ap1 br_u_cell opk) (derU (ap1 triF (pL p)))
                  funCascade (gWeak Gam cell_val)
  in mkAp1Eq p negLeaf htag funhead (derU (ap1 triF (pL p))) toAp1Cell_NH funDisp

-- ap1c, funhead = 6 (C)  =>  triF p = binNode (Pair 6 (Snd (funP p))) (triF pL) derLeaf.
triF_op_ap1c_C_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (ap1 Fst (dtag p)) dgAp1c)
                  (imp (eqF (ap1 Fst (funP p)) (natCode 6))
                       (eqF (ap1 triF p) (binNode (ap2 Pair (natCode 6) (ap1 Snd (funP p))) (ap1 triF (pL p)) derLeaf)))))
triF_op_ap1c_C_imp p ne =
  let open Ap1c p ne
      funhead = eqF (ap1 Fst (funP p)) (natCode 6)
      Gam = Cnj (Cnj negLeaf htag) funhead
      pFun = cnjR (Cnj negLeaf htag) funhead
      gFn = impEqTrans (ap1 funHd opk) (gP p) (natCode 6) (gWeak Gam (recG p ne)) pFun
      rhs = binNode (ap2 Pair (natCode 6) (ap1 Snd (funP p))) (ap1 triF (pL p)) derLeaf
      funCascade =
        impEqTrans (ap1 ap1Cell opk) (ap1 ap1_l2 opk) (ap1 br_C_cell opk)
          (fork_false_to_snd_imp Gam br_o_cell ap1_l2 (C natEqF funHd (constN 4)) opk
             (natEqSkip_imp Gam funHd 6 4 opk (wn 6 4 (\ ())) gFn))
          (impEqTrans (ap1 ap1_l2 opk) (ap1 ap1_l3 opk) (ap1 br_C_cell opk)
            (fork_false_to_snd_imp Gam br_u_cell ap1_l3 (C natEqF funHd (constN 5)) opk
               (natEqSkip_imp Gam funHd 6 5 opk (wn 6 5 (\ ())) gFn))
            (fork_true_to_fst_imp Gam br_C_cell br_s_cell (C natEqF funHd (constN 6)) opk
               (natEqFire_imp Gam funHd 6 opk gFn)))
      cell_val = mkAp2_val (mkLabel 6 bunSnd) triFL mkLeafD opk (ap2 Pair (natCode 6) (ap1 Snd (funP p))) (ap1 triF (pL p)) derLeaf
                   (mkLabel_val 6 bunSnd opk (ap1 Snd (funP p)) (recBunSnd p ne)) (recPL p ne) (mkLeafD_val opk)
      funDisp = impEqTrans (ap1 ap1Cell opk) (ap1 br_C_cell opk) rhs funCascade (gWeak Gam cell_val)
  in mkAp1Eq p negLeaf htag funhead rhs toAp1Cell_NH funDisp

-- ap1c, funhead = 3 (s)  =>  triF p = ap1c cSuc (triF (pL p)).
triF_op_ap1c_s_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (ap1 Fst (dtag p)) dgAp1c)
                  (imp (eqF (ap1 Fst (funP p)) (natCode 3)) (eqF (ap1 triF p) (ap1c cSuc (ap1 triF (pL p)))))))
triF_op_ap1c_s_imp p ne =
  let open Ap1c p ne
      funhead = eqF (ap1 Fst (funP p)) (natCode 3)
      Gam = Cnj (Cnj negLeaf htag) funhead
      pFun = cnjR (Cnj negLeaf htag) funhead
      gFn = impEqTrans (ap1 funHd opk) (gP p) (natCode 3) (gWeak Gam (recG p ne)) pFun
      funCascade =
        impEqTrans (ap1 ap1Cell opk) (ap1 ap1_l2 opk) (ap1 br_s_cell opk)
          (fork_false_to_snd_imp Gam br_o_cell ap1_l2 (C natEqF funHd (constN 4)) opk
             (natEqSkip_imp Gam funHd 3 4 opk (wn 3 4 (\ ())) gFn))
          (impEqTrans (ap1 ap1_l2 opk) (ap1 ap1_l3 opk) (ap1 br_s_cell opk)
            (fork_false_to_snd_imp Gam br_u_cell ap1_l3 (C natEqF funHd (constN 5)) opk
               (natEqSkip_imp Gam funHd 3 5 opk (wn 3 5 (\ ())) gFn))
            (fork_false_to_snd_imp Gam br_C_cell br_s_cell (C natEqF funHd (constN 6)) opk
               (natEqSkip_imp Gam funHd 3 6 opk (wn 3 6 (\ ())) gFn)))
      cell_val = mkAp2_val (mkLabel 1 cSucF) triFL mkLeafD opk (ap2 Pair (natCode 1) cSuc) (ap1 triF (pL p)) derLeaf
                   (mkLabel_val 1 cSucF opk cSuc (cSucF_val opk)) (recPL p ne) (mkLeafD_val opk)
      funDisp = impEqTrans (ap1 ap1Cell opk) (ap1 br_s_cell opk) (ap1c cSuc (ap1 triF (pL p)))
                  funCascade (gWeak Gam cell_val)
  in mkAp1Eq p negLeaf htag funhead (ap1c cSuc (ap1 triF (pL p))) toAp1Cell_NH funDisp

------------------------------------------------------------------------
-- SECTION 6.  ap2c-v  (htag = dgAp2c, funhead = 7).

private
  module Ap2c (p : Term) (ne : Deriv (neg (eqF p O))) where
    open Node p ne dgAp2c public
    fireTag2 : Deriv (imp htag (eqF (ap1 cellNodeTri opk) (ap1 ap2Cell opk)))
    fireTag2 =
      impEqTrans (ap1 cellNodeTri opk) (ap1 tri_l2 opk) (ap1 ap2Cell opk)
        (fork_false_to_snd_imp htag ap1Cell tri_l2 (testTag 1) opk
           (natEqSkip_imp htag derTagIdx 2 1 opk (wn 2 1 (\ ())) nieq_imp))
        (fork_true_to_fst_imp htag ap2Cell tri_l3 (testTag 2) opk
           (natEqFire_imp htag derTagIdx 2 opk nieq_imp))
    toAp2Cell_NH : Deriv (imp negLeaf (imp htag (eqF (ap1 triF p) (ap1 ap2Cell opk))))
    toAp2Cell_NH =
      trans2c (ap1 triF p) (ap1 triStepU opk) (ap1 ap2Cell opk)
        (lift2 negLeaf htag (opUnfold p ne))
        (trans2c (ap1 triStepU opk) (ap1 cellNodeTri opk) (ap1 ap2Cell opk)
          step2 (liftP negLeaf fireTag2))

triF_op_ap2c_v_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (ap1 Fst (dtag p)) dgAp2c)
                  (imp (eqF (ap1 Fst (funP p)) (natCode 7))
                       (eqF (ap1 triF p) (derV (ap1 triF (pL p)) (ap1 triF (pR p)))))))
triF_op_ap2c_v_imp p ne =
  let open Ap2c p ne
      funhead = eqF (ap1 Fst (funP p)) (natCode 7)
      Gam = Cnj (Cnj negLeaf htag) funhead
      pFun = cnjR (Cnj negLeaf htag) funhead
      gFn = impEqTrans (ap1 funHd opk) (gP p) (natCode 7) (gWeak Gam (recG p ne)) pFun
      funCascade = fork_true_to_fst_imp Gam br_v_cell R_disp (C natEqF funHd (constN 7)) opk
                     (natEqFire_imp Gam funHd 7 opk gFn)
      cell_val = mkAp2_val (mkLabel 5 Z) triFL triFR opk (ap2 Pair (natCode 5) O) (ap1 triF (pL p)) (ap1 triF (pR p))
                   (mkLabel_val 5 Z opk O (axZ opk)) (recPL p ne) (recPR p ne)
      rhs = derV (ap1 triF (pL p)) (ap1 triF (pR p))
      gToAp2 = compI (cnjL (Cnj negLeaf htag) funhead) (cnjUncurry toAp2Cell_NH)
      funDisp = impEqTrans (ap1 ap2Cell opk) (ap1 br_v_cell opk) rhs funCascade (gWeak Gam cell_val)
      full = impEqTrans (ap1 triF p) (ap1 ap2Cell opk) rhs gToAp2 funDisp
  in cnjCurry (cnjCurry full)
