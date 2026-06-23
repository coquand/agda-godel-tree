{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.PrTriUOpaque2Imp -- IMP-FORM opaque depth-2 ap2c-cRec triF equations (the
-- critical-pair case), mirroring T4.PrTriUOpaque2 in imp-form via GammaCtx.
-- Context = nested Cnj of [negLeaf, htag=dgAp2c, funhead=8, pR-conditions].
-- "To R_disp" is shared (Gam0 = Cnj (Cnj negLeaf htag) funhead); each case
-- extends Gam0 with the right-child conditions and dispatches within R_disp.
--
-- No holes, no postulates, no termination warnings (only the benign
-- RuleInst3:328 unreachable-clauses warning); --safe --without-K --exact-split.

module T4.PrTriUOpaque2Imp where

open import T4.Base

open import T4.PrDerCode using ( derLeaf ; dgAp2c )
open import T4.PrDev using ( mkAp2 ; mkAp2_val )
open import T4.PrTri
  using ( triF ; mkLabel ; mkLeafD ; mkLabel_val ; mkLeafD_val
        ; derTagIdx ; derBunIdx ; funHd ; bunSnd ; triFL ; triFR ; derLF
        ; ap1Cell ; ap2Cell ; br_v_cell ; R_disp ; R_mid ; R_inner
        ; br_Rb_cell ; br_Rs_cell ; br_Rcong_cell
        ; d2tag ; d2lab ; d2labTag ; d2FunHd
        ; testTag ; tri_l2 ; tri_l3 ; cellNodeTri )
open import T4.PrTriUOpaque using ( funP ; gP ; recBunSnd )

open import T4.DerCodeS using ( dtag ; pL ; pR )
open import T4.BinTree using ( binNode ; nIdx ; lIdx ; rIdx )
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

  recPL : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 triFL (opkg p)) (ap1 triF (pL p)))
  recPL p ne = lookup_op Z triStepU lIdx (ap1 predecessor p) (pL p) (op_pL p ne) (pLValueBound p ne)
  recPR : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 triFR (opkg p)) (ap1 triF (pR p)))
  recPR p ne = lookup_op Z triStepU rIdx (ap1 predecessor p) (pR p) (op_pR p ne) (pRValueBound p ne)

  -- d2 = pR p readers (bare).
  d2tag_bare : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 d2tag (opkg p)) (ap1 Fst (pR p)))
  d2tag_bare p ne = ruleTrans (compose1U_eq Fst rIdx (opkg p)) (cong1 Fst (op_pR p ne))
  d2lab_bare : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 d2lab (opkg p)) (ap1 Fst (ap1 Snd (pR p))))
  d2lab_bare p ne =
    ruleTrans (compose1U_eq Fst (compose1U Snd rIdx) (opkg p))
      (cong1 Fst (ruleTrans (compose1U_eq Snd rIdx (opkg p)) (cong1 Snd (op_pR p ne))))
  d2labTag_bare : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 d2labTag (opkg p)) (ap1 Fst (ap1 Fst (ap1 Snd (pR p)))))
  d2labTag_bare p ne = ruleTrans (compose1U_eq Fst d2lab (opkg p)) (cong1 Fst (d2lab_bare p ne))
  d2FunHd_bare : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 d2FunHd (opkg p)) (ap1 Fst (ap1 Snd (ap1 Fst (ap1 Snd (pR p))))))
  d2FunHd_bare p ne =
    ruleTrans (compose1U_eq Fst (compose1U Snd d2lab) (opkg p))
      (cong1 Fst (ruleTrans (compose1U_eq Snd d2lab (opkg p)) (cong1 Snd (d2lab_bare p ne))))

  -- the shared "to R_disp" derivation under Gam0 = Cnj (Cnj negLeaf htag) funhead.
  module RecNode (p : Term) (ne : Deriv (neg (eqF p O))) where
    opk = opkg p
    negLeaf : Formula
    negLeaf = neg (eqF (ap1 Fst p) (natCode 1))
    htag : Formula
    htag = eqF (ap1 Fst (dtag p)) dgAp2c
    funhead : Formula
    funhead = eqF (ap1 Fst (funP p)) (natCode 8)
    Gam0 : Formula
    Gam0 = Cnj (Cnj negLeaf htag) funhead
    pNH : Deriv (imp Gam0 (Cnj negLeaf htag))
    pNH = cnjL (Cnj negLeaf htag) funhead
    pFun : Deriv (imp Gam0 funhead)
    pFun = cnjR (Cnj negLeaf htag) funhead
    pHtag : Deriv (imp Gam0 htag)
    pHtag = compI pNH (cnjR negLeaf htag)
    -- step2 (triStepU = cellNodeTri) under [negLeaf, htag].
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
    nieq_imp : Deriv (imp htag (eqF (ap1 derTagIdx opk) dgAp2c))
    nieq_imp = impEqTrans (ap1 derTagIdx opk) (ap1 Fst (dtag p)) dgAp2c
                 (impLift derTag_bare) (identP htag)
    -- to cellNodeTri / ap2Cell / R_disp, all under Gam0.
    gToCell : Deriv (imp Gam0 (eqF (ap1 triF p) (ap1 cellNodeTri opk)))
    gToCell = impEqTrans (ap1 triF p) (ap1 triStepU opk) (ap1 cellNodeTri opk)
                (gWeak Gam0 (opUnfold p ne)) (compI pNH (cnjUncurry step2))
    gFireTag2 : Deriv (imp Gam0 (eqF (ap1 cellNodeTri opk) (ap1 ap2Cell opk)))
    gFireTag2 = compI pHtag
      (impEqTrans (ap1 cellNodeTri opk) (ap1 tri_l2 opk) (ap1 ap2Cell opk)
        (fork_false_to_snd_imp htag ap1Cell tri_l2 (testTag 1) opk
           (natEqSkip_imp htag derTagIdx 2 1 opk (wn 2 1 (\ ())) nieq_imp))
        (fork_true_to_fst_imp htag ap2Cell tri_l3 (testTag 2) opk
           (natEqFire_imp htag derTagIdx 2 opk nieq_imp)))
    gFn8 : Deriv (imp Gam0 (eqF (ap1 funHd opk) (natCode 8)))
    gFn8 = impEqTrans (ap1 funHd opk) (gP p) (natCode 8) (gWeak Gam0 (recG p ne)) pFun
    gToR : Deriv (imp Gam0 (eqF (ap1 ap2Cell opk) (ap1 R_disp opk)))
    gToR = fork_false_to_snd_imp Gam0 br_v_cell R_disp (C natEqF funHd (constN 7)) opk
             (natEqSkip_imp Gam0 funHd 8 7 opk (wn 8 7 (\ ())) gFn8)
    toRdisp_G0 : Deriv (imp Gam0 (eqF (ap1 triF p) (ap1 R_disp opk)))
    toRdisp_G0 = impEqTrans (ap1 triF p) (ap1 cellNodeTri opk) (ap1 R_disp opk) gToCell
                   (impEqTrans (ap1 cellNodeTri opk) (ap1 ap2Cell opk) (ap1 R_disp opk) gFireTag2 gToR)

------------------------------------------------------------------------
-- SECTION 2.  Rb:  pR p a leaf  (Fst (pR p) = 1).

triF_op_ap2c_Rb_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (ap1 Fst (dtag p)) dgAp2c)
                  (imp (eqF (ap1 Fst (funP p)) (natCode 8))
                       (imp (eqF (ap1 Fst (pR p)) (natCode 1))
                            (eqF (ap1 triF p) (binNode (ap2 Pair (natCode 7) (ap1 Snd (funP p))) (ap1 triF (pL p)) derLeaf))))))
triF_op_ap2c_Rb_imp p ne =
  let open RecNode p ne
      hd2 : Formula
      hd2 = eqF (ap1 Fst (pR p)) (natCode 1)
      Gam = Cnj Gam0 hd2
      pHd2 = cnjR Gam0 hd2
      rhs = binNode (ap2 Pair (natCode 7) (ap1 Snd (funP p))) (ap1 triF (pL p)) derLeaf
      gToR = compI (cnjL Gam0 hd2) toRdisp_G0
      gD2 = impEqTrans (ap1 d2tag opk) (ap1 Fst (pR p)) (natCode 1) (gWeak Gam (d2tag_bare p ne)) pHd2
      fires = fork_true_to_fst_imp Gam br_Rb_cell R_mid (C natEqF d2tag (constN 1)) opk
                (natEqFire_imp Gam d2tag 1 opk gD2)
      cell_val = mkAp2_val (mkLabel 7 bunSnd) triFL mkLeafD opk
                   (ap2 Pair (natCode 7) (ap1 Snd (funP p))) (ap1 triF (pL p)) derLeaf
                   (mkLabel_val 7 bunSnd opk (ap1 Snd (funP p)) (recBunSnd p ne)) (recPL p ne) (mkLeafD_val opk)
      full = impEqTrans (ap1 triF p) (ap1 R_disp opk) rhs gToR
               (impEqTrans (ap1 R_disp opk) (ap1 br_Rb_cell opk) rhs fires (gWeak Gam cell_val))
  in cnjCurry (cnjCurry (cnjCurry full))

------------------------------------------------------------------------
-- SECTION 3.  Rs:  pR p = ap1c cSuc ..  (node, dtag = ap1c, funhead = cSuc).

triF_op_ap2c_Rs_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (ap1 Fst (dtag p)) dgAp2c)
                  (imp (eqF (ap1 Fst (funP p)) (natCode 8))
                       (imp (eqF (ap1 Fst (pR p)) (natCode 2))
                            (imp (eqF (ap1 Fst (ap1 Fst (ap1 Snd (pR p)))) (natCode 1))
                                 (imp (eqF (ap1 Fst (ap1 Snd (ap1 Fst (ap1 Snd (pR p))))) (natCode 3))
                                      (eqF (ap1 triF p)
                                           (binNode (ap2 Pair (natCode 8) (ap1 Snd (funP p))) (ap1 triF (pL p))
                                                    (ap1 derLF (ap1 triF (pR p)))))))))))
triF_op_ap2c_Rs_imp p ne =
  let open RecNode p ne
      hd2node : Formula
      hd2node = eqF (ap1 Fst (pR p)) (natCode 2)
      hlabTag : Formula
      hlabTag = eqF (ap1 Fst (ap1 Fst (ap1 Snd (pR p)))) (natCode 1)
      hfun : Formula
      hfun = eqF (ap1 Fst (ap1 Snd (ap1 Fst (ap1 Snd (pR p))))) (natCode 3)
      Gam = Cnj (Cnj (Cnj Gam0 hd2node) hlabTag) hfun
      pG0   = compI (cnjL (Cnj (Cnj Gam0 hd2node) hlabTag) hfun)
                    (compI (cnjL (Cnj Gam0 hd2node) hlabTag) (cnjL Gam0 hd2node))
      pHd2  = compI (cnjL (Cnj (Cnj Gam0 hd2node) hlabTag) hfun)
                    (compI (cnjL (Cnj Gam0 hd2node) hlabTag) (cnjR Gam0 hd2node))
      pLab  = compI (cnjL (Cnj (Cnj Gam0 hd2node) hlabTag) hfun) (cnjR (Cnj Gam0 hd2node) hlabTag)
      pFunR = cnjR (Cnj (Cnj Gam0 hd2node) hlabTag) hfun
      rhs = binNode (ap2 Pair (natCode 8) (ap1 Snd (funP p))) (ap1 triF (pL p)) (ap1 derLF (ap1 triF (pR p)))
      gToR = compI pG0 toRdisp_G0
      gD2  = impEqTrans (ap1 d2tag opk) (ap1 Fst (pR p)) (natCode 2) (gWeak Gam (d2tag_bare p ne)) pHd2
      gLab = impEqTrans (ap1 d2labTag opk) (ap1 Fst (ap1 Fst (ap1 Snd (pR p)))) (natCode 1) (gWeak Gam (d2labTag_bare p ne)) pLab
      gFun = impEqTrans (ap1 d2FunHd opk) (ap1 Fst (ap1 Snd (ap1 Fst (ap1 Snd (pR p))))) (natCode 3) (gWeak Gam (d2FunHd_bare p ne)) pFunR
      fires =
        impEqTrans (ap1 R_disp opk) (ap1 R_mid opk) (ap1 br_Rs_cell opk)
          (fork_false_to_snd_imp Gam br_Rb_cell R_mid (C natEqF d2tag (constN 1)) opk
             (natEqSkip_imp Gam d2tag 2 1 opk (wn 2 1 (\ ())) gD2))
          (impEqTrans (ap1 R_mid opk) (ap1 R_inner opk) (ap1 br_Rs_cell opk)
            (fork_true_to_fst_imp Gam R_inner br_Rcong_cell (C natEqF d2labTag (constN 1)) opk
               (natEqFire_imp Gam d2labTag 1 opk gLab))
            (fork_true_to_fst_imp Gam br_Rs_cell br_Rcong_cell (C natEqF d2FunHd (constN 3)) opk
               (natEqFire_imp Gam d2FunHd 3 opk gFun)))
      thirdArm : Deriv (eqF (ap1 (compose1U derLF triFR) opk) (ap1 derLF (ap1 triF (pR p))))
      thirdArm = ruleTrans (compose1U_eq derLF triFR opk) (cong1 derLF (recPR p ne))
      cell_val = mkAp2_val (mkLabel 8 bunSnd) triFL (compose1U derLF triFR) opk
                   (ap2 Pair (natCode 8) (ap1 Snd (funP p))) (ap1 triF (pL p)) (ap1 derLF (ap1 triF (pR p)))
                   (mkLabel_val 8 bunSnd opk (ap1 Snd (funP p)) (recBunSnd p ne)) (recPL p ne) thirdArm
      full = impEqTrans (ap1 triF p) (ap1 R_disp opk) rhs gToR
               (impEqTrans (ap1 R_disp opk) (ap1 br_Rs_cell opk) rhs fires (gWeak Gam cell_val))
  in cnjCurry (cnjCurry (cnjCurry (cnjCurry (cnjCurry full))))


------------------------------------------------------------------------
-- SECTION 4.  R-congruence "else" (two flavors).

private
  br_Rcong_val : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 br_Rcong_cell (opkg p))
               (binNode (ap2 Pair (natCode 2) (funP p)) (ap1 triF (pL p)) (ap1 triF (pR p))))
  br_Rcong_val p ne =
    mkAp2_val (mkLabel 2 derBunIdx) triFL triFR (opkg p)
      (ap2 Pair (natCode 2) (funP p)) (ap1 triF (pL p)) (ap1 triF (pR p))
      (mkLabel_val 2 derBunIdx (opkg p) (funP p) (recBun p ne)) (recPL p ne) (recPR p ne)

-- (A) pR p a non-ap1c node:  Fst(pR p)=2 , dtag(pR p)-tag = m != 1.
triF_op_ap2c_Rcong_notAp1c_imp : (p : Term) -> Deriv (neg (eqF p O)) -> (m : Nat) -> ((Eq m 1) -> Empty) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (ap1 Fst (dtag p)) dgAp2c)
                  (imp (eqF (ap1 Fst (funP p)) (natCode 8))
                       (imp (eqF (ap1 Fst (pR p)) (natCode 2))
                            (imp (eqF (ap1 Fst (ap1 Fst (ap1 Snd (pR p)))) (natCode m))
                                 (eqF (ap1 triF p) (binNode (ap2 Pair (natCode 2) (funP p)) (ap1 triF (pL p)) (ap1 triF (pR p)))))))))
triF_op_ap2c_Rcong_notAp1c_imp p ne m m1 =
  let open RecNode p ne
      hd2node : Formula
      hd2node = eqF (ap1 Fst (pR p)) (natCode 2)
      hlabM : Formula
      hlabM = eqF (ap1 Fst (ap1 Fst (ap1 Snd (pR p)))) (natCode m)
      L1 = Cnj Gam0 hd2node
      Gam = Cnj L1 hlabM
      pG0   = compI (cnjL L1 hlabM) (cnjL Gam0 hd2node)
      pHd2  = compI (cnjL L1 hlabM) (cnjR Gam0 hd2node)
      pLabM = cnjR L1 hlabM
      rhs = binNode (ap2 Pair (natCode 2) (funP p)) (ap1 triF (pL p)) (ap1 triF (pR p))
      gToR = compI pG0 toRdisp_G0
      gD2  = impEqTrans (ap1 d2tag opk) (ap1 Fst (pR p)) (natCode 2) (gWeak Gam (d2tag_bare p ne)) pHd2
      gLab = impEqTrans (ap1 d2labTag opk) (ap1 Fst (ap1 Fst (ap1 Snd (pR p)))) (natCode m) (gWeak Gam (d2labTag_bare p ne)) pLabM
      fires =
        impEqTrans (ap1 R_disp opk) (ap1 R_mid opk) (ap1 br_Rcong_cell opk)
          (fork_false_to_snd_imp Gam br_Rb_cell R_mid (C natEqF d2tag (constN 1)) opk
             (natEqSkip_imp Gam d2tag 2 1 opk (wn 2 1 (\ ())) gD2))
          (fork_false_to_snd_imp Gam R_inner br_Rcong_cell (C natEqF d2labTag (constN 1)) opk
             (natEqSkip_imp Gam d2labTag m 1 opk (wn m 1 m1) gLab))
      full = impEqTrans (ap1 triF p) (ap1 R_disp opk) rhs gToR
               (impEqTrans (ap1 R_disp opk) (ap1 br_Rcong_cell opk) rhs fires (gWeak Gam (br_Rcong_val p ne)))
  in cnjCurry (cnjCurry (cnjCurry (cnjCurry full)))

-- (B) pR p an ap1c node with non-cSuc fun:  Fst(pR p)=2 , dtag=ap1c , funhead = m != 3.
triF_op_ap2c_Rcong_ap1cNotSuc_imp : (p : Term) -> Deriv (neg (eqF p O)) -> (m : Nat) -> ((Eq m 3) -> Empty) ->
  Deriv (imp (neg (eqF (ap1 Fst p) (natCode 1)))
             (imp (eqF (ap1 Fst (dtag p)) dgAp2c)
                  (imp (eqF (ap1 Fst (funP p)) (natCode 8))
                       (imp (eqF (ap1 Fst (pR p)) (natCode 2))
                            (imp (eqF (ap1 Fst (ap1 Fst (ap1 Snd (pR p)))) (natCode 1))
                                 (imp (eqF (ap1 Fst (ap1 Snd (ap1 Fst (ap1 Snd (pR p))))) (natCode m))
                                      (eqF (ap1 triF p) (binNode (ap2 Pair (natCode 2) (funP p)) (ap1 triF (pL p)) (ap1 triF (pR p))))))))))
triF_op_ap2c_Rcong_ap1cNotSuc_imp p ne m m3 =
  let open RecNode p ne
      hd2node : Formula
      hd2node = eqF (ap1 Fst (pR p)) (natCode 2)
      hlabTag : Formula
      hlabTag = eqF (ap1 Fst (ap1 Fst (ap1 Snd (pR p)))) (natCode 1)
      hfunM : Formula
      hfunM = eqF (ap1 Fst (ap1 Snd (ap1 Fst (ap1 Snd (pR p))))) (natCode m)
      L1 = Cnj Gam0 hd2node
      L2 = Cnj L1 hlabTag
      Gam = Cnj L2 hfunM
      pG0   = compI (cnjL L2 hfunM) (compI (cnjL L1 hlabTag) (cnjL Gam0 hd2node))
      pHd2  = compI (cnjL L2 hfunM) (compI (cnjL L1 hlabTag) (cnjR Gam0 hd2node))
      pLab  = compI (cnjL L2 hfunM) (cnjR L1 hlabTag)
      pFunM = cnjR L2 hfunM
      rhs = binNode (ap2 Pair (natCode 2) (funP p)) (ap1 triF (pL p)) (ap1 triF (pR p))
      gToR = compI pG0 toRdisp_G0
      gD2  = impEqTrans (ap1 d2tag opk) (ap1 Fst (pR p)) (natCode 2) (gWeak Gam (d2tag_bare p ne)) pHd2
      gLab = impEqTrans (ap1 d2labTag opk) (ap1 Fst (ap1 Fst (ap1 Snd (pR p)))) (natCode 1) (gWeak Gam (d2labTag_bare p ne)) pLab
      gFun = impEqTrans (ap1 d2FunHd opk) (ap1 Fst (ap1 Snd (ap1 Fst (ap1 Snd (pR p))))) (natCode m) (gWeak Gam (d2FunHd_bare p ne)) pFunM
      fires =
        impEqTrans (ap1 R_disp opk) (ap1 R_mid opk) (ap1 br_Rcong_cell opk)
          (fork_false_to_snd_imp Gam br_Rb_cell R_mid (C natEqF d2tag (constN 1)) opk
             (natEqSkip_imp Gam d2tag 2 1 opk (wn 2 1 (\ ())) gD2))
          (impEqTrans (ap1 R_mid opk) (ap1 R_inner opk) (ap1 br_Rcong_cell opk)
            (fork_true_to_fst_imp Gam R_inner br_Rcong_cell (C natEqF d2labTag (constN 1)) opk
               (natEqFire_imp Gam d2labTag 1 opk gLab))
            (fork_false_to_snd_imp Gam br_Rs_cell br_Rcong_cell (C natEqF d2FunHd (constN 3)) opk
               (natEqSkip_imp Gam d2FunHd m 3 opk (wn m 3 m3) gFun)))
      full = impEqTrans (ap1 triF p) (ap1 R_disp opk) rhs gToR
               (impEqTrans (ap1 R_disp opk) (ap1 br_Rcong_cell opk) rhs fires (gWeak Gam (br_Rcong_val p ne)))
  in cnjCurry (cnjCurry (cnjCurry (cnjCurry (cnjCurry full))))
