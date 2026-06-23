{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.PrTriUOpaque2 -- the OPAQUE depth-2 ap2c-cRec triangle equations (the
-- critical-pair case deferred from T4.PrTriUOpaque), mirroring T4.PrTri2 onto
-- the harness-recovered code p.  An ap2c node carrying a cRec funcode
-- (Fst(funP p) = 8) sub-dispatches on the RIGHT child pR p:
--
--   pR p a leaf (Fst(pR p)=1)            => triF p = derRb-shaped
--   pR p = ap1c cSuc .. (node, dtag=ap1c, funhead=cSuc)
--                                        => triF p = derRs-shaped
--   else                                 => ap2c-cRec congruence residual
--
-- The cell values are stated with the OPAQUE bundle  Snd (funP p)  / funP p
-- (NOT reconstructed components); the third Rs arm is  derLF (triF (pR p))
-- (= the grandchild, reduced downstream).  Together with PrTriUOpaque these
-- are ALL the opaque triF equations.
--
-- No holes, no postulates, no termination warnings (only the benign
-- RuleInst3:328 unreachable-clauses warning); --safe --without-K --exact-split.

module T4.PrTriUOpaque2 where

open import T4.Base

open import T4.PrDerCode using ( dgAp1c ; dgAp2c )
open import T4.PrCodeObj using ( cRec ; tgSuc ; tgRec )
open import T4.PrDev using ( mkAp2 ; mkAp2_val ; idxTest_fire ; idxTest_skip )
open import T4.PrTri
  using ( triF ; mkLabel ; mkLeafD ; mkLabel_val ; mkLeafD_val
        ; derTagIdx ; derBunIdx ; funHd ; bunSnd ; triFL ; triFR ; derLF
        ; ap1Cell ; ap2Cell ; br_v_cell ; R_disp ; R_mid ; R_inner
        ; br_Rb_cell ; br_Rs_cell ; br_Rcong_cell
        ; d2tag ; d2lab ; d2labTag ; d2FunHd
        ; testTag ; tri_l2 ; tri_l3 ; cellNodeTri )
open import T4.PrTriUOpaque using ( funP ; recBunSnd )

open import T4.PrDerCode using ( derLeaf )
open import T4.DerCodeS using ( dtag ; pL ; pR )
open import T4.BinTree using ( binNode ; nIdx ; lIdx ; rIdx )
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
  triStepU : Fun1
  triStepU = stepOf mkLeafD cellNodeTri
open T4.OpaqueHarness.H triStepU

------------------------------------------------------------------------
-- SECTION 1.  Harness recovery helpers (mirror PrTriUOpaque's private block).

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
    Deriv (eqF (ap1 triStepU (opkg p)) (ap1 cellNodeTri (opkg p)))
  toNode p ne nl =
    fork_false_to_snd mkLeafD cellNodeTri (C natEqF get_tag (constN 1)) (opkg p)
      (ruleTrans (test1At p ne) nl)

  recTag : (p : Term) -> Deriv (neg (eqF p O)) -> {tg : Term} ->
    Deriv (eqF (ap1 Fst (dtag p)) tg) -> Deriv (eqF (ap1 derTagIdx (opkg p)) tg)
  recTag p ne htag =
    ruleTrans (compose1U_eq Fst nIdx (opkg p)) (ruleTrans (cong1 Fst (op_nIdx p ne)) htag)

  recBun : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 derBunIdx (opkg p)) (funP p))
  recBun p ne = ruleTrans (compose1U_eq Snd nIdx (opkg p)) (cong1 Snd (op_nIdx p ne))

  recFunHd : (p : Term) -> Deriv (neg (eqF p O)) -> {hh : Term} ->
    Deriv (eqF (ap1 Fst (funP p)) hh) -> Deriv (eqF (ap1 funHd (opkg p)) hh)
  recFunHd p ne hf = ruleTrans (compose1U_eq Fst derBunIdx (opkg p)) (ruleTrans (cong1 Fst (recBun p ne)) hf)

  recPL : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 triFL (opkg p)) (ap1 triF (pL p)))
  recPL p ne = lookup_op Z triStepU lIdx (ap1 predecessor p) (pL p) (op_pL p ne) (pLValueBound p ne)
  recPR : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 triFR (opkg p)) (ap1 triF (pR p)))
  recPR p ne = lookup_op Z triStepU rIdx (ap1 predecessor p) (pR p) (op_pR p ne) (pRValueBound p ne)

  toCell : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) ->
    Deriv (eqF (ap1 triF p) (ap1 cellNodeTri (opkg p)))
  toCell p ne nl = ruleTrans (opUnfold p ne) (toNode p ne nl)

  w21 : NatNeqWitness 2 1
  w21 = decideNatNeq 2 1 (\ ())
  w87 : NatNeqWitness 8 7
  w87 = decideNatNeq 8 7 (\ ())
  wn : (m k : Nat) -> ((Eq m k) -> Empty) -> NatNeqWitness m k
  wn m k pf = decideNatNeq m k pf

  -- to R_disp : triF p = R_disp(opkg p), given dtag p = dgAp2c and Fst(funP p)=8.
  toRdisp : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) ->
    Deriv (eqF (ap1 Fst (dtag p)) dgAp2c) ->
    Deriv (eqF (ap1 Fst (funP p)) (natCode 8)) ->
    Deriv (eqF (ap1 triF p) (ap1 R_disp (opkg p)))
  toRdisp p ne nl htag hf8 =
    let opk = opkg p
        tg = recTag p ne htag
        hF = recFunHd p ne hf8
        to_ap2 =
          ruleTrans (fork_false_to_snd ap1Cell tri_l2 (testTag 1) opk (idxTest_skip derTagIdx 2 1 opk w21 tg))
                    (fork_true_to_fst ap2Cell tri_l3 (testTag 2) opk (idxTest_fire derTagIdx 2 opk tg))
        to_R = fork_false_to_snd br_v_cell R_disp (C natEqF funHd (constN 7)) opk
                 (idxTest_skip funHd 8 7 opk w87 hF)
    in ruleTrans (toCell p ne nl) (ruleTrans to_ap2 to_R)

  -- d2 = pR p readers.
  recD2tag : (p : Term) -> Deriv (neg (eqF p O)) -> {v : Term} ->
    Deriv (eqF (ap1 Fst (pR p)) v) -> Deriv (eqF (ap1 d2tag (opkg p)) v)
  recD2tag p ne h =
    ruleTrans (compose1U_eq Fst rIdx (opkg p)) (ruleTrans (cong1 Fst (op_pR p ne)) h)

  d2lab_eq : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 d2lab (opkg p)) (ap1 Fst (ap1 Snd (pR p))))
  d2lab_eq p ne =
    ruleTrans (compose1U_eq Fst (compose1U Snd rIdx) (opkg p))
      (cong1 Fst (ruleTrans (compose1U_eq Snd rIdx (opkg p)) (cong1 Snd (op_pR p ne))))

  recD2labTag : (p : Term) -> Deriv (neg (eqF p O)) -> {v : Term} ->
    Deriv (eqF (ap1 Fst (ap1 Fst (ap1 Snd (pR p)))) v) ->
    Deriv (eqF (ap1 d2labTag (opkg p)) v)
  recD2labTag p ne h =
    ruleTrans (compose1U_eq Fst d2lab (opkg p)) (ruleTrans (cong1 Fst (d2lab_eq p ne)) h)

  recD2FunHd : (p : Term) -> Deriv (neg (eqF p O)) -> {v : Term} ->
    Deriv (eqF (ap1 Fst (ap1 Snd (ap1 Fst (ap1 Snd (pR p))))) v) ->
    Deriv (eqF (ap1 d2FunHd (opkg p)) v)
  recD2FunHd p ne h =
    ruleTrans (compose1U_eq Fst (compose1U Snd d2lab) (opkg p))
      (ruleTrans (cong1 Fst (ruleTrans (compose1U_eq Snd d2lab (opkg p)) (cong1 Snd (d2lab_eq p ne)))) h)

------------------------------------------------------------------------
-- SECTION 2.  Rb:  pR p a leaf  (Fst (pR p) = 1).

triF_op_ap2c_Rb : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) ->
  Deriv (eqF (ap1 Fst (dtag p)) dgAp2c) ->
  Deriv (eqF (ap1 Fst (funP p)) (natCode 8)) ->
  Deriv (eqF (ap1 Fst (pR p)) (natCode 1)) ->
  Deriv (eqF (ap1 triF p)
             (binNode (ap2 Pair (natCode 7) (ap1 Snd (funP p))) (ap1 triF (pL p)) derLeaf))
triF_op_ap2c_Rb p ne nl htag hf8 hd2 =
  let opk = opkg p
      fires = fork_true_to_fst br_Rb_cell R_mid (C natEqF d2tag (constN 1)) opk
                (idxTest_fire d2tag 1 opk (recD2tag p ne hd2))
      val = mkAp2_val (mkLabel 7 bunSnd) triFL mkLeafD opk
              (ap2 Pair (natCode 7) (ap1 Snd (funP p))) (ap1 triF (pL p)) derLeaf
              (mkLabel_val 7 bunSnd opk (ap1 Snd (funP p)) (recBunSnd p ne)) (recPL p ne) (mkLeafD_val opk)
  in ruleTrans (toRdisp p ne nl htag hf8) (ruleTrans fires val)

------------------------------------------------------------------------
-- SECTION 3.  Rs:  pR p = ap1c cSuc ..  (node, dtag = ap1c, funhead = cSuc).

triF_op_ap2c_Rs : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) ->
  Deriv (eqF (ap1 Fst (dtag p)) dgAp2c) ->
  Deriv (eqF (ap1 Fst (funP p)) (natCode 8)) ->
  Deriv (eqF (ap1 Fst (pR p)) (natCode 2)) ->
  Deriv (eqF (ap1 Fst (ap1 Fst (ap1 Snd (pR p)))) (natCode 1)) ->
  Deriv (eqF (ap1 Fst (ap1 Snd (ap1 Fst (ap1 Snd (pR p))))) (natCode 3)) ->
  Deriv (eqF (ap1 triF p)
             (binNode (ap2 Pair (natCode 8) (ap1 Snd (funP p))) (ap1 triF (pL p))
                      (ap1 derLF (ap1 triF (pR p)))))
triF_op_ap2c_Rs p ne nl htag hf8 hd2node hlabTag hfun =
  let opk = opkg p
      fires =
        ruleTrans (fork_false_to_snd br_Rb_cell R_mid (C natEqF d2tag (constN 1)) opk
                     (idxTest_skip d2tag 2 1 opk w21 (recD2tag p ne hd2node)))
          (ruleTrans (fork_true_to_fst R_inner br_Rcong_cell (C natEqF d2labTag (constN 1)) opk
                       (idxTest_fire d2labTag 1 opk (recD2labTag p ne hlabTag)))
                     (fork_true_to_fst br_Rs_cell br_Rcong_cell (C natEqF d2FunHd (constN 3)) opk
                       (idxTest_fire d2FunHd 3 opk (recD2FunHd p ne hfun))))
      thirdArm : Deriv (eqF (ap1 (compose1U derLF triFR) opk) (ap1 derLF (ap1 triF (pR p))))
      thirdArm = ruleTrans (compose1U_eq derLF triFR opk) (cong1 derLF (recPR p ne))
      val = mkAp2_val (mkLabel 8 bunSnd) triFL (compose1U derLF triFR) opk
              (ap2 Pair (natCode 8) (ap1 Snd (funP p))) (ap1 triF (pL p)) (ap1 derLF (ap1 triF (pR p)))
              (mkLabel_val 8 bunSnd opk (ap1 Snd (funP p)) (recBunSnd p ne)) (recPL p ne) thirdArm
  in ruleTrans (toRdisp p ne nl htag hf8) (ruleTrans fires val)

------------------------------------------------------------------------
-- SECTION 4.  R-congruence "else".

private
  br_Rcong_val : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 br_Rcong_cell (opkg p))
               (binNode (ap2 Pair (natCode 2) (funP p)) (ap1 triF (pL p)) (ap1 triF (pR p))))
  br_Rcong_val p ne =
    mkAp2_val (mkLabel 2 derBunIdx) triFL triFR (opkg p)
      (ap2 Pair (natCode 2) (funP p)) (ap1 triF (pL p)) (ap1 triF (pR p))
      (mkLabel_val 2 derBunIdx (opkg p) (funP p) (recBun p ne)) (recPL p ne) (recPR p ne)

-- (A) pR p a non-ap1c node:  Fst(pR p)=2 , dtag(pR p)-tag = m != 1.
triF_op_ap2c_Rcong_notAp1c : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) ->
  Deriv (eqF (ap1 Fst (dtag p)) dgAp2c) ->
  Deriv (eqF (ap1 Fst (funP p)) (natCode 8)) ->
  Deriv (eqF (ap1 Fst (pR p)) (natCode 2)) -> (m : Nat) ->
  Deriv (eqF (ap1 Fst (ap1 Fst (ap1 Snd (pR p)))) (natCode m)) -> ((Eq m 1) -> Empty) ->
  Deriv (eqF (ap1 triF p)
             (binNode (ap2 Pair (natCode 2) (funP p)) (ap1 triF (pL p)) (ap1 triF (pR p))))
triF_op_ap2c_Rcong_notAp1c p ne nl htag hf8 hd2node m hlabTagM m1 =
  let opk = opkg p
      fires =
        ruleTrans (fork_false_to_snd br_Rb_cell R_mid (C natEqF d2tag (constN 1)) opk
                     (idxTest_skip d2tag 2 1 opk w21 (recD2tag p ne hd2node)))
                  (fork_false_to_snd R_inner br_Rcong_cell (C natEqF d2labTag (constN 1)) opk
                     (idxTest_skip d2labTag m 1 opk (wn m 1 m1) (recD2labTag p ne hlabTagM)))
  in ruleTrans (toRdisp p ne nl htag hf8) (ruleTrans fires (br_Rcong_val p ne))

-- (B) pR p an ap1c node with non-cSuc fun:  Fst(pR p)=2 , dtag=ap1c , funhead = m != 3.
triF_op_ap2c_Rcong_ap1cNotSuc : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) ->
  Deriv (eqF (ap1 Fst (dtag p)) dgAp2c) ->
  Deriv (eqF (ap1 Fst (funP p)) (natCode 8)) ->
  Deriv (eqF (ap1 Fst (pR p)) (natCode 2)) ->
  Deriv (eqF (ap1 Fst (ap1 Fst (ap1 Snd (pR p)))) (natCode 1)) -> (m : Nat) ->
  Deriv (eqF (ap1 Fst (ap1 Snd (ap1 Fst (ap1 Snd (pR p))))) (natCode m)) -> ((Eq m 3) -> Empty) ->
  Deriv (eqF (ap1 triF p)
             (binNode (ap2 Pair (natCode 2) (funP p)) (ap1 triF (pL p)) (ap1 triF (pR p))))
triF_op_ap2c_Rcong_ap1cNotSuc p ne nl htag hf8 hd2node hlabTag m hfunM m3 =
  let opk = opkg p
      fires =
        ruleTrans (fork_false_to_snd br_Rb_cell R_mid (C natEqF d2tag (constN 1)) opk
                     (idxTest_skip d2tag 2 1 opk w21 (recD2tag p ne hd2node)))
          (ruleTrans (fork_true_to_fst R_inner br_Rcong_cell (C natEqF d2labTag (constN 1)) opk
                       (idxTest_fire d2labTag 1 opk (recD2labTag p ne hlabTag)))
                     (fork_false_to_snd br_Rs_cell br_Rcong_cell (C natEqF d2FunHd (constN 3)) opk
                       (idxTest_skip d2FunHd m 3 opk (wn m 3 m3) (recD2FunHd p ne hfunM))))
  in ruleTrans (toRdisp p ne nl htag hf8) (ruleTrans fires (br_Rcong_val p ne))
