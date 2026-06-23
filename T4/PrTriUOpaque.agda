{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.PrTriUOpaque -- the OPAQUE triF equations over arbitrary codes p : Term,
-- the triangle-map analogue of T4.PrSrcUOpaque.  triF p is computed from p's
-- projections via the harness (recovers triF (pL p) / triF (pR p)); the ap1c
-- case sub-dispatches on the carried fun's head Fst(funP p) -> o/u/s/C.
-- This file covers all cases EXCEPT the depth-2 ap2c-cRec (Rb/Rs/Rcong), which
-- (mirroring the PrTri / PrTri2 split) go in a follow-up.
--
--   reflO  => triF p = derLeaf
--   ap1c, Fst(funP p)=3 (s) => triF p = ap1c cSuc (triF (pL p))
--   ap1c, Fst(funP p)=4 (o) => triF p = derO (triF (pL p))
--   ap1c, Fst(funP p)=5 (u) => triF p = derU (triF (pL p))
--   ap1c, Fst(funP p)=6 (C) => triF p = derC (gP p)(h1P p)(h2P p) (triF (pL p))
--   ap2c, Fst(funP p)=7 (v) => triF p = derV (triF (pL p)) (triF (pR p))
--   rO  => triF p = derLeaf      rU  => triF p = triF (pL p)     rV  => triF p = triF (pR p)
--   rC  => triF p = ap2c (gP p)(ap1c (h1P p)(triF pL))(ap1c (h2P p)(triF pL))
--   rRb => triF p = ap1c (gP p)(triF pL)
--   rRs => triF p = ap2c (h1P p)(ap2c (h2P p)(triF pL)(triF pR))(ap2c (cRec (gP p)(h1P p)(h2P p))(triF pL)(triF pR))
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.PrTriUOpaque where

open import T4.Base

open import T4.PrDerCode using ( dgReflO ; dgAp1c ; dgAp2c ; dgRo ; dgRu ; dgRv ; dgRC ; dgRb ; dgRs )
open import T4.PrCodeObj using ( cSuc ; cRec ; tgSuc ; tgZero ; tgId ; tgComp ; tgProj )
open import T4.PrDev using ( mkAp2 ; mkAp2_val ; idxTest_fire ; idxTest_skip )
open import T4.PrTri
  using ( triF ; mkLabel ; mkLeafD ; mkLabel_val ; mkLeafD_val
        ; derTagIdx ; derBunIdx ; funHd ; bunSnd ; bunH1' ; bunH2' ; triFL ; triFR
        ; br_s_cell ; br_o_cell ; br_u_cell ; br_C_cell ; ap1_l2 ; ap1_l3 ; ap1Cell
        ; br_v_cell ; R_disp ; ap2Cell
        ; o_cell ; u_cell ; v_cell ; C_cell ; Rb_cell ; Rs_cell
        ; testTag ; tri_l2 ; tri_l3 ; tri_l4 ; tri_l5 ; tri_l6 ; tri_l7 ; cellNodeTri )

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
-- SECTION 0.  Projection terms.

funP : Term -> Term
funP p = ap1 Snd (dtag p)
gP : Term -> Term
gP p = ap1 Fst (funP p)
h1P : Term -> Term
h1P p = ap1 Fst (ap1 Snd (funP p))
h2P : Term -> Term
h2P p = ap1 Snd (ap1 Snd (funP p))

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

  recG : (p : Term) -> Deriv (neg (eqF p O)) -> Deriv (eqF (ap1 funHd (opkg p)) (gP p))
  recG p ne = ruleTrans (compose1U_eq Fst derBunIdx (opkg p)) (cong1 Fst (recBun p ne))
  recH1 : (p : Term) -> Deriv (neg (eqF p O)) -> Deriv (eqF (ap1 bunH1' (opkg p)) (h1P p))
  recH1 p ne = ruleTrans (compose1U_eq Fst bunSnd (opkg p))
                 (cong1 Fst (ruleTrans (compose1U_eq Snd derBunIdx (opkg p)) (cong1 Snd (recBun p ne))))
  recH2 : (p : Term) -> Deriv (neg (eqF p O)) -> Deriv (eqF (ap1 bunH2' (opkg p)) (h2P p))
  recH2 p ne = ruleTrans (compose1U_eq Snd bunSnd (opkg p))
                 (cong1 Snd (ruleTrans (compose1U_eq Snd derBunIdx (opkg p)) (cong1 Snd (recBun p ne))))

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

  -- fire the outer dispatch to ap1Cell (tag 1) / ap2Cell (tag 2).
  toAp1Cell : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) -> Deriv (eqF (ap1 Fst (dtag p)) dgAp1c) ->
    Deriv (eqF (ap1 triF p) (ap1 ap1Cell (opkg p)))
  toAp1Cell p ne nl htag =
    ruleTrans (toCell p ne nl)
      (fork_true_to_fst ap1Cell tri_l2 (testTag 1) (opkg p) (idxTest_fire derTagIdx 1 (opkg p) (recTag p ne htag)))

  toAp2Cell : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) -> Deriv (eqF (ap1 Fst (dtag p)) dgAp2c) ->
    Deriv (eqF (ap1 triF p) (ap1 ap2Cell (opkg p)))
  toAp2Cell p ne nl htag =
    let opk = opkg p
        tg = recTag p ne htag
    in ruleTrans (toCell p ne nl)
         (ruleTrans (fork_false_to_snd ap1Cell tri_l2 (testTag 1) opk (idxTest_skip derTagIdx 2 1 opk w21 tg))
                    (fork_true_to_fst ap2Cell tri_l3 (testTag 2) opk (idxTest_fire derTagIdx 2 opk tg)))
    where w21 = decideNatNeq 2 1 (\ ())

  wn : (m k : Nat) -> ((Eq m k) -> Empty) -> NatNeqWitness m k
  wn m k pf = decideNatNeq m k pf
  w21 : NatNeqWitness 2 1
  w21 = decideNatNeq 2 1 (\ ())

------------------------------------------------------------------------
-- SECTION 2.  Leaf.

triF_op_reflO : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap1 Fst p) (natCode 1)) -> Deriv (eqF (ap1 triF p) (ap1 mkLeafD (opkg p)))
triF_op_reflO p ne htagB =
  let opk = opkg p
      t1_fire = ruleTrans (test1At p ne) (ruleTrans (congL natEqF (natCode 1) htagB) (natEq_eq 1))
      cell_fires = fork_true_to_fst mkLeafD cellNodeTri (C natEqF get_tag (constN 1)) opk t1_fire
  in ruleTrans (opUnfold p ne) cell_fires

-- the leaf value is derLeaf; expose it.
triF_op_reflO_val : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap1 Fst p) (natCode 1)) -> Deriv (eqF (ap1 triF p) T4.PrDerCode.derLeaf)
triF_op_reflO_val p ne htagB = ruleTrans (triF_op_reflO p ne htagB) (mkLeafD_val (opkg p))

------------------------------------------------------------------------
-- SECTION 3.  ap1c sub-dispatch (on Fst(funP p)).

triF_op_ap1c_o : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) -> Deriv (eqF (ap1 Fst (dtag p)) dgAp1c) ->
  Deriv (eqF (ap1 Fst (funP p)) (natCode 4)) ->
  Deriv (eqF (ap1 triF p) (T4.PrDerCode.derO (ap1 triF (pL p))))
triF_op_ap1c_o p ne nl htag hf =
  let opk = opkg p
      hF = recFunHd p ne hf
      fires = fork_true_to_fst br_o_cell ap1_l2 (C natEqF funHd (constN 4)) opk (idxTest_fire funHd 4 opk hF)
      val = mkAp2_val (mkLabel 3 Z) triFL mkLeafD opk (ap2 Pair (natCode 3) O) (ap1 triF (pL p)) T4.PrDerCode.derLeaf
              (mkLabel_val 3 Z opk O (axZ opk)) (recPL p ne) (mkLeafD_val opk)
  in ruleTrans (toAp1Cell p ne nl htag) (ruleTrans fires val)

triF_op_ap1c_u : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) -> Deriv (eqF (ap1 Fst (dtag p)) dgAp1c) ->
  Deriv (eqF (ap1 Fst (funP p)) (natCode 5)) ->
  Deriv (eqF (ap1 triF p) (T4.PrDerCode.derU (ap1 triF (pL p))))
triF_op_ap1c_u p ne nl htag hf =
  let opk = opkg p
      hF = recFunHd p ne hf
      fires =
        ruleTrans (fork_false_to_snd br_o_cell ap1_l2 (C natEqF funHd (constN 4)) opk (idxTest_skip funHd 5 4 opk (wn 5 4 (\ ())) hF))
                  (fork_true_to_fst br_u_cell ap1_l3 (C natEqF funHd (constN 5)) opk (idxTest_fire funHd 5 opk hF))
      val = mkAp2_val (mkLabel 4 Z) triFL mkLeafD opk (ap2 Pair (natCode 4) O) (ap1 triF (pL p)) T4.PrDerCode.derLeaf
              (mkLabel_val 4 Z opk O (axZ opk)) (recPL p ne) (mkLeafD_val opk)
  in ruleTrans (toAp1Cell p ne nl htag) (ruleTrans fires val)

-- ‼ ap1c-C CONGRUENCE: triF p = derC-shaped node with bundle = Snd(funP p)
-- (the OPAQUE carried fun's bundle), NOT reconstructed components.  Relating
-- Snd(funP p) to a cComp needs funcode validation (wfFun) downstream.
recBunSnd : (q : Term) -> Deriv (neg (eqF q O)) -> Deriv (eqF (ap1 bunSnd (opkg q)) (ap1 Snd (funP q)))
recBunSnd q ne = ruleTrans (compose1U_eq Snd derBunIdx (opkg q)) (cong1 Snd (recBun q ne))

triF_op_ap1c_C : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) -> Deriv (eqF (ap1 Fst (dtag p)) dgAp1c) ->
  Deriv (eqF (ap1 Fst (funP p)) (natCode 6)) ->
  Deriv (eqF (ap1 triF p) (binNode (ap2 Pair (natCode 6) (ap1 Snd (funP p))) (ap1 triF (pL p)) derLeaf))
triF_op_ap1c_C p ne nl htag hf =
  let opk = opkg p
      hF = recFunHd p ne hf
      fires =
        ruleTrans (fork_false_to_snd br_o_cell ap1_l2 (C natEqF funHd (constN 4)) opk (idxTest_skip funHd 6 4 opk (wn 6 4 (\ ())) hF))
          (ruleTrans (fork_false_to_snd br_u_cell ap1_l3 (C natEqF funHd (constN 5)) opk (idxTest_skip funHd 6 5 opk (wn 6 5 (\ ())) hF))
                     (fork_true_to_fst br_C_cell br_s_cell (C natEqF funHd (constN 6)) opk (idxTest_fire funHd 6 opk hF)))
      val = mkAp2_val (mkLabel 6 bunSnd) triFL mkLeafD opk (ap2 Pair (natCode 6) (ap1 Snd (funP p))) (ap1 triF (pL p)) derLeaf
              (mkLabel_val 6 bunSnd opk (ap1 Snd (funP p)) (recBunSnd p ne)) (recPL p ne) (mkLeafD_val opk)
  in ruleTrans (toAp1Cell p ne nl htag) (ruleTrans fires val)

triF_op_ap1c_s : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) -> Deriv (eqF (ap1 Fst (dtag p)) dgAp1c) ->
  Deriv (eqF (ap1 Fst (funP p)) (natCode 3)) ->
  Deriv (eqF (ap1 triF p) (T4.PrDerCode.ap1c cSuc (ap1 triF (pL p))))
triF_op_ap1c_s p ne nl htag hf =
  let opk = opkg p
      hF = recFunHd p ne hf
      fires =
        ruleTrans (fork_false_to_snd br_o_cell ap1_l2 (C natEqF funHd (constN 4)) opk (idxTest_skip funHd 3 4 opk (wn 3 4 (\ ())) hF))
          (ruleTrans (fork_false_to_snd br_u_cell ap1_l3 (C natEqF funHd (constN 5)) opk (idxTest_skip funHd 3 5 opk (wn 3 5 (\ ())) hF))
                     (fork_false_to_snd br_C_cell br_s_cell (C natEqF funHd (constN 6)) opk (idxTest_skip funHd 3 6 opk (wn 3 6 (\ ())) hF)))
      val = mkAp2_val (mkLabel 1 T4.PrDev.cSucF) triFL mkLeafD opk (ap2 Pair (natCode 1) cSuc) (ap1 triF (pL p)) T4.PrDerCode.derLeaf
              (mkLabel_val 1 T4.PrDev.cSucF opk cSuc (T4.PrDev.cSucF_val opk)) (recPL p ne) (mkLeafD_val opk)
  in ruleTrans (toAp1Cell p ne nl htag) (ruleTrans fires val)

------------------------------------------------------------------------
-- SECTION 4.  ap2c v-case.

triF_op_ap2c_v : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) -> Deriv (eqF (ap1 Fst (dtag p)) dgAp2c) ->
  Deriv (eqF (ap1 Fst (funP p)) (natCode 7)) ->
  Deriv (eqF (ap1 triF p) (T4.PrDerCode.derV (ap1 triF (pL p)) (ap1 triF (pR p))))
triF_op_ap2c_v p ne nl htag hf =
  let opk = opkg p
      hF = recFunHd p ne hf
      fires = fork_true_to_fst br_v_cell R_disp (C natEqF funHd (constN 7)) opk (idxTest_fire funHd 7 opk hF)
      val = mkAp2_val (mkLabel 5 Z) triFL triFR opk (ap2 Pair (natCode 5) O) (ap1 triF (pL p)) (ap1 triF (pR p))
              (mkLabel_val 5 Z opk O (axZ opk)) (recPL p ne) (recPR p ne)
  in ruleTrans (toAp2Cell p ne nl htag) (ruleTrans fires val)

------------------------------------------------------------------------
-- SECTION 5.  Redex tags (3..8).

private
  -- fire the outer dispatch through to tag k's cell.
  toRedex1 : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) -> (k : Nat) ->
    Deriv (eqF (ap1 Fst (dtag p)) (natCode k)) -> Deriv (eqF (ap1 derTagIdx (opkg p)) (natCode k))
  toRedex1 p ne nl k htag = recTag p ne htag

triF_op_O : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) -> Deriv (eqF (ap1 Fst (dtag p)) dgRo) ->
  Deriv (eqF (ap1 triF p) (ap1 mkLeafD (opkg p)))
triF_op_O p ne nl htag =
  let opk = opkg p
      tg = recTag p ne htag
      fires =
        ruleTrans (fork_false_to_snd ap1Cell tri_l2 (testTag 1) opk (idxTest_skip derTagIdx 3 1 opk (wn 3 1 (\ ())) tg))
          (ruleTrans (fork_false_to_snd ap2Cell tri_l3 (testTag 2) opk (idxTest_skip derTagIdx 3 2 opk (wn 3 2 (\ ())) tg))
                     (fork_true_to_fst o_cell tri_l4 (testTag 3) opk (idxTest_fire derTagIdx 3 opk tg)))
  in ruleTrans (toCell p ne nl) fires

triF_op_U : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) -> Deriv (eqF (ap1 Fst (dtag p)) dgRu) ->
  Deriv (eqF (ap1 triF p) (ap1 triF (pL p)))
triF_op_U p ne nl htag =
  let opk = opkg p
      tg = recTag p ne htag
      fires =
        ruleTrans (fork_false_to_snd ap1Cell tri_l2 (testTag 1) opk (idxTest_skip derTagIdx 4 1 opk (wn 4 1 (\ ())) tg))
          (ruleTrans (fork_false_to_snd ap2Cell tri_l3 (testTag 2) opk (idxTest_skip derTagIdx 4 2 opk (wn 4 2 (\ ())) tg))
            (ruleTrans (fork_false_to_snd o_cell tri_l4 (testTag 3) opk (idxTest_skip derTagIdx 4 3 opk (wn 4 3 (\ ())) tg))
                       (fork_true_to_fst u_cell tri_l5 (testTag 4) opk (idxTest_fire derTagIdx 4 opk tg))))
  in ruleTrans (toCell p ne nl) (ruleTrans fires (recPL p ne))

triF_op_V : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) -> Deriv (eqF (ap1 Fst (dtag p)) dgRv) ->
  Deriv (eqF (ap1 triF p) (ap1 triF (pR p)))
triF_op_V p ne nl htag =
  let opk = opkg p
      tg = recTag p ne htag
      fires =
        ruleTrans (fork_false_to_snd ap1Cell tri_l2 (testTag 1) opk (idxTest_skip derTagIdx 5 1 opk (wn 5 1 (\ ())) tg))
          (ruleTrans (fork_false_to_snd ap2Cell tri_l3 (testTag 2) opk (idxTest_skip derTagIdx 5 2 opk (wn 5 2 (\ ())) tg))
            (ruleTrans (fork_false_to_snd o_cell tri_l4 (testTag 3) opk (idxTest_skip derTagIdx 5 3 opk (wn 5 3 (\ ())) tg))
              (ruleTrans (fork_false_to_snd u_cell tri_l5 (testTag 4) opk (idxTest_skip derTagIdx 5 4 opk (wn 5 4 (\ ())) tg))
                         (fork_true_to_fst v_cell tri_l6 (testTag 5) opk (idxTest_fire derTagIdx 5 opk tg)))))
  in ruleTrans (toCell p ne nl) (ruleTrans fires (recPR p ne))

triF_op_C : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) -> Deriv (eqF (ap1 Fst (dtag p)) dgRC) ->
  Deriv (eqF (ap1 triF p)
             (T4.PrDerCode.ap2c (gP p) (T4.PrDerCode.ap1c (h1P p) (ap1 triF (pL p))) (T4.PrDerCode.ap1c (h2P p) (ap1 triF (pL p)))))
triF_op_C p ne nl htag =
  let opk = opkg p
      tg = recTag p ne htag
      fires =
        ruleTrans (fork_false_to_snd ap1Cell tri_l2 (testTag 1) opk (idxTest_skip derTagIdx 6 1 opk (wn 6 1 (\ ())) tg))
          (ruleTrans (fork_false_to_snd ap2Cell tri_l3 (testTag 2) opk (idxTest_skip derTagIdx 6 2 opk (wn 6 2 (\ ())) tg))
            (ruleTrans (fork_false_to_snd o_cell tri_l4 (testTag 3) opk (idxTest_skip derTagIdx 6 3 opk (wn 6 3 (\ ())) tg))
              (ruleTrans (fork_false_to_snd u_cell tri_l5 (testTag 4) opk (idxTest_skip derTagIdx 6 4 opk (wn 6 4 (\ ())) tg))
                (ruleTrans (fork_false_to_snd v_cell tri_l6 (testTag 5) opk (idxTest_skip derTagIdx 6 5 opk (wn 6 5 (\ ())) tg))
                           (fork_true_to_fst C_cell tri_l7 (testTag 6) opk (idxTest_fire derTagIdx 6 opk tg))))))
      armH1 = mkAp2_val (mkLabel 1 bunH1') triFL mkLeafD opk (ap2 Pair (natCode 1) (h1P p)) (ap1 triF (pL p)) T4.PrDerCode.derLeaf
                (mkLabel_val 1 bunH1' opk (h1P p) (recH1 p ne)) (recPL p ne) (mkLeafD_val opk)
      armH2 = mkAp2_val (mkLabel 1 bunH2') triFL mkLeafD opk (ap2 Pair (natCode 1) (h2P p)) (ap1 triF (pL p)) T4.PrDerCode.derLeaf
                (mkLabel_val 1 bunH2' opk (h2P p) (recH2 p ne)) (recPL p ne) (mkLeafD_val opk)
      val = mkAp2_val (mkLabel 2 funHd) (mkAp2 (mkLabel 1 bunH1') triFL mkLeafD) (mkAp2 (mkLabel 1 bunH2') triFL mkLeafD) opk
              (ap2 Pair (natCode 2) (gP p)) (T4.PrDerCode.ap1c (h1P p) (ap1 triF (pL p))) (T4.PrDerCode.ap1c (h2P p) (ap1 triF (pL p)))
              (mkLabel_val 2 funHd opk (gP p) (recG p ne)) armH1 armH2
  in ruleTrans (toCell p ne nl) (ruleTrans fires val)

triF_op_Rb : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) -> Deriv (eqF (ap1 Fst (dtag p)) dgRb) ->
  Deriv (eqF (ap1 triF p) (T4.PrDerCode.ap1c (gP p) (ap1 triF (pL p))))
triF_op_Rb p ne nl htag =
  let opk = opkg p
      tg = recTag p ne htag
      fires =
        ruleTrans (fork_false_to_snd ap1Cell tri_l2 (testTag 1) opk (idxTest_skip derTagIdx 7 1 opk (wn 7 1 (\ ())) tg))
          (ruleTrans (fork_false_to_snd ap2Cell tri_l3 (testTag 2) opk (idxTest_skip derTagIdx 7 2 opk (wn 7 2 (\ ())) tg))
            (ruleTrans (fork_false_to_snd o_cell tri_l4 (testTag 3) opk (idxTest_skip derTagIdx 7 3 opk (wn 7 3 (\ ())) tg))
              (ruleTrans (fork_false_to_snd u_cell tri_l5 (testTag 4) opk (idxTest_skip derTagIdx 7 4 opk (wn 7 4 (\ ())) tg))
                (ruleTrans (fork_false_to_snd v_cell tri_l6 (testTag 5) opk (idxTest_skip derTagIdx 7 5 opk (wn 7 5 (\ ())) tg))
                  (ruleTrans (fork_false_to_snd C_cell tri_l7 (testTag 6) opk (idxTest_skip derTagIdx 7 6 opk (wn 7 6 (\ ())) tg))
                             (fork_true_to_fst Rb_cell Rs_cell (testTag 7) opk (idxTest_fire derTagIdx 7 opk tg)))))))
      val = mkAp2_val (mkLabel 1 funHd) triFL mkLeafD opk (ap2 Pair (natCode 1) (gP p)) (ap1 triF (pL p)) T4.PrDerCode.derLeaf
              (mkLabel_val 1 funHd opk (gP p) (recG p ne)) (recPL p ne) (mkLeafD_val opk)
  in ruleTrans (toCell p ne nl) (ruleTrans fires val)

triF_op_Rs : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) -> Deriv (eqF (ap1 Fst (dtag p)) dgRs) ->
  Deriv (eqF (ap1 triF p)
             (T4.PrDerCode.ap2c (h1P p) (T4.PrDerCode.ap2c (h2P p) (ap1 triF (pL p)) (ap1 triF (pR p)))
                                (T4.PrDerCode.ap2c (ap2 Pair (natCode 8) (funP p)) (ap1 triF (pL p)) (ap1 triF (pR p)))))
triF_op_Rs p ne nl htag =
  let opk = opkg p
      tg = recTag p ne htag
      fires =
        ruleTrans (fork_false_to_snd ap1Cell tri_l2 (testTag 1) opk (idxTest_skip derTagIdx 8 1 opk (wn 8 1 (\ ())) tg))
          (ruleTrans (fork_false_to_snd ap2Cell tri_l3 (testTag 2) opk (idxTest_skip derTagIdx 8 2 opk (wn 8 2 (\ ())) tg))
            (ruleTrans (fork_false_to_snd o_cell tri_l4 (testTag 3) opk (idxTest_skip derTagIdx 8 3 opk (wn 8 3 (\ ())) tg))
              (ruleTrans (fork_false_to_snd u_cell tri_l5 (testTag 4) opk (idxTest_skip derTagIdx 8 4 opk (wn 8 4 (\ ())) tg))
                (ruleTrans (fork_false_to_snd v_cell tri_l6 (testTag 5) opk (idxTest_skip derTagIdx 8 5 opk (wn 8 5 (\ ())) tg))
                  (ruleTrans (fork_false_to_snd C_cell tri_l7 (testTag 6) opk (idxTest_skip derTagIdx 8 6 opk (wn 8 6 (\ ())) tg))
                             (fork_false_to_snd Rb_cell Rs_cell (testTag 7) opk (idxTest_skip derTagIdx 8 7 opk (wn 8 7 (\ ())) tg)))))))
      arm2 = mkAp2_val (mkLabel 2 bunH2') triFL triFR opk (ap2 Pair (natCode 2) (h2P p)) (ap1 triF (pL p)) (ap1 triF (pR p))
               (mkLabel_val 2 bunH2' opk (h2P p) (recH2 p ne)) (recPL p ne) (recPR p ne)
      recFun = mkLabel_val 2 (mkLabel 8 derBunIdx) opk (ap2 Pair (natCode 8) (funP p))
                 (mkLabel_val 8 derBunIdx opk (funP p) (recBun p ne))
      arm3 = mkAp2_val (mkLabel 2 (mkLabel 8 derBunIdx)) triFL triFR opk (ap2 Pair (natCode 2) (ap2 Pair (natCode 8) (funP p))) (ap1 triF (pL p)) (ap1 triF (pR p))
               recFun (recPL p ne) (recPR p ne)
      val = mkAp2_val (mkLabel 2 bunH1') (mkAp2 (mkLabel 2 bunH2') triFL triFR) (mkAp2 (mkLabel 2 (mkLabel 8 derBunIdx)) triFL triFR) opk
              (ap2 Pair (natCode 2) (h1P p)) (T4.PrDerCode.ap2c (h2P p) (ap1 triF (pL p)) (ap1 triF (pR p)))
              (T4.PrDerCode.ap2c (ap2 Pair (natCode 8) (funP p)) (ap1 triF (pL p)) (ap1 triF (pR p)))
              (mkLabel_val 2 bunH1' opk (h1P p) (recH1 p ne)) arm2 arm3
  in ruleTrans (toCell p ne nl) (ruleTrans fires val)
