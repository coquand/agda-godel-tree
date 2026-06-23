{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.DerTriUSuGam -- the GRANDCHILD Su unfold over the UNSIZED coding, with the
-- non-O hypothesis ne, the leaf-skip nl, and the tag htag all THREADED as facts
-- under an arbitrary conjunction context  Gam .  This is the one Su unfold that
-- must be applied to an OPAQUE child (the left child  pL p  of an Ad node in the
-- Ad_Su critical pair), where ne (pL p) is NOT available bare.  It composes the
-- ne-form harness (T4.OpaqueHarnessImp.Himp triStepU) + lookup_op_imp +
-- pLValueBound_imp + the ForkImp imp-form cascades, every step  imp Gam X .
--
--   triF_op_Su_gam Gam q gNe gNl gHtag :
--     imp Gam (triF q = derSu (triF (pL q)))
--
-- where gNe : imp Gam (q != O), gNl : imp Gam (natEqF (Fst q) 1 = O),
--       gHtag : imp Gam (dtag q = dgSu).
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.DerTriUSuGam where

open import T4.Base

open import T4.DerCode using ( derSu ; dgSu ; filler )
open import T4.DerCodeS using ( dtag ; pL ; pArg )
open import T4.DerTri
  using ( triF ; cellLeafTri ; cellNodeTri ; suNodeCell ; restAdTri ; cellLeafTri_at )
open import T4.DerSrc using ( testEq )
open import T4.ProgParse using ( get_tag )
open import T4.FoldRec using ( lookupAt ; fold ; get_newK )
open import T4.ParsObj using ( stepOf )
open import T4.BinTree using ( nIdx ; lIdx ; rIdx )
open import T4.WfRedExtract using ( pLValueBound )
open import T4.DescSndImp using ( neSucc ; succForm_imp )

open import T4.OpaqueLookupImp using ( lookup_op_imp )
open import T4.ForkImp
  using ( fork_false_to_snd_imp ; fork_true_to_fst_imp ; testEq_fire_imp )

open import BRA3.Church       using ( pi ; predecessor ; sub )
open import BRA3.ChurchLeq    using ( leq )
open import BRA3.PairAlgebra  using ( compose1U_eq )
open import BRA3.SubT.NatEq   using ( natEqF )
open import BRA3.Contrapositive using ( compI )
open import T4.Thm12.ImpHelpers
  using ( impLift ; impCong1 ; impCongL ; impCongR ; impEqTrans )

import T4.OpaqueHarnessImp
private
  triStepU : Fun1
  triStepU = stepOf cellLeafTri cellNodeTri
open T4.OpaqueHarnessImp.Himp triStepU

------------------------------------------------------------------------
-- pLValueBound_imp :  imp (p != O) (pL p <= pred p) .
-- Transport the bare bound at the manifest successor  sp = s (pred p)  back
-- along  p = sp  (succForm_imp), as in T4.DescSndImp.argValueBound_imp, with one
-- extra Fst layer since  pL p = Fst (Snd (Snd p)) .

pLValueBound_imp : (p : Term) ->
  Deriv (imp (neg (eqF p O)) (leq (pL p) (ap1 predecessor p)))
pLValueBound_imp p =
  let sp : Term
      sp = ap1 s (ap1 predecessor p)
      neS : Deriv (neg (eqF sp O))
      neS = neSucc (ap1 predecessor p)
      D : Deriv (leq (pL sp) (ap1 predecessor sp))
      D = pLValueBound sp neS
      sfi : Deriv (imp (neg (eqF p O)) (eqF p sp))
      sfi = succForm_imp p
      argEq : Deriv (imp (neg (eqF p O)) (eqF (pL p) (pL sp)))
      argEq = impCong1 Fst (pArg p) (pArg sp)
                (impCong1 Snd (ap1 Snd p) (ap1 Snd sp)
                  (impCong1 Snd p sp sfi))
      predEq : Deriv (imp (neg (eqF p O))
                 (eqF (ap1 predecessor p) (ap1 predecessor sp)))
      predEq = impCong1 predecessor p sp sfi
      stepA : Deriv (imp (neg (eqF p O))
                (eqF (ap2 sub (pL p) (ap1 predecessor p))
                     (ap2 sub (pL sp) (ap1 predecessor p))))
      stepA = impCongL sub (pL p) (pL sp) (ap1 predecessor p) argEq
      stepB : Deriv (imp (neg (eqF p O))
                (eqF (ap2 sub (pL sp) (ap1 predecessor p))
                     (ap2 sub (pL sp) (ap1 predecessor sp))))
      stepB = impCongR sub (ap1 predecessor p) (ap1 predecessor sp) (pL sp) predEq
      chain : Deriv (imp (neg (eqF p O))
                (eqF (ap2 sub (pL p) (ap1 predecessor p))
                     (ap2 sub (pL sp) (ap1 predecessor sp))))
      chain = impEqTrans (ap2 sub (pL p) (ap1 predecessor p))
                         (ap2 sub (pL sp) (ap1 predecessor p))
                         (ap2 sub (pL sp) (ap1 predecessor sp))
                stepA stepB
  in impEqTrans (ap2 sub (pL p) (ap1 predecessor p))
                (ap2 sub (pL sp) (ap1 predecessor sp))
                O
       chain (impLift D)

------------------------------------------------------------------------
-- ne-threaded leaf-test helpers.

private
  op_tag_imp : (q : Term) ->
    Deriv (imp (neg (eqF q O)) (eqF (ap1 get_tag (opkg q)) (ap1 Fst q)))
  op_tag_imp q =
    impEqTrans (ap1 get_tag (opkg q)) (ap1 Fst (ap1 get_newK (opkg q))) (ap1 Fst q)
      (impLift (compose1U_eq Fst get_newK (opkg q)))
      (impCong1 Fst (ap1 get_newK (opkg q)) q (op_newK_imp q))

  test1At_imp : (q : Term) ->
    Deriv (imp (neg (eqF q O))
               (eqF (ap1 (C natEqF get_tag (constN 1)) (opkg q))
                    (ap2 natEqF (ap1 Fst q) (natCode 1))))
  test1At_imp q =
    impEqTrans (ap1 (C natEqF get_tag (constN 1)) (opkg q))
               (ap2 natEqF (ap1 get_tag (opkg q)) (ap1 (constN 1) (opkg q)))
               (ap2 natEqF (ap1 Fst q) (natCode 1))
      (impLift (ax_C natEqF get_tag (constN 1) (opkg q)))
      (impEqTrans (ap2 natEqF (ap1 get_tag (opkg q)) (ap1 (constN 1) (opkg q)))
                  (ap2 natEqF (ap1 Fst q) (ap1 (constN 1) (opkg q)))
                  (ap2 natEqF (ap1 Fst q) (natCode 1))
         (impCongL natEqF (ap1 get_tag (opkg q)) (ap1 Fst q) (ap1 (constN 1) (opkg q))
            (op_tag_imp q))
         (impLift (congR natEqF (ap1 Fst q) (constN_eq 1 (opkg q)))))

------------------------------------------------------------------------
-- The main Gam-polymorphic Su unfold.

triF_op_Su_gam : (Gam : Formula) (q : Term) ->
  Deriv (imp Gam (neg (eqF q O))) ->
  Deriv (imp Gam (eqF (ap2 natEqF (ap1 Fst q) (natCode 1)) O)) ->
  Deriv (imp Gam (eqF (dtag q) dgSu)) ->
  Deriv (imp Gam (eqF (ap1 triF q) (derSu (ap1 triF (pL q)))))
triF_op_Su_gam Gam q gNe gNl gHtag =
  let opk : Term
      opk = opkg q
      tpl : Term
      tpl = ap1 triF (pL q)
      ----------------------------------------------------------------
      -- (0) unfold.
      u0 : Deriv (imp Gam (eqF (ap1 triF q) (ap1 triStepU opk)))
      u0 = compI gNe (opUnfold_imp q)
      ----------------------------------------------------------------
      -- (1) leaf-test skips -> node branch.
      t1_eq : Deriv (imp Gam (eqF (ap1 (C natEqF get_tag (constN 1)) opk)
                                  (ap2 natEqF (ap1 Fst q) (natCode 1))))
      t1_eq = compI gNe (test1At_imp q)
      t1_O : Deriv (imp Gam (eqF (ap1 (C natEqF get_tag (constN 1)) opk) O))
      t1_O = impEqTrans (ap1 (C natEqF get_tag (constN 1)) opk)
                        (ap2 natEqF (ap1 Fst q) (natCode 1)) O t1_eq gNl
      toNode_g : Deriv (imp Gam (eqF (ap1 triStepU opk) (ap1 cellNodeTri opk)))
      toNode_g = fork_false_to_snd_imp Gam cellLeafTri cellNodeTri
                   (C natEqF get_tag (constN 1)) opk t1_O
      ----------------------------------------------------------------
      -- (2) node-label cascade fires Su.
      nieqH : Deriv (imp Gam (eqF (ap1 nIdx opk) dgSu))
      nieqH = impEqTrans (ap1 nIdx opk) (dtag q) dgSu (compI gNe (op_nIdx_imp q)) gHtag
      node_fires : Deriv (imp Gam (eqF (ap1 cellNodeTri opk) (ap1 suNodeCell opk)))
      node_fires = fork_true_to_fst_imp Gam suNodeCell restAdTri (testEq 1) opk
                     (testEq_fire_imp Gam 1 opk nieqH)
      ----------------------------------------------------------------
      -- (3) cell value:  suNodeCell opk = derSu (triF (pL q)) .
      recL_imp : Deriv (imp Gam (eqF (ap1 (lookupAt lIdx) opk) tpl))
      recL_imp = lookup_op_imp Gam Z triStepU lIdx (ap1 predecessor q) (pL q)
                   (compI gNe (op_pL_imp q)) (compI gNe (pLValueBound_imp q))
      clt : Term
      clt = ap1 cellLeafTri opk
      LlookL : Term
      LlookL = ap1 (lookupAt lIdx) opk
      inner_val : Deriv (imp Gam (eqF (ap1 (C pi (lookupAt lIdx) cellLeafTri) opk)
                                      (ap2 pi tpl filler)))
      inner_val =
        impEqTrans (ap1 (C pi (lookupAt lIdx) cellLeafTri) opk)
                   (ap2 pi LlookL clt) (ap2 pi tpl filler)
          (impLift (ax_C pi (lookupAt lIdx) cellLeafTri opk))
          (impEqTrans (ap2 pi LlookL clt) (ap2 pi tpl clt) (ap2 pi tpl filler)
             (impCongL pi LlookL tpl clt recL_imp)
             (impLift (congR pi tpl (cellLeafTri_at opk))))
      CC : Term
      CC = ap1 (C pi (lookupAt lIdx) cellLeafTri) opk
      mid_val : Deriv (imp Gam (eqF (ap1 (C pi (constN 1) (C pi (lookupAt lIdx) cellLeafTri)) opk)
                                    (ap2 pi dgSu (ap2 pi tpl filler))))
      mid_val =
        impEqTrans (ap1 (C pi (constN 1) (C pi (lookupAt lIdx) cellLeafTri)) opk)
                   (ap2 pi (ap1 (constN 1) opk) CC)
                   (ap2 pi dgSu (ap2 pi tpl filler))
          (impLift (ax_C pi (constN 1) (C pi (lookupAt lIdx) cellLeafTri) opk))
          (impEqTrans (ap2 pi (ap1 (constN 1) opk) CC) (ap2 pi (natCode 1) CC)
                      (ap2 pi dgSu (ap2 pi tpl filler))
             (impLift (congL pi CC (constN_eq 1 opk)))
             (impCongR pi CC (ap2 pi tpl filler) (natCode 1) inner_val))
      DD : Term
      DD = ap1 (C pi (constN 1) (C pi (lookupAt lIdx) cellLeafTri)) opk
      cell_val : Deriv (imp Gam (eqF (ap1 suNodeCell opk) (derSu tpl)))
      cell_val =
        impEqTrans (ap1 suNodeCell opk) (ap2 pi (ap1 (constN 2) opk) DD) (derSu tpl)
          (impLift (ax_C pi (constN 2) (C pi (constN 1) (C pi (lookupAt lIdx) cellLeafTri)) opk))
          (impEqTrans (ap2 pi (ap1 (constN 2) opk) DD) (ap2 pi (natCode 2) DD) (derSu tpl)
             (impLift (congL pi DD (constN_eq 2 opk)))
             (impCongR pi DD (ap2 pi dgSu (ap2 pi tpl filler)) (natCode 2) mid_val))
  in impEqTrans (ap1 triF q) (ap1 triStepU opk) (derSu tpl) u0
       (impEqTrans (ap1 triStepU opk) (ap1 cellNodeTri opk) (derSu tpl) toNode_g
          (impEqTrans (ap1 cellNodeTri opk) (ap1 suNodeCell opk) (derSu tpl)
             node_fires cell_val))
