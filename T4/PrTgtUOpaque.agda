{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.PrTgtUOpaque -- the OPAQUE tgtF equations over arbitrary codes p : Term,
-- the target-endpoint analogue of T4.PrSrcUOpaque (same dispatch skeleton; the
-- cell values encode the rule RIGHT-hand sides).
--
--   reflO  => tgtF p = tmO
--   ap1c   => tgtF p = tmAp1 (funP p) (tgtF (pL p))
--   ap2c   => tgtF p = tmAp2 (funP p) (tgtF (pL p)) (tgtF (pR p))
--   rO     => tgtF p = tmO
--   rU     => tgtF p = tgtF (pL p)
--   rV     => tgtF p = tgtF (pR p)
--   rC     => tgtF p = tmAp2 (gP p) (tmAp1 (h1P p)(tgtF (pL p))) (tmAp1 (h2P p)(tgtF (pL p)))
--   rRb    => tgtF p = tmAp1 (gP p) (tgtF (pL p))
--   rRs    => tgtF p = tmAp2 (h1P p) (tmAp2 (h2P p)(tgtF (pL p))(tgtF (pR p)))
--                              (tmAp2 (cRec (gP p)(h1P p)(h2P p))(tgtF (pL p))(tgtF (pR p)))
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.PrTgtUOpaque where

open import T4.Base

open import T4.PrDerCode using ( dgReflO ; dgAp1c ; dgAp2c ; dgRo ; dgRu ; dgRv ; dgRC ; dgRb ; dgRs )
open import T4.PrCodeObj using ( tmO ; tmAp1 ; tmAp2 ; cRec )
open import T4.PrDev using ( mkAp1 ; mkAp2 ; mkRec ; tmOF
                           ; mkAp1_val ; mkAp2_val ; mkRec_val ; tmOF_val
                           ; idxTest_fire ; idxTest_skip )
open import T4.PrTgt
  using ( tgtF ; derTagIdx ; derBunIdx ; bunF ; bunG ; bunH1 ; bunH2 ; tgtL ; tgtR
        ; ap1cCell ; ap2cCell ; rOCell ; rUCell ; rVCell ; rCCell ; rRbCell ; rRsCell
        ; tgt_l2 ; tgt_l3 ; tgt_l4 ; tgt_l5 ; tgt_l6 ; tgt_l7 ; cellNodeTgt ; testTag )

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
  tgtStepU : Fun1
  tgtStepU = stepOf tmOF cellNodeTgt
open T4.OpaqueHarness.H tgtStepU

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
    Deriv (eqF (ap1 tgtStepU (opkg p)) (ap1 cellNodeTgt (opkg p)))
  toNode p ne nl =
    fork_false_to_snd tmOF cellNodeTgt (C natEqF get_tag (constN 1)) (opkg p)
      (ruleTrans (test1At p ne) nl)

  recTag : (p : Term) -> Deriv (neg (eqF p O)) -> {tg : Term} ->
    Deriv (eqF (ap1 Fst (dtag p)) tg) -> Deriv (eqF (ap1 derTagIdx (opkg p)) tg)
  recTag p ne htag =
    ruleTrans (compose1U_eq Fst nIdx (opkg p)) (ruleTrans (cong1 Fst (op_nIdx p ne)) htag)

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

  toCell : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) ->
    Deriv (eqF (ap1 tgtF p) (ap1 cellNodeTgt (opkg p)))
  toCell p ne nl = ruleTrans (opUnfold p ne) (toNode p ne nl)

  wn : (m k : Nat) -> ((Eq m k) -> Empty) -> NatNeqWitness m k
  wn m k pf = decideNatNeq m k pf
  w21 : NatNeqWitness 2 1
  w21 = decideNatNeq 2 1 (\ ())

------------------------------------------------------------------------
-- SECTION 2.  Leaf and o-redex (both tmO).

tgtF_op_reflO : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap1 Fst p) (natCode 1)) -> Deriv (eqF (ap1 tgtF p) tmO)
tgtF_op_reflO p ne htagB =
  let opk = opkg p
      t1_fire = ruleTrans (test1At p ne) (ruleTrans (congL natEqF (natCode 1) htagB) (natEq_eq 1))
      cell_fires = fork_true_to_fst tmOF cellNodeTgt (C natEqF get_tag (constN 1)) opk t1_fire
  in ruleTrans (opUnfold p ne) (ruleTrans cell_fires (tmOF_val opk))

tgtF_op_ap1c : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) -> Deriv (eqF (ap1 Fst (dtag p)) dgAp1c) ->
  Deriv (eqF (ap1 tgtF p) (tmAp1 (funP p) (ap1 tgtF (pL p))))
tgtF_op_ap1c p ne nl htag =
  let opk = opkg p
      tg = recTag p ne htag
      fires = fork_true_to_fst ap1cCell tgt_l2 (testTag 1) opk (idxTest_fire derTagIdx 1 opk tg)
      val = mkAp1_val bunF tgtL opk (funP p) (ap1 tgtF (pL p)) (recBun p ne) (recPL p ne)
  in ruleTrans (toCell p ne nl) (ruleTrans fires val)

tgtF_op_ap2c : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) -> Deriv (eqF (ap1 Fst (dtag p)) dgAp2c) ->
  Deriv (eqF (ap1 tgtF p) (tmAp2 (funP p) (ap1 tgtF (pL p)) (ap1 tgtF (pR p))))
tgtF_op_ap2c p ne nl htag =
  let opk = opkg p
      tg = recTag p ne htag
      fires =
        ruleTrans (fork_false_to_snd ap1cCell tgt_l2 (testTag 1) opk (idxTest_skip derTagIdx 2 1 opk w21 tg))
                  (fork_true_to_fst ap2cCell tgt_l3 (testTag 2) opk (idxTest_fire derTagIdx 2 opk tg))
      val = mkAp2_val bunF tgtL tgtR opk (funP p) (ap1 tgtF (pL p)) (ap1 tgtF (pR p)) (recBun p ne) (recPL p ne) (recPR p ne)
  in ruleTrans (toCell p ne nl) (ruleTrans fires val)

tgtF_op_rO : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) -> Deriv (eqF (ap1 Fst (dtag p)) dgRo) ->
  Deriv (eqF (ap1 tgtF p) tmO)
tgtF_op_rO p ne nl htag =
  let opk = opkg p
      tg = recTag p ne htag
      fires =
        ruleTrans (fork_false_to_snd ap1cCell tgt_l2 (testTag 1) opk (idxTest_skip derTagIdx 3 1 opk (wn 3 1 (\ ())) tg))
          (ruleTrans (fork_false_to_snd ap2cCell tgt_l3 (testTag 2) opk (idxTest_skip derTagIdx 3 2 opk (wn 3 2 (\ ())) tg))
                     (fork_true_to_fst rOCell tgt_l4 (testTag 3) opk (idxTest_fire derTagIdx 3 opk tg)))
  in ruleTrans (toCell p ne nl) (ruleTrans fires (tmOF_val opk))

tgtF_op_rU : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) -> Deriv (eqF (ap1 Fst (dtag p)) dgRu) ->
  Deriv (eqF (ap1 tgtF p) (ap1 tgtF (pL p)))
tgtF_op_rU p ne nl htag =
  let opk = opkg p
      tg = recTag p ne htag
      fires =
        ruleTrans (fork_false_to_snd ap1cCell tgt_l2 (testTag 1) opk (idxTest_skip derTagIdx 4 1 opk (wn 4 1 (\ ())) tg))
          (ruleTrans (fork_false_to_snd ap2cCell tgt_l3 (testTag 2) opk (idxTest_skip derTagIdx 4 2 opk (wn 4 2 (\ ())) tg))
            (ruleTrans (fork_false_to_snd rOCell tgt_l4 (testTag 3) opk (idxTest_skip derTagIdx 4 3 opk (wn 4 3 (\ ())) tg))
                       (fork_true_to_fst rUCell tgt_l5 (testTag 4) opk (idxTest_fire derTagIdx 4 opk tg))))
  in ruleTrans (toCell p ne nl) (ruleTrans fires (recPL p ne))

tgtF_op_rV : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) -> Deriv (eqF (ap1 Fst (dtag p)) dgRv) ->
  Deriv (eqF (ap1 tgtF p) (ap1 tgtF (pR p)))
tgtF_op_rV p ne nl htag =
  let opk = opkg p
      tg = recTag p ne htag
      fires =
        ruleTrans (fork_false_to_snd ap1cCell tgt_l2 (testTag 1) opk (idxTest_skip derTagIdx 5 1 opk (wn 5 1 (\ ())) tg))
          (ruleTrans (fork_false_to_snd ap2cCell tgt_l3 (testTag 2) opk (idxTest_skip derTagIdx 5 2 opk (wn 5 2 (\ ())) tg))
            (ruleTrans (fork_false_to_snd rOCell tgt_l4 (testTag 3) opk (idxTest_skip derTagIdx 5 3 opk (wn 5 3 (\ ())) tg))
              (ruleTrans (fork_false_to_snd rUCell tgt_l5 (testTag 4) opk (idxTest_skip derTagIdx 5 4 opk (wn 5 4 (\ ())) tg))
                         (fork_true_to_fst rVCell tgt_l6 (testTag 5) opk (idxTest_fire derTagIdx 5 opk tg)))))
  in ruleTrans (toCell p ne nl) (ruleTrans fires (recPR p ne))

tgtF_op_rC : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) -> Deriv (eqF (ap1 Fst (dtag p)) dgRC) ->
  Deriv (eqF (ap1 tgtF p) (tmAp2 (gP p) (tmAp1 (h1P p) (ap1 tgtF (pL p))) (tmAp1 (h2P p) (ap1 tgtF (pL p)))))
tgtF_op_rC p ne nl htag =
  let opk = opkg p
      tg = recTag p ne htag
      fires =
        ruleTrans (fork_false_to_snd ap1cCell tgt_l2 (testTag 1) opk (idxTest_skip derTagIdx 6 1 opk (wn 6 1 (\ ())) tg))
          (ruleTrans (fork_false_to_snd ap2cCell tgt_l3 (testTag 2) opk (idxTest_skip derTagIdx 6 2 opk (wn 6 2 (\ ())) tg))
            (ruleTrans (fork_false_to_snd rOCell tgt_l4 (testTag 3) opk (idxTest_skip derTagIdx 6 3 opk (wn 6 3 (\ ())) tg))
              (ruleTrans (fork_false_to_snd rUCell tgt_l5 (testTag 4) opk (idxTest_skip derTagIdx 6 4 opk (wn 6 4 (\ ())) tg))
                (ruleTrans (fork_false_to_snd rVCell tgt_l6 (testTag 5) opk (idxTest_skip derTagIdx 6 5 opk (wn 6 5 (\ ())) tg))
                           (fork_true_to_fst rCCell tgt_l7 (testTag 6) opk (idxTest_fire derTagIdx 6 opk tg))))))
      armH1 = mkAp1_val bunH1 tgtL opk (h1P p) (ap1 tgtF (pL p)) (recH1 p ne) (recPL p ne)
      armH2 = mkAp1_val bunH2 tgtL opk (h2P p) (ap1 tgtF (pL p)) (recH2 p ne) (recPL p ne)
      val = mkAp2_val bunG (mkAp1 bunH1 tgtL) (mkAp1 bunH2 tgtL) opk
              (gP p) (tmAp1 (h1P p) (ap1 tgtF (pL p))) (tmAp1 (h2P p) (ap1 tgtF (pL p))) (recG p ne) armH1 armH2
  in ruleTrans (toCell p ne nl) (ruleTrans fires val)

tgtF_op_rRb : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) -> Deriv (eqF (ap1 Fst (dtag p)) dgRb) ->
  Deriv (eqF (ap1 tgtF p) (tmAp1 (gP p) (ap1 tgtF (pL p))))
tgtF_op_rRb p ne nl htag =
  let opk = opkg p
      tg = recTag p ne htag
      fires =
        ruleTrans (fork_false_to_snd ap1cCell tgt_l2 (testTag 1) opk (idxTest_skip derTagIdx 7 1 opk (wn 7 1 (\ ())) tg))
          (ruleTrans (fork_false_to_snd ap2cCell tgt_l3 (testTag 2) opk (idxTest_skip derTagIdx 7 2 opk (wn 7 2 (\ ())) tg))
            (ruleTrans (fork_false_to_snd rOCell tgt_l4 (testTag 3) opk (idxTest_skip derTagIdx 7 3 opk (wn 7 3 (\ ())) tg))
              (ruleTrans (fork_false_to_snd rUCell tgt_l5 (testTag 4) opk (idxTest_skip derTagIdx 7 4 opk (wn 7 4 (\ ())) tg))
                (ruleTrans (fork_false_to_snd rVCell tgt_l6 (testTag 5) opk (idxTest_skip derTagIdx 7 5 opk (wn 7 5 (\ ())) tg))
                  (ruleTrans (fork_false_to_snd rCCell tgt_l7 (testTag 6) opk (idxTest_skip derTagIdx 7 6 opk (wn 7 6 (\ ())) tg))
                             (fork_true_to_fst rRbCell rRsCell (testTag 7) opk (idxTest_fire derTagIdx 7 opk tg)))))))
      val = mkAp1_val bunG tgtL opk (gP p) (ap1 tgtF (pL p)) (recG p ne) (recPL p ne)
  in ruleTrans (toCell p ne nl) (ruleTrans fires val)

tgtF_op_rRs : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) -> Deriv (eqF (ap1 Fst (dtag p)) dgRs) ->
  Deriv (eqF (ap1 tgtF p)
             (tmAp2 (h1P p) (tmAp2 (h2P p) (ap1 tgtF (pL p)) (ap1 tgtF (pR p)))
                            (tmAp2 (cRec (gP p) (h1P p) (h2P p)) (ap1 tgtF (pL p)) (ap1 tgtF (pR p)))))
tgtF_op_rRs p ne nl htag =
  let opk = opkg p
      tg = recTag p ne htag
      fires =
        ruleTrans (fork_false_to_snd ap1cCell tgt_l2 (testTag 1) opk (idxTest_skip derTagIdx 8 1 opk (wn 8 1 (\ ())) tg))
          (ruleTrans (fork_false_to_snd ap2cCell tgt_l3 (testTag 2) opk (idxTest_skip derTagIdx 8 2 opk (wn 8 2 (\ ())) tg))
            (ruleTrans (fork_false_to_snd rOCell tgt_l4 (testTag 3) opk (idxTest_skip derTagIdx 8 3 opk (wn 8 3 (\ ())) tg))
              (ruleTrans (fork_false_to_snd rUCell tgt_l5 (testTag 4) opk (idxTest_skip derTagIdx 8 4 opk (wn 8 4 (\ ())) tg))
                (ruleTrans (fork_false_to_snd rVCell tgt_l6 (testTag 5) opk (idxTest_skip derTagIdx 8 5 opk (wn 8 5 (\ ())) tg))
                  (ruleTrans (fork_false_to_snd rCCell tgt_l7 (testTag 6) opk (idxTest_skip derTagIdx 8 6 opk (wn 8 6 (\ ())) tg))
                             (fork_false_to_snd rRbCell rRsCell (testTag 7) opk (idxTest_skip derTagIdx 8 7 opk (wn 8 7 (\ ())) tg)))))))
      arm2 = mkAp2_val bunH2 tgtL tgtR opk (h2P p) (ap1 tgtF (pL p)) (ap1 tgtF (pR p)) (recH2 p ne) (recPL p ne) (recPR p ne)
      recFun = mkRec_val bunG bunH1 bunH2 opk (gP p) (h1P p) (h2P p) (recG p ne) (recH1 p ne) (recH2 p ne)
      arm3 = mkAp2_val (mkRec bunG bunH1 bunH2) tgtL tgtR opk (cRec (gP p) (h1P p) (h2P p)) (ap1 tgtF (pL p)) (ap1 tgtF (pR p)) recFun (recPL p ne) (recPR p ne)
      val = mkAp2_val bunH1 (mkAp2 bunH2 tgtL tgtR) (mkAp2 (mkRec bunG bunH1 bunH2) tgtL tgtR) opk
              (h1P p) (tmAp2 (h2P p) (ap1 tgtF (pL p)) (ap1 tgtF (pR p)))
              (tmAp2 (cRec (gP p) (h1P p) (h2P p)) (ap1 tgtF (pL p)) (ap1 tgtF (pR p))) (recH1 p ne) arm2 arm3
  in ruleTrans (toCell p ne nl) (ruleTrans fires val)
