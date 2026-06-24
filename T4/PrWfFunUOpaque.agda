{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.PrWfFunUOpaque -- OPAQUE wfFun extraction for compound funcodes, over an
-- arbitrary funcode  f : Term .  For  Fst f = natCode 6 (cComp) / 8 (cRec) :
--
--   wfFun f = pi (funValid f) (pi (wfFun (dtag f)) (pi (wfFun (pL f)) (wfFun (pR f))))
--
-- where dtag f = Fst(Snd f) = the first sub-funcode g, pL f = h1, pR f = h2.
-- Combined with the dispatch this gives  wfFun (funP sK) = O  =>  funValid (funP
-- sK) = O  (reassembly, via piZeroL -> funValid_C, for the src endpoint) AND
-- wfFun of each component = O (for validity of the residual derC/derRs).
--
-- No holes, no postulates, no termination warnings (only the benign
-- RuleInst3:328 unreachable-clauses warning); --safe --without-K --exact-split.

module T4.PrWfFunUOpaque where

open import T4.Base

open import T4.PrFunValidCanon using ( funValidF )
open import T4.PrWfFun
  using ( wfFun ; wfFunNodeCell ; leafCell ; fv3cell ; selfChk ; compCellC ; compCellR ; rejectCell
        ; nH ; isF1at ; isF2at ; isF1 ; isF2
        ; wfn_l4 ; wfn_l5 ; wfn_l6 ; wfn_l7 ; wfn_l8 ; testHd )

open import T4.DerCodeS using ( dtag ; pL ; pR )
open import T4.BinTree using ( nIdx ; lIdx ; rIdx )
open import T4.FoldRec using ( lookupAt ; fold ; get_newK )
open import T4.ParsObj using ( stepOf )
open import T4.ProgParse using ( get_tag )
open import T4.OpaqueLookup using ( lookup_op )
open import T4.WfRedExtract using ( pLValueBound ; pRValueBound )
open import T4.DerSrc using ( fork_true_to_fst ; fork_false_to_snd )
open import T4.PrDev using ( idxTest_fire ; idxTest_skip )

-- dtagValueBound deps (mirror argValueBound).
open import T4.SizedPres using ( succForm )
open import T4.DescSnd  using ( descSnd )
open import T4.SndDescent using ( sndLe )
open import T4.TauRowBase using ( fstLe )
open import T4.Counting using ( nonzero_ge_one )
open import T4.TreeCovInd using ( leq_s_s_cancel )

open import BRA3.Church       using ( pi ; sub ; predecessor )
open import BRA3.ChurchLeq    using ( leq )
open import BRA3.PairAlgebra  using ( compose1U ; compose1U_eq )
open import BRA3.SubT.NatEq    using ( natEqF ; natEq_eq )
open import BRA3.SubT.V2NatNeq using ( NatNeqWitness ; natEqF_at_neq ; decideNatNeq )
open import T4.LeqMono using ( leq_trans )

import T4.OpaqueHarness
private
  wfFunStepU : Fun1
  wfFunStepU = stepOf Z wfFunNodeCell
open T4.OpaqueHarness.HBase rejectCell wfFunStepU

------------------------------------------------------------------------
-- SECTION 0.  dtag f <= pred f  (mirror argValueBound with fstLe instead of sndLe).

dtagValueBound : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (leq (dtag p) (ap1 predecessor p))
dtagValueBound p ne =
  let pos : Deriv (leq (ap1 s O) p)
      pos = nonzero_ge_one p ne
      dscS : Deriv (leq (ap1 s (ap1 Snd p)) (ap1 s (ap1 predecessor p)))
      dscS = ruleTrans (congR sub (ap1 s (ap1 Snd p)) (succForm p ne)) (descSnd p pos)
      sndLeP : Deriv (leq (ap1 Snd p) (ap1 predecessor p))
      sndLeP = leq_s_s_cancel (ap1 Snd p) (ap1 predecessor p) dscS
  in leq_trans (dtag p) (ap1 Snd p) (ap1 predecessor p) (fstLe (ap1 Snd p)) sndLeP

------------------------------------------------------------------------
-- SECTION 1.  Harness recovery.

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

  -- selfChk (opkg p) = funValid p   (= ap1 funValidF p, via op_newK).
  selfChk_op : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 selfChk (opkg p)) (ap1 funValidF p))
  selfChk_op p ne =
    ruleTrans (compose1U_eq funValidF get_newK (opkg p)) (cong1 funValidF (op_newK p ne))

  recN : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 (lookupAt nIdx) (opkg p)) (ap1 wfFun (dtag p)))
  recN p ne = lookup_op rejectCell wfFunStepU nIdx (ap1 predecessor p) (dtag p) (op_nIdx p ne) (dtagValueBound p ne)
  recL : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 (lookupAt lIdx) (opkg p)) (ap1 wfFun (pL p)))
  recL p ne = lookup_op rejectCell wfFunStepU lIdx (ap1 predecessor p) (pL p) (op_pL p ne) (pLValueBound p ne)
  recR : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 (lookupAt rIdx) (opkg p)) (ap1 wfFun (pR p)))
  recR p ne = lookup_op rejectCell wfFunStepU rIdx (ap1 predecessor p) (pR p) (op_pR p ne) (pRValueBound p ne)

  -- opaque head recovery and arity-cell values (FIX(C)).
  hdN_op : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 (compose1U Fst nIdx) (opkg p)) (ap1 Fst (dtag p)))
  hdN_op p ne = ruleTrans (compose1U_eq Fst nIdx (opkg p)) (cong1 Fst (op_nIdx p ne))
  hdL_op : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 (compose1U Fst lIdx) (opkg p)) (ap1 Fst (pL p)))
  hdL_op p ne = ruleTrans (compose1U_eq Fst lIdx (opkg p)) (cong1 Fst (op_pL p ne))
  hdR_op : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 (compose1U Fst rIdx) (opkg p)) (ap1 Fst (pR p)))
  hdR_op p ne = ruleTrans (compose1U_eq Fst rIdx (opkg p)) (cong1 Fst (op_pR p ne))
  nH_op : (p : Term) (k : Nat) (idx : Fun1) (X : Term) ->
    Deriv (eqF (ap1 (compose1U Fst idx) (opkg p)) (ap1 Fst X)) ->
    Deriv (eqF (ap1 (nH k idx) (opkg p)) (ap2 natEqF (ap1 Fst X) (natCode k)))
  nH_op p k idx X hd =
    ruleTrans (ax_C natEqF (compose1U Fst idx) (constN k) (opkg p))
      (ruleTrans (congL natEqF (ap1 (constN k) (opkg p)) hd)
                 (congR natEqF (ap1 Fst X) (constN_eq k (opkg p))))
  isF1at_op : (p : Term) (idx : Fun1) (X : Term) ->
    Deriv (eqF (ap1 (compose1U Fst idx) (opkg p)) (ap1 Fst X)) ->
    Deriv (eqF (ap1 (isF1at idx) (opkg p)) (isF1 X))
  isF1at_op p idx X hd =
    ruleTrans (ax_C pi (nH 7 idx) (nH 8 idx) (opkg p))
      (ruleTrans (congL pi (ap1 (nH 8 idx) (opkg p)) (nH_op p 7 idx X hd))
                 (congR pi (ap2 natEqF (ap1 Fst X) (natCode 7)) (nH_op p 8 idx X hd)))
  isF2at_op : (p : Term) (idx : Fun1) (X : Term) ->
    Deriv (eqF (ap1 (compose1U Fst idx) (opkg p)) (ap1 Fst X)) ->
    Deriv (eqF (ap1 (isF2at idx) (opkg p)) (isF2 X))
  isF2at_op p idx X hd =
    ruleTrans (ax_C pi (nH 3 idx) (C pi (nH 4 idx) (C pi (nH 5 idx) (nH 6 idx))) (opkg p))
      (ruleTrans (congL pi (ap1 (C pi (nH 4 idx) (C pi (nH 5 idx) (nH 6 idx))) (opkg p)) (nH_op p 3 idx X hd))
        (congR pi (ap2 natEqF (ap1 Fst X) (natCode 3))
          (ruleTrans (ax_C pi (nH 4 idx) (C pi (nH 5 idx) (nH 6 idx)) (opkg p))
            (ruleTrans (congL pi (ap1 (C pi (nH 5 idx) (nH 6 idx)) (opkg p)) (nH_op p 4 idx X hd))
              (congR pi (ap2 natEqF (ap1 Fst X) (natCode 4))
                (ruleTrans (ax_C pi (nH 5 idx) (nH 6 idx) (opkg p))
                  (ruleTrans (congL pi (ap1 (nH 6 idx) (opkg p)) (nH_op p 5 idx X hd))
                             (congR pi (ap2 natEqF (ap1 Fst X) (natCode 5)) (nH_op p 6 idx X hd)))))))))
  -- shared deep fv3 value.
  fv3v_op : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 fv3cell (opkg p))
               (ap2 pi (ap1 wfFun (dtag p)) (ap2 pi (ap1 wfFun (pL p)) (ap1 wfFun (pR p)))))
  fv3v_op p ne =
    let opk = opkg p
    in ruleTrans (ax_C pi (lookupAt nIdx) (C pi (lookupAt lIdx) (lookupAt rIdx)) opk)
         (ruleTrans (congL pi (ap1 (C pi (lookupAt lIdx) (lookupAt rIdx)) opk) (recN p ne))
           (congR pi (ap1 wfFun (dtag p))
             (ruleTrans (ax_C pi (lookupAt lIdx) (lookupAt rIdx) opk)
               (ruleTrans (congL pi (ap1 (lookupAt rIdx) opk) (recL p ne))
                          (congR pi (ap1 wfFun (pL p)) (recR p ne))))))
  -- compCellC value (cComp arity: g Fun2, h1/h2 Fun1).
  compCellC_op : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 compCellC (opkg p))
               (ap2 pi (ap1 funValidF p)
                 (ap2 pi (isF2 (dtag p)) (ap2 pi (isF1 (pL p)) (ap2 pi (isF1 (pR p))
                   (ap2 pi (ap1 wfFun (dtag p)) (ap2 pi (ap1 wfFun (pL p)) (ap1 wfFun (pR p)))))))))
  compCellC_op p ne =
    let opk = opkg p
    in ruleTrans (ax_C pi selfChk (C pi (isF2at nIdx) (C pi (isF1at lIdx) (C pi (isF1at rIdx) fv3cell))) opk)
         (ruleTrans (congL pi (ap1 (C pi (isF2at nIdx) (C pi (isF1at lIdx) (C pi (isF1at rIdx) fv3cell))) opk) (selfChk_op p ne))
           (congR pi (ap1 funValidF p)
             (ruleTrans (ax_C pi (isF2at nIdx) (C pi (isF1at lIdx) (C pi (isF1at rIdx) fv3cell)) opk)
               (ruleTrans (congL pi (ap1 (C pi (isF1at lIdx) (C pi (isF1at rIdx) fv3cell)) opk) (isF2at_op p nIdx (dtag p) (hdN_op p ne)))
                 (congR pi (isF2 (dtag p))
                   (ruleTrans (ax_C pi (isF1at lIdx) (C pi (isF1at rIdx) fv3cell) opk)
                     (ruleTrans (congL pi (ap1 (C pi (isF1at rIdx) fv3cell) opk) (isF1at_op p lIdx (pL p) (hdL_op p ne)))
                       (congR pi (isF1 (pL p))
                         (ruleTrans (ax_C pi (isF1at rIdx) fv3cell opk)
                           (ruleTrans (congL pi (ap1 fv3cell opk) (isF1at_op p rIdx (pR p) (hdR_op p ne)))
                             (congR pi (isF1 (pR p)) (fv3v_op p ne))))))))))))
  -- compCellR value (cRec arity: g Fun1, h1/h2 Fun2).
  compCellR_op : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap1 compCellR (opkg p))
               (ap2 pi (ap1 funValidF p)
                 (ap2 pi (isF1 (dtag p)) (ap2 pi (isF2 (pL p)) (ap2 pi (isF2 (pR p))
                   (ap2 pi (ap1 wfFun (dtag p)) (ap2 pi (ap1 wfFun (pL p)) (ap1 wfFun (pR p)))))))))
  compCellR_op p ne =
    let opk = opkg p
    in ruleTrans (ax_C pi selfChk (C pi (isF1at nIdx) (C pi (isF2at lIdx) (C pi (isF2at rIdx) fv3cell))) opk)
         (ruleTrans (congL pi (ap1 (C pi (isF1at nIdx) (C pi (isF2at lIdx) (C pi (isF2at rIdx) fv3cell))) opk) (selfChk_op p ne))
           (congR pi (ap1 funValidF p)
             (ruleTrans (ax_C pi (isF1at nIdx) (C pi (isF2at lIdx) (C pi (isF2at rIdx) fv3cell)) opk)
               (ruleTrans (congL pi (ap1 (C pi (isF2at lIdx) (C pi (isF2at rIdx) fv3cell)) opk) (isF1at_op p nIdx (dtag p) (hdN_op p ne)))
                 (congR pi (isF1 (dtag p))
                   (ruleTrans (ax_C pi (isF2at lIdx) (C pi (isF2at rIdx) fv3cell) opk)
                     (ruleTrans (congL pi (ap1 (C pi (isF2at rIdx) fv3cell) opk) (isF2at_op p lIdx (pL p) (hdL_op p ne)))
                       (congR pi (isF2 (pL p))
                         (ruleTrans (ax_C pi (isF2at rIdx) fv3cell opk)
                           (ruleTrans (congL pi (ap1 fv3cell opk) (isF2at_op p rIdx (pR p) (hdR_op p ne)))
                             (congR pi (isF2 (pR p)) (fv3v_op p ne))))))))))))

  -- to the node cell: wfFun p = wfFunNodeCell (opkg p)  (test1 skips for Fst p in 3..8).
  toCell : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) ->
    Deriv (eqF (ap1 wfFun p) (ap1 wfFunNodeCell (opkg p)))
  toCell p ne nl =
    ruleTrans (opUnfold p ne)
      (fork_false_to_snd Z wfFunNodeCell (C natEqF get_tag (constN 1)) (opkg p)
        (ruleTrans (test1At p ne) nl))

------------------------------------------------------------------------
-- SECTION 2.  The compound extraction equations (Fst f = 6 / 8).

wfFun_op_C : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) ->
  Deriv (eqF (ap1 Fst p) (natCode 6)) ->
  Deriv (eqF (ap1 wfFun p)
             (ap2 pi (ap1 funValidF p)
               (ap2 pi (isF2 (dtag p)) (ap2 pi (isF1 (pL p)) (ap2 pi (isF1 (pR p))
                 (ap2 pi (ap1 wfFun (dtag p)) (ap2 pi (ap1 wfFun (pL p)) (ap1 wfFun (pR p)))))))))
wfFun_op_C p ne nl h6 =
  let opk = opkg p
      tg : Deriv (eqF (ap1 get_tag opk) (natCode 6))
      tg = ruleTrans (op_tag p ne) h6
      fires =
        ruleTrans (fork_false_to_snd leafCell wfn_l4 (testHd 3) opk (idxTest_skip get_tag 6 3 opk (wn 6 3 (\ ())) tg))
          (ruleTrans (fork_false_to_snd leafCell wfn_l5 (testHd 4) opk (idxTest_skip get_tag 6 4 opk (wn 6 4 (\ ())) tg))
            (ruleTrans (fork_false_to_snd leafCell wfn_l6 (testHd 5) opk (idxTest_skip get_tag 6 5 opk (wn 6 5 (\ ())) tg))
                       (fork_true_to_fst compCellC wfn_l7 (testHd 6) opk (idxTest_fire get_tag 6 opk tg))))
  in ruleTrans (toCell p ne nl) (ruleTrans fires (compCellC_op p ne))

wfFun_op_R : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) ->
  Deriv (eqF (ap1 Fst p) (natCode 8)) ->
  Deriv (eqF (ap1 wfFun p)
             (ap2 pi (ap1 funValidF p)
               (ap2 pi (isF1 (dtag p)) (ap2 pi (isF2 (pL p)) (ap2 pi (isF2 (pR p))
                 (ap2 pi (ap1 wfFun (dtag p)) (ap2 pi (ap1 wfFun (pL p)) (ap1 wfFun (pR p)))))))))
wfFun_op_R p ne nl h8 =
  let opk = opkg p
      tg : Deriv (eqF (ap1 get_tag opk) (natCode 8))
      tg = ruleTrans (op_tag p ne) h8
      fires =
        ruleTrans (fork_false_to_snd leafCell wfn_l4 (testHd 3) opk (idxTest_skip get_tag 8 3 opk (wn 8 3 (\ ())) tg))
          (ruleTrans (fork_false_to_snd leafCell wfn_l5 (testHd 4) opk (idxTest_skip get_tag 8 4 opk (wn 8 4 (\ ())) tg))
            (ruleTrans (fork_false_to_snd leafCell wfn_l6 (testHd 5) opk (idxTest_skip get_tag 8 5 opk (wn 8 5 (\ ())) tg))
              (ruleTrans (fork_false_to_snd compCellC wfn_l7 (testHd 6) opk (idxTest_skip get_tag 8 6 opk (wn 8 6 (\ ())) tg))
                (ruleTrans (fork_false_to_snd leafCell wfn_l8 (testHd 7) opk (idxTest_skip get_tag 8 7 opk (wn 8 7 (\ ())) tg))
                           (fork_true_to_fst compCellR rejectCell (testHd 8) opk (idxTest_fire get_tag 8 opk tg))))))
  in ruleTrans (toCell p ne nl) (ruleTrans fires (compCellR_op p ne))

------------------------------------------------------------------------
-- SECTION 3.  The leaf extraction equations (Fst f in {3,4,5,7}).
-- leafCell = selfChk now, so wfFun p = ap1 funValidF p (shallow reassembly).

wfFun_op_s : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) ->
  Deriv (eqF (ap1 Fst p) (natCode 3)) ->
  Deriv (eqF (ap1 wfFun p) (ap1 funValidF p))
wfFun_op_s p ne nl h3 =
  let opk = opkg p
      tg = ruleTrans (op_tag p ne) h3
      fires = fork_true_to_fst leafCell wfn_l4 (testHd 3) opk (idxTest_fire get_tag 3 opk tg)
  in ruleTrans (toCell p ne nl) (ruleTrans fires (selfChk_op p ne))

wfFun_op_o : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) ->
  Deriv (eqF (ap1 Fst p) (natCode 4)) ->
  Deriv (eqF (ap1 wfFun p) (ap1 funValidF p))
wfFun_op_o p ne nl h4 =
  let opk = opkg p
      tg = ruleTrans (op_tag p ne) h4
      fires =
        ruleTrans (fork_false_to_snd leafCell wfn_l4 (testHd 3) opk (idxTest_skip get_tag 4 3 opk (wn 4 3 (\ ())) tg))
                  (fork_true_to_fst leafCell wfn_l5 (testHd 4) opk (idxTest_fire get_tag 4 opk tg))
  in ruleTrans (toCell p ne nl) (ruleTrans fires (selfChk_op p ne))

wfFun_op_u : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) ->
  Deriv (eqF (ap1 Fst p) (natCode 5)) ->
  Deriv (eqF (ap1 wfFun p) (ap1 funValidF p))
wfFun_op_u p ne nl h5 =
  let opk = opkg p
      tg = ruleTrans (op_tag p ne) h5
      fires =
        ruleTrans (fork_false_to_snd leafCell wfn_l4 (testHd 3) opk (idxTest_skip get_tag 5 3 opk (wn 5 3 (\ ())) tg))
          (ruleTrans (fork_false_to_snd leafCell wfn_l5 (testHd 4) opk (idxTest_skip get_tag 5 4 opk (wn 5 4 (\ ())) tg))
                     (fork_true_to_fst leafCell wfn_l6 (testHd 5) opk (idxTest_fire get_tag 5 opk tg)))
  in ruleTrans (toCell p ne nl) (ruleTrans fires (selfChk_op p ne))

wfFun_op_v : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap2 natEqF (ap1 Fst p) (natCode 1)) O) ->
  Deriv (eqF (ap1 Fst p) (natCode 7)) ->
  Deriv (eqF (ap1 wfFun p) (ap1 funValidF p))
wfFun_op_v p ne nl h7 =
  let opk = opkg p
      tg = ruleTrans (op_tag p ne) h7
      fires =
        ruleTrans (fork_false_to_snd leafCell wfn_l4 (testHd 3) opk (idxTest_skip get_tag 7 3 opk (wn 7 3 (\ ())) tg))
          (ruleTrans (fork_false_to_snd leafCell wfn_l5 (testHd 4) opk (idxTest_skip get_tag 7 4 opk (wn 7 4 (\ ())) tg))
            (ruleTrans (fork_false_to_snd leafCell wfn_l6 (testHd 5) opk (idxTest_skip get_tag 7 5 opk (wn 7 5 (\ ())) tg))
              (ruleTrans (fork_false_to_snd compCellC wfn_l7 (testHd 6) opk (idxTest_skip get_tag 7 6 opk (wn 7 6 (\ ())) tg))
                         (fork_true_to_fst leafCell wfn_l8 (testHd 7) opk (idxTest_fire get_tag 7 opk tg)))))
  in ruleTrans (toCell p ne nl) (ruleTrans fires (selfChk_op p ne))
