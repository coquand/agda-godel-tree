{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.PrWfFunLeafImp -- IMP-FORM (Carneiro) leaf extraction for wfFun, threading
-- the funhead  Fst f = natCode k  as the ANTECEDENT (the ap1c/ap2c funhead
-- caseElim of the cov dispatch hands it back as a hypothesis, not a bare Deriv):
--
--   wfFun_op_o_himp f : imp (Fst f = natCode 4) (eqF (ap1 wfFun f) (ap1 funValidF f))
--   ... and _u (5) / _s (3) / _v (7).
--
-- The non-O hypothesis  neg (f = O)  the bare harness needs is DERIVED from the
-- funhead (Fst f = natCode k, k >= 3, so f != O).  The ne-threaded harness ops
-- come from T4.OpaqueHarnessImp.HimpBase rejectCell wfFunStepU.
--
-- No holes, no postulates, no termination warnings (only the benign
-- RuleInst3:328 unreachable-clauses warning); --safe --without-K --exact-split.

module T4.PrWfFunLeafImp where

open import T4.Base

open import T4.PrWfFun
  using ( wfFun ; wfFunNodeCell ; leafCell ; selfChk ; compCellC ; rejectCell
        ; wfn_l4 ; wfn_l5 ; wfn_l6 ; wfn_l7 ; wfn_l8 ; testHd )
open import T4.PrFunValidCanon using ( funValidF )
open import T4.ProgParse using ( get_tag )
open import T4.FoldRec using ( get_newK )
open import T4.ParsObj using ( stepOf )

open import T4.ForkImp
  using ( fork_true_to_fst_imp ; fork_false_to_snd_imp ; natEqFire_imp ; natEqSkip_imp )
open import T4.Thm12.ImpHelpers
  using ( impLift ; impEqTrans ; impCong1 ; impCongL ; impMp ; impRuleSym )
open import T4.AdDispatchAux using ( FstO )
open import T4.CtxKit using ( trans2c )

open import BRA3.PairAlgebra using ( compose1U_eq )
open import BRA3.SubT.NatEq using ( natEqF )
open import BRA3.SubT.V2NatNeq using ( NatNeqWitness ; natEqF_at_neq ; decideNatNeq )
open import BRA3.Contrapositive using ( compI ; identP )
open import BRA3.Classical using ( axContrapos )
open import BRA3.ChurchLeq using ( leq ; T76 )
open import BRA3.ChurchT78 using ( T78 )
open import BRA3.RuleInst2 using ( ruleInst2 )
open import T4.DescSnd using ( posNeqO )

import T4.OpaqueHarnessImp
private
  wfFunStepU : Fun1
  wfFunStepU = stepOf Z wfFunNodeCell
open T4.OpaqueHarnessImp.HimpBase rejectCell wfFunStepU
  using ( opkg ; opUnfold_imp ; op_newK_imp )

------------------------------------------------------------------------
-- natCode k != O  for  k >= 1  (k = 3,4,5,7 here).

natCodeNeqO : (k7 : Nat) -> Deriv (neg (eqF (natCode (suc k7)) O))
natCodeNeqO k7 = posNeqO (natCode (suc k7)) (mp (ruleInst2 0 O 1 (natCode k7) refl T78) (ruleInst 0 (natCode k7) T76))

------------------------------------------------------------------------
-- The shared funhead context.  H = (Fst f = natCode k), opk = opkg f.

module HeadImp (f : Term) (k : Nat) (nek : Deriv (neg (eqF (natCode k) O)))
               (kne1 : (Eq k 1) -> Empty) where
  opk : Term
  opk = opkg f
  H : Formula
  H = eqF (ap1 Fst f) (natCode k)

  -- ne_h : imp H (neg (f = O)).  (f = O => Fst f = Fst O = O = natCode k, absurd.)
  ne_h : Deriv (imp H (neg (eqF f O)))
  ne_h =
    let P : Formula
        P = eqF f O
        Q : Formula
        Q = eqF (natCode k) O
        hsym : Deriv (imp H (eqF (natCode k) (ap1 Fst f)))
        hsym = impRuleSym (identP H)
        leg1 : Deriv (imp H (imp P (eqF (natCode k) (ap1 Fst f))))
        leg1 = compI hsym (axK (eqF (natCode k) (ap1 Fst f)) P)
        a1 : Deriv (imp P (eqF (ap1 Fst f) (ap1 Fst O)))
        a1 = impCong1 Fst f O (identP P)
        bareLeg : Deriv (imp P (eqF (ap1 Fst f) O))
        bareLeg = impEqTrans (ap1 Fst f) (ap1 Fst O) O a1 (impLift FstO)
        leg2 : Deriv (imp H (imp P (eqF (ap1 Fst f) O)))
        leg2 = impLift bareLeg
        combined : Deriv (imp H (imp P Q))
        combined = trans2c (natCode k) (ap1 Fst f) O leg1 leg2
        contraStep : Deriv (imp H (imp (neg Q) (neg P)))
        contraStep = impMp (impLift (axContrapos P Q)) combined
    in impMp contraStep (impLift nek)

  -- get_tag opk = Fst f  (over neg (f = O)), then over H.
  gtag_ne : Deriv (imp (neg (eqF f O)) (eqF (ap1 get_tag opk) (ap1 Fst f)))
  gtag_ne =
    impEqTrans (ap1 get_tag opk) (ap1 Fst (ap1 get_newK opk)) (ap1 Fst f)
      (impLift (compose1U_eq Fst get_newK opk))
      (impCong1 Fst (ap1 get_newK opk) f (op_newK_imp f))
  gtag_h : Deriv (imp H (eqF (ap1 get_tag opk) (ap1 Fst f)))
  gtag_h = compI ne_h gtag_ne
  gtagK_h : Deriv (imp H (eqF (ap1 get_tag opk) (natCode k)))
  gtagK_h = impEqTrans (ap1 get_tag opk) (ap1 Fst f) (natCode k) gtag_h (identP H)

  -- selfChk opk = funValidF f.
  selfChk_ne : Deriv (imp (neg (eqF f O)) (eqF (ap1 selfChk opk) (ap1 funValidF f)))
  selfChk_ne =
    impEqTrans (ap1 selfChk opk) (ap1 funValidF (ap1 get_newK opk)) (ap1 funValidF f)
      (impLift (compose1U_eq funValidF get_newK opk))
      (impCong1 funValidF (ap1 get_newK opk) f (op_newK_imp f))
  selfChk_h : Deriv (imp H (eqF (ap1 selfChk opk) (ap1 funValidF f)))
  selfChk_h = compI ne_h selfChk_ne

  -- wfFun f = wfFunStepU opk  (opUnfold), then to the node cell.
  opUnfold_h : Deriv (imp H (eqF (ap1 wfFun f) (ap1 wfFunStepU opk)))
  opUnfold_h = compI ne_h (opUnfold_imp f)
  test1At_h : Deriv (imp H (eqF (ap1 (C natEqF get_tag (constN 1)) opk) (ap2 natEqF (ap1 Fst f) (natCode 1))))
  test1At_h =
    impEqTrans (ap1 (C natEqF get_tag (constN 1)) opk)
               (ap2 natEqF (ap1 get_tag opk) (ap1 (constN 1) opk))
               (ap2 natEqF (ap1 Fst f) (natCode 1))
      (impLift (ax_C natEqF get_tag (constN 1) opk))
      (impEqTrans (ap2 natEqF (ap1 get_tag opk) (ap1 (constN 1) opk))
                  (ap2 natEqF (ap1 Fst f) (ap1 (constN 1) opk))
                  (ap2 natEqF (ap1 Fst f) (natCode 1))
        (impCongL natEqF (ap1 get_tag opk) (ap1 Fst f) (ap1 (constN 1) opk) gtag_h)
        (impLift (congR natEqF (ap1 Fst f) (constN_eq 1 opk))))
  test1skip_h : Deriv (imp H (eqF (ap1 (C natEqF get_tag (constN 1)) opk) O))
  test1skip_h =
    impEqTrans (ap1 (C natEqF get_tag (constN 1)) opk)
               (ap2 natEqF (ap1 Fst f) (natCode 1)) O
      test1At_h
      (impEqTrans (ap2 natEqF (ap1 Fst f) (natCode 1)) (ap2 natEqF (natCode k) (natCode 1)) O
        (impCongL natEqF (ap1 Fst f) (natCode k) (natCode 1) (identP H))
        (impLift (natEqF_at_neq k 1 (decideNatNeq k 1 kne1))))
  toNode_h : Deriv (imp H (eqF (ap1 wfFun f) (ap1 wfFunNodeCell opk)))
  toNode_h =
    impEqTrans (ap1 wfFun f) (ap1 wfFunStepU opk) (ap1 wfFunNodeCell opk)
      opUnfold_h
      (fork_false_to_snd_imp H Z wfFunNodeCell (C natEqF get_tag (constN 1)) opk test1skip_h)

  -- wn helper for the cascade.
  wn : (m kk : Nat) -> ((Eq m kk) -> Empty) -> NatNeqWitness m kk
  wn m kk pf = decideNatNeq m kk pf

------------------------------------------------------------------------
-- The four leaf extractions (cascade on get_tag = natCode k -> leafCell).

wfFun_op_s_himp : (f : Term) -> Deriv (imp (eqF (ap1 Fst f) (natCode 3)) (eqF (ap1 wfFun f) (ap1 funValidF f)))
wfFun_op_s_himp f =
  let open HeadImp f 3 (natCodeNeqO 2) (\ ())
      fires = fork_true_to_fst_imp H leafCell wfn_l4 (testHd 3) opk (natEqFire_imp H get_tag 3 opk gtagK_h)
  in impEqTrans (ap1 wfFun f) (ap1 wfFunNodeCell opk) (ap1 funValidF f)
       toNode_h (impEqTrans (ap1 wfFunNodeCell opk) (ap1 leafCell opk) (ap1 funValidF f) fires selfChk_h)

wfFun_op_o_himp : (f : Term) -> Deriv (imp (eqF (ap1 Fst f) (natCode 4)) (eqF (ap1 wfFun f) (ap1 funValidF f)))
wfFun_op_o_himp f =
  let open HeadImp f 4 (natCodeNeqO 3) (\ ())
      fires =
        impEqTrans (ap1 wfFunNodeCell opk) (ap1 wfn_l4 opk) (ap1 leafCell opk)
          (fork_false_to_snd_imp H leafCell wfn_l4 (testHd 3) opk (natEqSkip_imp H get_tag 4 3 opk (wn 4 3 (\ ())) gtagK_h))
          (fork_true_to_fst_imp H leafCell wfn_l5 (testHd 4) opk (natEqFire_imp H get_tag 4 opk gtagK_h))
  in impEqTrans (ap1 wfFun f) (ap1 wfFunNodeCell opk) (ap1 funValidF f)
       toNode_h (impEqTrans (ap1 wfFunNodeCell opk) (ap1 leafCell opk) (ap1 funValidF f) fires selfChk_h)

wfFun_op_u_himp : (f : Term) -> Deriv (imp (eqF (ap1 Fst f) (natCode 5)) (eqF (ap1 wfFun f) (ap1 funValidF f)))
wfFun_op_u_himp f =
  let open HeadImp f 5 (natCodeNeqO 4) (\ ())
      fires =
        impEqTrans (ap1 wfFunNodeCell opk) (ap1 wfn_l4 opk) (ap1 leafCell opk)
          (fork_false_to_snd_imp H leafCell wfn_l4 (testHd 3) opk (natEqSkip_imp H get_tag 5 3 opk (wn 5 3 (\ ())) gtagK_h))
          (impEqTrans (ap1 wfn_l4 opk) (ap1 wfn_l5 opk) (ap1 leafCell opk)
            (fork_false_to_snd_imp H leafCell wfn_l5 (testHd 4) opk (natEqSkip_imp H get_tag 5 4 opk (wn 5 4 (\ ())) gtagK_h))
            (fork_true_to_fst_imp H leafCell wfn_l6 (testHd 5) opk (natEqFire_imp H get_tag 5 opk gtagK_h)))
  in impEqTrans (ap1 wfFun f) (ap1 wfFunNodeCell opk) (ap1 funValidF f)
       toNode_h (impEqTrans (ap1 wfFunNodeCell opk) (ap1 leafCell opk) (ap1 funValidF f) fires selfChk_h)

wfFun_op_v_himp : (f : Term) -> Deriv (imp (eqF (ap1 Fst f) (natCode 7)) (eqF (ap1 wfFun f) (ap1 funValidF f)))
wfFun_op_v_himp f =
  let open HeadImp f 7 (natCodeNeqO 6) (\ ())
      fires =
        impEqTrans (ap1 wfFunNodeCell opk) (ap1 wfn_l4 opk) (ap1 leafCell opk)
          (fork_false_to_snd_imp H leafCell wfn_l4 (testHd 3) opk (natEqSkip_imp H get_tag 7 3 opk (wn 7 3 (\ ())) gtagK_h))
          (impEqTrans (ap1 wfn_l4 opk) (ap1 wfn_l5 opk) (ap1 leafCell opk)
            (fork_false_to_snd_imp H leafCell wfn_l5 (testHd 4) opk (natEqSkip_imp H get_tag 7 4 opk (wn 7 4 (\ ())) gtagK_h))
            (impEqTrans (ap1 wfn_l5 opk) (ap1 wfn_l6 opk) (ap1 leafCell opk)
              (fork_false_to_snd_imp H leafCell wfn_l6 (testHd 5) opk (natEqSkip_imp H get_tag 7 5 opk (wn 7 5 (\ ())) gtagK_h))
              (impEqTrans (ap1 wfn_l6 opk) (ap1 wfn_l7 opk) (ap1 leafCell opk)
                (fork_false_to_snd_imp H compCellC wfn_l7 (testHd 6) opk (natEqSkip_imp H get_tag 7 6 opk (wn 7 6 (\ ())) gtagK_h))
                (fork_true_to_fst_imp H leafCell wfn_l8 (testHd 7) opk (natEqFire_imp H get_tag 7 opk gtagK_h)))))
  in impEqTrans (ap1 wfFun f) (ap1 wfFunNodeCell opk) (ap1 funValidF f)
       toNode_h (impEqTrans (ap1 wfFunNodeCell opk) (ap1 leafCell opk) (ap1 funValidF f) fires selfChk_h)
