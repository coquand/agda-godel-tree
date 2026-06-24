{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.PrLeafReflOImp -- IMP-FORM leaf (reflO) source/target endpoints, threading
-- the head  Fst p = natCode 1  as the antecedent (and deriving the non-O
-- hypothesis the bare harness needs FROM that head):
--
--   srcF_reflO_himp p : imp (Fst p = natCode 1) (srcF p = tmO)
--   tgtF_reflO_himp p : imp (Fst p = natCode 1) (tgtF p = tmO)
--
-- Needed by the ap2c cRec R-base sub-glue, where the right child pR has head 1
-- (a reflO leaf) but no BARE non-O witness -- only the head antecedent.
--
-- No holes, no postulates, no termination warnings (only the benign
-- RuleInst3:328 unreachable-clauses warning); --safe --without-K --exact-split.

module T4.PrLeafReflOImp where

open import T4.Base

open import T4.PrSrc using ( srcF ; cellNodeSrc )
open import T4.PrTgt using ( tgtF ; cellNodeTgt )
open import T4.PrDev using ( tmOF ; tmOF_val )
open import T4.PrCodeObj using ( tmO )
open import T4.ParsObj using ( stepOf )
open import T4.ProgParse using ( get_tag )
open import T4.FoldRec using ( get_newK )

open import BRA3.PairAlgebra using ( compose1U_eq )
open import BRA3.SubT.NatEq using ( natEqF )
open import T4.ForkImp using ( fork_true_to_fst_imp ; natEqFire_imp )
open import T4.Thm12.ImpHelpers using ( impLift ; impEqTrans ; impCong1 ; impMp ; impRuleSym )
open import BRA3.Contrapositive using ( compI ; identP )
open import BRA3.Classical using ( axContrapos )
open import T4.AdDispatchAux using ( FstO )
open import T4.CtxKit using ( trans2c )
open import T4.DescSndImp using ( neSucc )

import T4.OpaqueHarnessImp

private
  srcStepU : Fun1
  srcStepU = stepOf tmOF cellNodeSrc
  tgtStepU : Fun1
  tgtStepU = stepOf tmOF cellNodeTgt
module Hs = T4.OpaqueHarnessImp.HimpBase Z srcStepU
module Ht = T4.OpaqueHarnessImp.HimpBase Z tgtStepU

------------------------------------------------------------------------
-- ne from the head:  Fst p = natCode 1  =>  p != O .

ne_from_head1 : (p : Term) -> Deriv (imp (eqF (ap1 Fst p) (natCode 1)) (neg (eqF p O)))
ne_from_head1 p =
  let H : Formula
      H = eqF (ap1 Fst p) (natCode 1)
      P : Formula
      P = eqF p O
      Q : Formula
      Q = eqF (natCode 1) O
      leg1 : Deriv (imp H (imp P (eqF (natCode 1) (ap1 Fst p))))
      leg1 = compI (impRuleSym (identP H)) (axK (eqF (natCode 1) (ap1 Fst p)) P)
      a1 : Deriv (imp P (eqF (ap1 Fst p) (ap1 Fst O)))
      a1 = impCong1 Fst p O (identP P)
      bareLeg : Deriv (imp P (eqF (ap1 Fst p) O))
      bareLeg = impEqTrans (ap1 Fst p) (ap1 Fst O) O a1 (impLift FstO)
      leg2 : Deriv (imp H (imp P (eqF (ap1 Fst p) O)))
      leg2 = impLift bareLeg
      combined : Deriv (imp H (imp P Q))
      combined = trans2c (natCode 1) (ap1 Fst p) O leg1 leg2
      contraStep : Deriv (imp H (imp (neg Q) (neg P)))
      contraStep = impMp (impLift (axContrapos P Q)) combined
  in impMp contraStep (impLift (neSucc O))

------------------------------------------------------------------------
-- imp-form reflO endpoints.

srcF_reflO_himp : (p : Term) -> Deriv (imp (eqF (ap1 Fst p) (natCode 1)) (eqF (ap1 srcF p) tmO))
srcF_reflO_himp p =
  let H = eqF (ap1 Fst p) (natCode 1)
      ne = ne_from_head1 p
      opk = Hs.opkg p
      op_tag_ne : Deriv (imp (neg (eqF p O)) (eqF (ap1 get_tag opk) (ap1 Fst p)))
      op_tag_ne = impEqTrans (ap1 get_tag opk) (ap1 Fst (ap1 get_newK opk)) (ap1 Fst p)
                    (impLift (compose1U_eq Fst get_newK opk)) (impCong1 Fst (ap1 get_newK opk) p (Hs.op_newK_imp p))
      gtag : Deriv (imp H (eqF (ap1 get_tag opk) (natCode 1)))
      gtag = impEqTrans (ap1 get_tag opk) (ap1 Fst p) (natCode 1) (compI ne op_tag_ne) (identP H)
      cell_fires : Deriv (imp H (eqF (ap1 srcStepU opk) (ap1 tmOF opk)))
      cell_fires = fork_true_to_fst_imp H tmOF cellNodeSrc (C natEqF get_tag (constN 1)) opk
                     (natEqFire_imp H get_tag 1 opk gtag)
  in impEqTrans (ap1 srcF p) (ap1 srcStepU opk) tmO
       (compI ne (Hs.opUnfold_imp p))
       (impEqTrans (ap1 srcStepU opk) (ap1 tmOF opk) tmO cell_fires (impLift (tmOF_val opk)))

tgtF_reflO_himp : (p : Term) -> Deriv (imp (eqF (ap1 Fst p) (natCode 1)) (eqF (ap1 tgtF p) tmO))
tgtF_reflO_himp p =
  let H = eqF (ap1 Fst p) (natCode 1)
      ne = ne_from_head1 p
      opk = Ht.opkg p
      op_tag_ne : Deriv (imp (neg (eqF p O)) (eqF (ap1 get_tag opk) (ap1 Fst p)))
      op_tag_ne = impEqTrans (ap1 get_tag opk) (ap1 Fst (ap1 get_newK opk)) (ap1 Fst p)
                    (impLift (compose1U_eq Fst get_newK opk)) (impCong1 Fst (ap1 get_newK opk) p (Ht.op_newK_imp p))
      gtag : Deriv (imp H (eqF (ap1 get_tag opk) (natCode 1)))
      gtag = impEqTrans (ap1 get_tag opk) (ap1 Fst p) (natCode 1) (compI ne op_tag_ne) (identP H)
      cell_fires : Deriv (imp H (eqF (ap1 tgtStepU opk) (ap1 tmOF opk)))
      cell_fires = fork_true_to_fst_imp H tmOF cellNodeTgt (C natEqF get_tag (constN 1)) opk
                     (natEqFire_imp H get_tag 1 opk gtag)
  in impEqTrans (ap1 tgtF p) (ap1 tgtStepU opk) tmO
       (compI ne (Ht.opUnfold_imp p))
       (impEqTrans (ap1 tgtStepU opk) (ap1 tmOF opk) tmO cell_fires (impLift (tmOF_val opk)))
