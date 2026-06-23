{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.CertHeadSuObj -- object per-step SU head-preservation (the su-leg of
-- objJoinClash): a valid step d != O whose source is su-headed has a su-headed
-- target.  Unlike ze (ex falso), su# CAN step (cSu), so this is a genuine
-- preservation: src head = tagSu PINS tag 1, whose tgt cell tCellSu is su-headed;
-- the tag != 1 branch is ex falso (src head = natCode 2 vs tagSu = natCode 1).
--
--   certHeadSu_step : d != O -> Fst(src d) = tagSu -> Fst(tgt d) = tagSu
--
-- src-pkg and tgt-pkg differ (different fold step), bridged via OpaqueTag.test1_op
-- (both = natEqF (Fst d)(natCode 1)).  No holes, no postulates; --safe.

module T4.CertHeadSuObj where

open import T4.Base

open import T4.ParEnds using
  ( stepBody_src ; stepBody_tgt ; inner1 ; inner1_t ; tCellSu ; cellSu
  ; test1 ; src ; tgt ; srcBase ; stepFun_src ; stepFun_tgt )
open import T4.SrcHeadStab using ( srcUnfold ; tgtUnfold )
open import T4.CellHead using ( hd_cellSu )
open import T4.StepDispatchImp using ( to_inner1_imp ; firesTo_imp )
open import T4.SuLegParts using ( inner1HeadIs2 ; refuter21_imp )
open import T4.OpaqueTag using ( test1_op )
open import T4.ImpEq using ( impCong1 ; impRuleTrans ; impSym )
open import T4.TrsCodeObj using ( tagSu )

open import BRA3.Logic          using ( impTrans )
open import BRA3.Classical      using ( axContrapos )
open import BRA3.Contrapositive using ( liftP ; identP )
open import BRA3.Church         using ( predecessor ; pi )
open import BRA3.Dispatch       using ( condFork )
open import T4.CoVSpec          using ( cov_spec )
open import T4.PHP              using ( byCases )

certHeadSu_step : (d : Term) ->
  Deriv (neg (eqF d O)) ->
  Deriv (eqF (ap1 Fst (ap1 src d)) tagSu) ->
  Deriv (eqF (ap1 Fst (ap1 tgt d)) tagSu)
certHeadSu_step d ne hyp =
  let predd : Term
      predd = ap1 predecessor d
      sState : Term
      sState = ap1 Snd (ap2 (cov_spec srcBase stepFun_src) O predd)
      tState : Term
      tState = ap1 Snd (ap2 (cov_spec srcBase stepFun_tgt) O predd)
      spkg : Term
      spkg = ap2 pi predd sState
      tpkg : Term
      tpkg = ap2 pi predd tState
      goal : Formula
      goal = eqF (ap1 Fst (ap1 tgt d)) tagSu
      a1 : Formula
      a1 = eqF (ap1 test1 spkg) O
      -- src/tgt heads exposed.
      srcUnf : Deriv (eqF (ap1 Fst (ap1 src d)) (ap1 Fst (ap1 stepBody_src spkg)))
      srcUnf = cong1 Fst (srcUnfold d ne)
      tgtUnf : Deriv (eqF (ap1 Fst (ap1 tgt d)) (ap1 Fst (ap1 stepBody_tgt tpkg)))
      tgtUnf = cong1 Fst (tgtUnfold d ne)
      gSrc : Deriv (eqF (ap1 Fst (ap1 stepBody_src spkg)) tagSu)
      gSrc = ruleTrans (ruleSym srcUnf) hyp
      -- bridge:  test1 spkg = test1 tpkg .
      eqST : Deriv (eqF (ap1 test1 spkg) (ap1 test1 tpkg))
      eqST = ruleTrans (test1_op d sState ne) (ruleSym (test1_op d tState ne))
      -- h1:  test1 spkg = O  =>  src head = natCode 2, clash with tagSu = natCode 1.
      h1 : Deriv (imp a1 goal)
      h1 = impTrans
             (impRuleTrans
               (impSym (impRuleTrans (impCong1 Fst (to_inner1_imp spkg))
                                     (liftP a1 (inner1HeadIs2 spkg))))
               (liftP a1 gSrc))
             (refuter21_imp goal)
      -- h2:  test1 spkg != O  =>  tgt = tCellSu, head = natCode 1 = tagSu.
      to_tCS : Deriv (imp (neg (eqF (ap1 test1 tpkg) O))
                          (eqF (ap1 stepBody_tgt tpkg) (ap1 tCellSu tpkg)))
      to_tCS = firesTo_imp stepBody_tgt tCellSu inner1_t test1 tpkg
                 (ax_C condFork (C pi tCellSu inner1_t) test1 tpkg)
      -- neg(test1 spkg=O) => neg(test1 tpkg=O)  (via eqST, contraposition).
      ntpkg : Deriv (imp (neg a1) (neg (eqF (ap1 test1 tpkg) O)))
      ntpkg = mp (axContrapos (eqF (ap1 test1 tpkg) O) a1)
                 (impRuleTrans (liftP (eqF (ap1 test1 tpkg) O) eqST)
                               (identP (eqF (ap1 test1 tpkg) O)))
      h2 : Deriv (imp (neg a1) goal)
      h2 = impRuleTrans (liftP (neg a1) tgtUnf)
             (impRuleTrans (impCong1 Fst (impTrans ntpkg to_tCS))
                           (liftP (neg a1) (hd_cellSu tpkg)))
  in byCases a1 goal h1 h2
