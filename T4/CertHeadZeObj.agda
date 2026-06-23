{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.CertHeadZeObj -- object per-step head-stability (the d != O core of the
-- last arrow  objJoinClash ): a valid step from a ze-headed term is impossible,
-- i.e.  hd(src d) = tagZe  with  d != O  is contradictory (ex falso any Q),
-- because for d != O the src step-body rebuilds a SUCCESSOR-headed node.
--
-- Assembly: nested `imp_byCases` over the test cascade (T4.StepDispatchImp),
-- each leaf a successor-headed cell (T4.CellHead), the contradiction packaged
-- via the single/double imp-lift toolkits (T4.ImpEq / T4.ImpImpEq).
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.CertHeadZeObj where

open import T4.Base

open import T4.ParEnds using
  ( stepBody_src ; inner1 ; inner2
  ; cellSu ; cellAd ; cellRO ; cellRS ; test1 ; test2 ; test3 ; src )
open import T4.SrcHeadStab using ( srcUnfold )
open import T4.CellHead using ( hd_cellSu ; hd_cellAd ; hd_cellRO ; hd_cellRS )
open import T4.StepDispatchImp using
  ( to_cellSu_imp ; to_inner1_imp ; to_cellAd_imp ; to_inner2_imp
  ; to_cellRO_imp ; to_cellRS_imp )
open import T4.ImpEq    using ( impSym ; impRuleTrans )
open import T4.ImpImpEq using ( impImpMp ; impImpCong1 ; impImpSym ; impImpRuleTrans )
open import T4.TrsCodeObj using ( tagZe )

open import BRA3.Logic          using ( impTrans )
open import BRA3.Contrapositive using ( liftP ; identP )
open import BRA3.ChurchT80      using ( succEqO_to_anything )
open import T4.ImpExtras        using ( imp_byCases )

------------------------------------------------------------------------
-- A successor head is absurd against tagZe:  H = s W  =>  imp (H = tagZe) Q .

cellHeadAbsurd : (H W : Term) (Q : Formula) ->
  Deriv (eqF H (ap1 s W)) -> Deriv (imp (eqF H tagZe) Q)
cellHeadAbsurd H W Q hd =
  impTrans (impRuleTrans (impSym (liftP (eqF H tagZe) hd))
                         (identP (eqF H tagZe)))
           (succEqO_to_anything W Q)

------------------------------------------------------------------------
-- One cascade level:  if both children's heads are absurd, so is the body's.

absurdBody : (body fstCell sndCell test : Fun1) (pkg : Term) (Q : Formula) ->
  Deriv (imp (neg (eqF (ap1 test pkg) O)) (eqF (ap1 body pkg) (ap1 fstCell pkg))) ->
  Deriv (imp (eqF (ap1 test pkg) O) (eqF (ap1 body pkg) (ap1 sndCell pkg))) ->
  Deriv (imp (eqF (ap1 Fst (ap1 fstCell pkg)) tagZe) Q) ->
  Deriv (imp (eqF (ap1 Fst (ap1 sndCell pkg)) tagZe) Q) ->
  Deriv (imp (eqF (ap1 Fst (ap1 body pkg)) tagZe) Q)
absurdBody body fstCell sndCell test pkg Q firesImp restImp fstAbsurd sndAbsurd =
  let rf : Formula
      rf = eqF (ap1 Fst (ap1 body pkg)) tagZe
      ta : Formula
      ta = eqF (ap1 test pkg) O
      bd : Term
      bd = ap1 Fst (ap1 body pkg)
      -- the body-head fact, weakened under each branch antecedent.
      rfUnderNA : Deriv (imp rf (imp (neg ta) (eqF bd tagZe)))
      rfUnderNA = impTrans (identP rf) (axK rf (neg ta))
      rfUnderTA : Deriv (imp rf (imp ta (eqF bd tagZe)))
      rfUnderTA = impTrans (identP rf) (axK rf ta)
      -- neg-ta branch: body = fstCell, so bd = Fst fstCell, contradicting rf.
      fcZe : Deriv (imp rf (imp (neg ta) (eqF (ap1 Fst (ap1 fstCell pkg)) tagZe)))
      fcZe = impImpRuleTrans rf (neg ta)
               (impImpSym rf (neg ta) (impImpCong1 rf (neg ta) Fst (liftP rf firesImp)))
               rfUnderNA
      hh2 : Deriv (imp rf (imp (neg ta) Q))
      hh2 = impImpMp rf (neg ta) (eqF (ap1 Fst (ap1 fstCell pkg)) tagZe) Q
              (liftP rf (liftP (neg ta) fstAbsurd)) fcZe
      -- ta branch: body = sndCell, so bd = Fst sndCell, contradicting rf.
      scZe : Deriv (imp rf (imp ta (eqF (ap1 Fst (ap1 sndCell pkg)) tagZe)))
      scZe = impImpRuleTrans rf ta
               (impImpSym rf ta (impImpCong1 rf ta Fst (liftP rf restImp)))
               rfUnderTA
      hh1 : Deriv (imp rf (imp ta Q))
      hh1 = impImpMp rf ta (eqF (ap1 Fst (ap1 sndCell pkg)) tagZe) Q
              (liftP rf (liftP ta sndAbsurd)) scZe
  in imp_byCases rf ta Q hh1 hh2

------------------------------------------------------------------------
-- The three cascade levels (cells are successor-headed: cellSu=1, rest=2).

absurd_inner2 : (pkg : Term) (Q : Formula) ->
  Deriv (imp (eqF (ap1 Fst (ap1 inner2 pkg)) tagZe) Q)
absurd_inner2 pkg Q =
  absurdBody inner2 cellRO cellRS test3 pkg Q
    (to_cellRO_imp pkg) (to_cellRS_imp pkg)
    (cellHeadAbsurd (ap1 Fst (ap1 cellRO pkg)) (natCode 1) Q (hd_cellRO pkg))
    (cellHeadAbsurd (ap1 Fst (ap1 cellRS pkg)) (natCode 1) Q (hd_cellRS pkg))

absurd_inner1 : (pkg : Term) (Q : Formula) ->
  Deriv (imp (eqF (ap1 Fst (ap1 inner1 pkg)) tagZe) Q)
absurd_inner1 pkg Q =
  absurdBody inner1 cellAd inner2 test2 pkg Q
    (to_cellAd_imp pkg) (to_inner2_imp pkg)
    (cellHeadAbsurd (ap1 Fst (ap1 cellAd pkg)) (natCode 1) Q (hd_cellAd pkg))
    (absurd_inner2 pkg Q)

absurd_SB : (pkg : Term) (Q : Formula) ->
  Deriv (imp (eqF (ap1 Fst (ap1 stepBody_src pkg)) tagZe) Q)
absurd_SB pkg Q =
  absurdBody stepBody_src cellSu inner1 test1 pkg Q
    (to_cellSu_imp pkg) (to_inner1_imp pkg)
    (cellHeadAbsurd (ap1 Fst (ap1 cellSu pkg)) O Q (hd_cellSu pkg))
    (absurd_inner1 pkg Q)

------------------------------------------------------------------------
-- The d != O head-stability core:  hd(src d) = tagZe  is ex-falso.

certHeadZe_step : (d : Term) (Q : Formula) ->
  Deriv (neg (eqF d O)) ->
  Deriv (eqF (ap1 Fst (ap1 src d)) tagZe) ->
  Deriv Q
certHeadZe_step d Q ne hyp =
  mp (absurd_SB _ Q)
     (ruleTrans (ruleSym (cong1 Fst (srcUnfold d ne))) hyp)
