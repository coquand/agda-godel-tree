{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.StepDispatchImp -- the IMP-FORM of the src step-body dispatch (T4.StepDispatch),
-- needed because `byCases` is imp-form.  Generic one-level imp-unfolds:
--   firesTo_imp : imp (test != O) (body = first cell)     (via succForm-imp + condFork_true_nc)
--   restTo_imp  : imp (test  = O) (body = rest)            (via identP + condFork_false)
-- instantiated for the three cascade levels.  All via the T4.ImpEq toolkit
-- (impCongR/impSym/impRuleTrans) + liftP/identP.  No holes, no postulates, no
-- termination warnings; --safe --without-K --exact-split.

module T4.StepDispatchImp where

open import T4.Base

open import T4.ParEnds using
  ( stepBody_src ; inner1 ; inner2
  ; cellSu ; cellAd ; cellRO ; cellRS ; test1 ; test2 ; test3 )
open import T4.ImpEq using ( impCongR ; impSym ; impRuleTrans )

open import BRA3.Church          using ( predecessor ; pi )
open import BRA3.Dispatch        using ( condFork ; condFork_true_nc ; condFork_false )
open import BRA3.ChurchPredLemmas using ( L_sp )
open import BRA3.Contrapositive  using ( liftP ; identP )

------------------------------------------------------------------------
-- Generic one-level imp-unfolds.

firesTo_imp : (body fstCell sndCell test : Fun1) (pkg : Term) ->
  Deriv (eqF (ap1 body pkg)
             (ap2 condFork (ap1 (C pi fstCell sndCell) pkg) (ap1 test pkg))) ->
  Deriv (imp (neg (eqF (ap1 test pkg) O)) (eqF (ap1 body pkg) (ap1 fstCell pkg)))
firesTo_imp body fstCell sndCell test pkg unf =
  let rf : Formula
      rf = neg (eqF (ap1 test pkg) O)
      z : Term
      z = ap1 (C pi fstCell sndCell) pkg
      predT : Term
      predT = ap1 predecessor (ap1 test pkg)
      sf_imp : Deriv (imp rf (eqF (ap1 s predT) (ap1 test pkg)))
      sf_imp = ruleInst 0 (ap1 test pkg) L_sp
      s1 : Deriv (imp rf (eqF (ap1 body pkg) (ap2 condFork z (ap1 test pkg))))
      s1 = liftP rf unf
      s2 : Deriv (imp rf (eqF (ap2 condFork z (ap1 test pkg))
                              (ap2 condFork z (ap1 s predT))))
      s2 = impCongR condFork z (impSym sf_imp)
      s3 : Deriv (imp rf (eqF (ap2 condFork z (ap1 s predT)) (ap1 Fst z)))
      s3 = liftP rf (condFork_true_nc z predT)
      s4 : Deriv (imp rf (eqF (ap1 Fst z) (ap1 fstCell pkg)))
      s4 = liftP rf (ruleTrans (cong1 Fst (ax_C pi fstCell sndCell pkg))
                               (axFst (ap1 fstCell pkg) (ap1 sndCell pkg)))
  in impRuleTrans s1 (impRuleTrans s2 (impRuleTrans s3 s4))

restTo_imp : (body fstCell sndCell test : Fun1) (pkg : Term) ->
  Deriv (eqF (ap1 body pkg)
             (ap2 condFork (ap1 (C pi fstCell sndCell) pkg) (ap1 test pkg))) ->
  Deriv (imp (eqF (ap1 test pkg) O) (eqF (ap1 body pkg) (ap1 sndCell pkg)))
restTo_imp body fstCell sndCell test pkg unf =
  let rf : Formula
      rf = eqF (ap1 test pkg) O
      z : Term
      z = ap1 (C pi fstCell sndCell) pkg
      s1 : Deriv (imp rf (eqF (ap1 body pkg) (ap2 condFork z (ap1 test pkg))))
      s1 = liftP rf unf
      s2 : Deriv (imp rf (eqF (ap2 condFork z (ap1 test pkg)) (ap2 condFork z O)))
      s2 = impCongR condFork z (identP rf)
      s3 : Deriv (imp rf (eqF (ap2 condFork z O) (ap1 Snd z)))
      s3 = liftP rf (condFork_false z)
      s4 : Deriv (imp rf (eqF (ap1 Snd z) (ap1 sndCell pkg)))
      s4 = liftP rf (ruleTrans (cong1 Snd (ax_C pi fstCell sndCell pkg))
                               (axSnd (ap1 fstCell pkg) (ap1 sndCell pkg)))
  in impRuleTrans s1 (impRuleTrans s2 (impRuleTrans s3 s4))

------------------------------------------------------------------------
-- The six instantiations.

to_cellSu_imp : (pkg : Term) ->
  Deriv (imp (neg (eqF (ap1 test1 pkg) O)) (eqF (ap1 stepBody_src pkg) (ap1 cellSu pkg)))
to_cellSu_imp pkg =
  firesTo_imp stepBody_src cellSu inner1 test1 pkg
    (ax_C condFork (C pi cellSu inner1) test1 pkg)

to_inner1_imp : (pkg : Term) ->
  Deriv (imp (eqF (ap1 test1 pkg) O) (eqF (ap1 stepBody_src pkg) (ap1 inner1 pkg)))
to_inner1_imp pkg =
  restTo_imp stepBody_src cellSu inner1 test1 pkg
    (ax_C condFork (C pi cellSu inner1) test1 pkg)

to_cellAd_imp : (pkg : Term) ->
  Deriv (imp (neg (eqF (ap1 test2 pkg) O)) (eqF (ap1 inner1 pkg) (ap1 cellAd pkg)))
to_cellAd_imp pkg =
  firesTo_imp inner1 cellAd inner2 test2 pkg
    (ax_C condFork (C pi cellAd inner2) test2 pkg)

to_inner2_imp : (pkg : Term) ->
  Deriv (imp (eqF (ap1 test2 pkg) O) (eqF (ap1 inner1 pkg) (ap1 inner2 pkg)))
to_inner2_imp pkg =
  restTo_imp inner1 cellAd inner2 test2 pkg
    (ax_C condFork (C pi cellAd inner2) test2 pkg)

to_cellRO_imp : (pkg : Term) ->
  Deriv (imp (neg (eqF (ap1 test3 pkg) O)) (eqF (ap1 inner2 pkg) (ap1 cellRO pkg)))
to_cellRO_imp pkg =
  firesTo_imp inner2 cellRO cellRS test3 pkg
    (ax_C condFork (C pi cellRO cellRS) test3 pkg)

to_cellRS_imp : (pkg : Term) ->
  Deriv (imp (eqF (ap1 test3 pkg) O) (eqF (ap1 inner2 pkg) (ap1 cellRS pkg)))
to_cellRS_imp pkg =
  restTo_imp inner2 cellRO cellRS test3 pkg
    (ax_C condFork (C pi cellRO cellRS) test3 pkg)
