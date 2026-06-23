{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.TriDispatchImp -- the imp-lifted DISPATCH for the triF step-body (first 3b
-- brick: object CR via lifting the green triangle).  triF's cascade
--   stepBody_tri = condFork (pi cellCSu innerO1) test1 ; innerO1 = ... test2 ;
--   innerO2 = condFork (pi cellCRO cellCRS) test3
-- has the SAME shape as stepBody_src, so the generic T4.StepDispatchImp helpers
-- (firesTo_imp / restTo_imp) apply verbatim -- the opaque triF dispatch is free.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.TriDispatchImp where

open import T4.Base

open import T4.TriF using
  ( stepBody_tri ; innerO1 ; innerO2
  ; cellCSu ; cellCAd ; cellCRO ; cellCRS ; test1 ; test2 ; test3 )
open import T4.StepDispatchImp using ( firesTo_imp ; restTo_imp )

open import BRA3.Church   using ( pi )
open import BRA3.Dispatch using ( condFork )

------------------------------------------------------------------------
-- Level 1:  stepBody_tri .

to_cellCSu_imp : (pkg : Term) ->
  Deriv (imp (neg (eqF (ap1 test1 pkg) O)) (eqF (ap1 stepBody_tri pkg) (ap1 cellCSu pkg)))
to_cellCSu_imp pkg =
  firesTo_imp stepBody_tri cellCSu innerO1 test1 pkg
    (ax_C condFork (C pi cellCSu innerO1) test1 pkg)

to_innerO1_imp : (pkg : Term) ->
  Deriv (imp (eqF (ap1 test1 pkg) O) (eqF (ap1 stepBody_tri pkg) (ap1 innerO1 pkg)))
to_innerO1_imp pkg =
  restTo_imp stepBody_tri cellCSu innerO1 test1 pkg
    (ax_C condFork (C pi cellCSu innerO1) test1 pkg)

------------------------------------------------------------------------
-- Level 2:  innerO1 .

to_cellCAd_imp : (pkg : Term) ->
  Deriv (imp (neg (eqF (ap1 test2 pkg) O)) (eqF (ap1 innerO1 pkg) (ap1 cellCAd pkg)))
to_cellCAd_imp pkg =
  firesTo_imp innerO1 cellCAd innerO2 test2 pkg
    (ax_C condFork (C pi cellCAd innerO2) test2 pkg)

to_innerO2_imp : (pkg : Term) ->
  Deriv (imp (eqF (ap1 test2 pkg) O) (eqF (ap1 innerO1 pkg) (ap1 innerO2 pkg)))
to_innerO2_imp pkg =
  restTo_imp innerO1 cellCAd innerO2 test2 pkg
    (ax_C condFork (C pi cellCAd innerO2) test2 pkg)

------------------------------------------------------------------------
-- Level 3:  innerO2 .

to_cellCRO_imp : (pkg : Term) ->
  Deriv (imp (neg (eqF (ap1 test3 pkg) O)) (eqF (ap1 innerO2 pkg) (ap1 cellCRO pkg)))
to_cellCRO_imp pkg =
  firesTo_imp innerO2 cellCRO cellCRS test3 pkg
    (ax_C condFork (C pi cellCRO cellCRS) test3 pkg)

to_cellCRS_imp : (pkg : Term) ->
  Deriv (imp (eqF (ap1 test3 pkg) O) (eqF (ap1 innerO2 pkg) (ap1 cellCRS pkg)))
to_cellCRS_imp pkg =
  restTo_imp innerO2 cellCRO cellCRS test3 pkg
    (ax_C condFork (C pi cellCRO cellCRS) test3 pkg)
