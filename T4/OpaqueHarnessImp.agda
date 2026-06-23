{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.OpaqueHarnessImp -- the IMP-FORM (Carneiro) opaque harness: the same
-- recovery as T4.OpaqueHarness but carrying the non-O hypothesis  neg (d = O)
-- as an ANTECEDENT, since the covFuel tag dispatch (object caseElim) hands it
-- back as an antecedent rather than a bare Deriv.  Every ne-use is via
-- foldOpaque -> succForm -> L_sp, which is ALREADY imp-form, so the lift is a
-- clean impCong1 / impEqTrans / impLift chain.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.OpaqueHarnessImp where

open import T4.Base

open import T4.DerCodeS using ( dtag ; pArg ; pL ; pR )
open import T4.CoVSpec using ( cov_spec )
open import T4.LenR    using ( get_rc )
open import T4.FoldRec using ( fold ; get_newK ; get_newK_at_pi )
open import T4.BinTree using ( nIdx ; lIdx ; rIdx )
open import T4.BinTreeCovInd using ( foldStepRaw )

open import BRA3.Church      using ( pi ; predecessor )
open import BRA3.ChurchPredLemmas using ( L_sp )
open import BRA3.PairAlgebra using ( Post ; axPost ; compose1U ; compose1U_eq )
open import T4.Thm12.ImpHelpers using ( impLift ; impCong1 ; impRuleSym ; impEqTrans )

------------------------------------------------------------------------
-- foldOpaque, imp-form over  neg (d = O) .

foldOpaque_imp : (g : Fun1) (h : Fun2) (d : Term) ->
  Deriv (imp (neg (eqF d O))
             (eqF (ap1 (fold g h) d)
                  (ap2 h (ap1 predecessor d)
                         (ap1 Snd (ap2 (cov_spec g h) O (ap1 predecessor d))))))
foldOpaque_imp g h d =
  let dEq_imp : Deriv (imp (neg (eqF d O)) (eqF d (ap1 s (ap1 predecessor d))))
      dEq_imp = impRuleSym (ruleInst 0 d L_sp)
      liftFold_imp : Deriv (imp (neg (eqF d O))
                              (eqF (ap1 (fold g h) d) (ap1 (fold g h) (ap1 s (ap1 predecessor d)))))
      liftFold_imp = impCong1 (fold g h) d (ap1 s (ap1 predecessor d)) dEq_imp
  in impEqTrans (ap1 (fold g h) d) (ap1 (fold g h) (ap1 s (ap1 predecessor d)))
                (ap2 h (ap1 predecessor d)
                       (ap1 Snd (ap2 (cov_spec g h) O (ap1 predecessor d))))
       liftFold_imp (impLift (foldStepRaw g h (ap1 predecessor d)))

------------------------------------------------------------------------
-- The harness, parameterised by sbf.

-- Generalised over the fold BASE  g  (analogue of T4.OpaqueHarness.HBase): the
-- accessors are base-independent; only prevS / opUnfold_imp thread  g .  The
-- original  Himp  is  HimpBase Z  (below).  Lets the strict  wfRed  (base
-- rejectCell) reuse the ne-threaded harness.
module HimpBase (g sbf : Fun1) where

  prevS : Term -> Term
  prevS p = ap1 Snd (ap2 (cov_spec g (Post sbf pi)) O (ap1 predecessor p))

  opkg : Term -> Term
  opkg p = ap2 pi (ap1 predecessor p) (prevS p)

  opUnfold_imp : (p : Term) ->
    Deriv (imp (neg (eqF p O)) (eqF (ap1 (fold g (Post sbf pi)) p) (ap1 sbf (opkg p))))
  opUnfold_imp p =
    impEqTrans (ap1 (fold g (Post sbf pi)) p)
               (ap2 (Post sbf pi) (ap1 predecessor p) (prevS p))
               (ap1 sbf (opkg p))
      (foldOpaque_imp g (Post sbf pi) p)
      (impLift (axPost sbf pi (ap1 predecessor p) (prevS p)))

  op_newK_imp : (p : Term) ->
    Deriv (imp (neg (eqF p O)) (eqF (ap1 get_newK (opkg p)) p))
  op_newK_imp p =
    impEqTrans (ap1 get_newK (opkg p)) (ap1 s (ap1 predecessor p)) p
      (impLift (get_newK_at_pi (ap1 predecessor p) (prevS p)))
      (ruleInst 0 p L_sp)

  op_rc_imp : (p : Term) ->
    Deriv (imp (neg (eqF p O)) (eqF (ap1 get_rc (opkg p)) (ap1 Snd p)))
  op_rc_imp p =
    impEqTrans (ap1 get_rc (opkg p)) (ap1 Snd (ap1 get_newK (opkg p))) (ap1 Snd p)
      (impLift (compose1U_eq Snd get_newK (opkg p)))
      (impCong1 Snd (ap1 get_newK (opkg p)) p (op_newK_imp p))

  op_nIdx_imp : (p : Term) ->
    Deriv (imp (neg (eqF p O)) (eqF (ap1 nIdx (opkg p)) (dtag p)))
  op_nIdx_imp p =
    impEqTrans (ap1 nIdx (opkg p)) (ap1 Fst (ap1 get_rc (opkg p))) (dtag p)
      (impLift (compose1U_eq Fst get_rc (opkg p)))
      (impCong1 Fst (ap1 get_rc (opkg p)) (ap1 Snd p) (op_rc_imp p))

  argIdx : Fun1
  argIdx = compose1U Snd get_rc

  op_argIdx_imp : (p : Term) ->
    Deriv (imp (neg (eqF p O)) (eqF (ap1 argIdx (opkg p)) (pArg p)))
  op_argIdx_imp p =
    impEqTrans (ap1 argIdx (opkg p)) (ap1 Snd (ap1 get_rc (opkg p))) (pArg p)
      (impLift (compose1U_eq Snd get_rc (opkg p)))
      (impCong1 Snd (ap1 get_rc (opkg p)) (ap1 Snd p) (op_rc_imp p))

  op_pL_imp : (p : Term) ->
    Deriv (imp (neg (eqF p O)) (eqF (ap1 lIdx (opkg p)) (pL p)))
  op_pL_imp p =
    impEqTrans (ap1 lIdx (opkg p)) (ap1 Fst (ap1 argIdx (opkg p))) (pL p)
      (impLift (compose1U_eq Fst (compose1U Snd get_rc) (opkg p)))
      (impCong1 Fst (ap1 argIdx (opkg p)) (pArg p) (op_argIdx_imp p))

  op_pR_imp : (p : Term) ->
    Deriv (imp (neg (eqF p O)) (eqF (ap1 rIdx (opkg p)) (pR p)))
  op_pR_imp p =
    impEqTrans (ap1 rIdx (opkg p)) (ap1 Snd (ap1 argIdx (opkg p))) (pR p)
      (impLift (compose1U_eq Snd (compose1U Snd get_rc) (opkg p)))
      (impCong1 Snd (ap1 argIdx (opkg p)) (pArg p) (op_argIdx_imp p))

-- The original ne-threaded harness:  fold base = Z  (triF / srcF / tgtF).
module Himp (sbf : Fun1) where
  open HimpBase Z sbf public
