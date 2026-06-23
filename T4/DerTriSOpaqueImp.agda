{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.DerTriSOpaqueImp -- the IMP-FORM (htag-carrying) opaque triFSized equations.
-- Same content as T4.DerTriSOpaque, but the tag premise  dtag p = dgK  is carried
-- as the ANTECEDENT  htag  (not a bare Deriv), as the object tag dispatch supplies
-- it (caseElim exposes the tag equality as a hypothesis -- no deduction theorem).
-- The tag-dependent cascade fires use the imp-form fork primitives (T4.ForkImp);
-- the (tag-independent) child recovery + cell value are impLift'd.
--
-- THIS FILE: the four non-Ad cases.
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.DerTriSOpaqueImp where

open import T4.Base

open import T4.DerCodeS using ( szDerZe ; szDerSu ; szDerAd ; dtag ; pArg ; pL ; pR )
open import T4.DerCodeSFun using ( szDerSuF ; szDerSuF_eq ; szDerAdF ; szDerAdF_eq )
open import T4.DerCode using ( dgZe ; dgSu ; dgRO ; dgRS )
open import T4.DerTriS
  using ( triStep ; triFSized
        ; cellTriZe ; cellTriSu ; cellTriRO ; cellTriRS
        ; triRestSu ; triRestAd ; triRestRO ; triRestRS ; adCellTriS
        ; cellTriZe_eq )
open import T4.WfRedSized using ( w10 ; w20 ; w30 ; w40 )
open import T4.WfRedExtract using ( argValueBound ; pLValueBound ; pRValueBound )
open import T4.OpaqueLookup using ( lookup_op )
open import T4.FoldRec using ( lookupAt )
open import T4.BinTree using ( nIdx ; lIdx ; rIdx )

open import T4.DerSrc
  using ( testEq ; w21 ; w31 ; w32 ; w41 ; w42 ; w43 )
open import T4.ForkImp
  using ( testEq_fire_imp ; testEq_skip_imp
        ; fork_true_to_fst_imp ; fork_false_to_snd_imp )

open import BRA3.Church      using ( predecessor )
open import BRA3.PairAlgebra using ( compose1U_eq )
open import BRA3.Logic       using ( prependEqLeft )
open import T4.Thm12.ImpHelpers using ( impLift ; impEqTrans )

import T4.OpaqueHarness
open T4.OpaqueHarness.H triStep

------------------------------------------------------------------------
-- The recovered-label premise, carried under htag = (dtag p = dgK).

private
  nieqImp : (p : Term) -> Deriv (neg (eqF p O)) -> (dgK : Term) ->
    Deriv (imp (eqF (dtag p) dgK) (eqF (ap1 nIdx (opkg p)) dgK))
  nieqImp p ne dgK =
    prependEqLeft (ap1 nIdx (opkg p)) (dtag p) dgK (op_nIdx p ne)

------------------------------------------------------------------------

triFSized_op_Ze_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (eqF (dtag p) dgZe) (eqF (ap1 triFSized p) szDerZe))
triFSized_op_Ze_imp p ne =
  let H : Formula
      H = eqF (dtag p) dgZe
      opk : Term
      opk = opkg p
      nieq : Deriv (imp H (eqF (ap1 nIdx opk) dgZe))
      nieq = nieqImp p ne dgZe
      cell_fires : Deriv (imp H (eqF (ap1 triStep opk) (ap1 cellTriZe opk)))
      cell_fires = fork_true_to_fst_imp H cellTriZe triRestSu (testEq 0) opk
                     (testEq_fire_imp H 0 opk nieq)
  in impEqTrans (ap1 triFSized p) (ap1 triStep opk) szDerZe
       (impLift {H} (opUnfold p ne))
       (impEqTrans (ap1 triStep opk) (ap1 cellTriZe opk) szDerZe
         cell_fires (impLift {H} (cellTriZe_eq opk)))

triFSized_op_Su_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (eqF (dtag p) dgSu)
             (eqF (ap1 triFSized p) (szDerSu (ap1 triFSized (pArg p)))))
triFSized_op_Su_imp p ne =
  let H : Formula
      H = eqF (dtag p) dgSu
      opk : Term
      opk = opkg p
      nieq : Deriv (imp H (eqF (ap1 nIdx opk) dgSu))
      nieq = nieqImp p ne dgSu
      cell_fires : Deriv (imp H (eqF (ap1 triStep opk) (ap1 cellTriSu opk)))
      cell_fires =
        impEqTrans (ap1 triStep opk) (ap1 triRestSu opk) (ap1 cellTriSu opk)
          (fork_false_to_snd_imp H cellTriZe triRestSu (testEq 0) opk
             (testEq_skip_imp H 1 0 opk w10 nieq))
          (fork_true_to_fst_imp H cellTriSu triRestAd (testEq 1) opk
             (testEq_fire_imp H 1 opk nieq))
      recArg : Deriv (eqF (ap1 (lookupAt argIdx) opk) (ap1 triFSized (pArg p)))
      recArg = lookup_op Z triStep argIdx (ap1 predecessor p) (pArg p)
                 (op_argIdx p ne) (argValueBound p ne)
      cell_val : Deriv (eqF (ap1 cellTriSu opk) (szDerSu (ap1 triFSized (pArg p))))
      cell_val =
        ruleTrans (compose1U_eq szDerSuF (lookupAt argIdx) opk)
          (ruleTrans (cong1 szDerSuF recArg) (szDerSuF_eq (ap1 triFSized (pArg p))))
  in impEqTrans (ap1 triFSized p) (ap1 triStep opk) (szDerSu (ap1 triFSized (pArg p)))
       (impLift {H} (opUnfold p ne))
       (impEqTrans (ap1 triStep opk) (ap1 cellTriSu opk) (szDerSu (ap1 triFSized (pArg p)))
         cell_fires (impLift {H} cell_val))

triFSized_op_RO_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (eqF (dtag p) dgRO)
             (eqF (ap1 triFSized p) (ap1 triFSized (pArg p))))
triFSized_op_RO_imp p ne =
  let H : Formula
      H = eqF (dtag p) dgRO
      opk : Term
      opk = opkg p
      nieq : Deriv (imp H (eqF (ap1 nIdx opk) dgRO))
      nieq = nieqImp p ne dgRO
      cell_fires : Deriv (imp H (eqF (ap1 triStep opk) (ap1 cellTriRO opk)))
      cell_fires =
        impEqTrans (ap1 triStep opk) (ap1 triRestSu opk) (ap1 cellTriRO opk)
          (fork_false_to_snd_imp H cellTriZe triRestSu (testEq 0) opk
             (testEq_skip_imp H 3 0 opk w30 nieq))
          (impEqTrans (ap1 triRestSu opk) (ap1 triRestAd opk) (ap1 cellTriRO opk)
            (fork_false_to_snd_imp H cellTriSu triRestAd (testEq 1) opk
               (testEq_skip_imp H 3 1 opk w31 nieq))
            (impEqTrans (ap1 triRestAd opk) (ap1 triRestRO opk) (ap1 cellTriRO opk)
              (fork_false_to_snd_imp H adCellTriS triRestRO (testEq 2) opk
                 (testEq_skip_imp H 3 2 opk w32 nieq))
              (fork_true_to_fst_imp H cellTriRO triRestRS (testEq 3) opk
                 (testEq_fire_imp H 3 opk nieq))))
      recArg : Deriv (eqF (ap1 (lookupAt argIdx) opk) (ap1 triFSized (pArg p)))
      recArg = lookup_op Z triStep argIdx (ap1 predecessor p) (pArg p)
                 (op_argIdx p ne) (argValueBound p ne)
  in impEqTrans (ap1 triFSized p) (ap1 triStep opk) (ap1 triFSized (pArg p))
       (impLift {H} (opUnfold p ne))
       (impEqTrans (ap1 triStep opk) (ap1 cellTriRO opk) (ap1 triFSized (pArg p))
         cell_fires (impLift {H} recArg))

triFSized_op_RS_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (eqF (dtag p) dgRS)
             (eqF (ap1 triFSized p)
                  (szDerSu (szDerAd (ap1 triFSized (pL p)) (ap1 triFSized (pR p))))))
triFSized_op_RS_imp p ne =
  let H : Formula
      H = eqF (dtag p) dgRS
      opk : Term
      opk = opkg p
      nieq : Deriv (imp H (eqF (ap1 nIdx opk) dgRS))
      nieq = nieqImp p ne dgRS
      cell_fires : Deriv (imp H (eqF (ap1 triStep opk) (ap1 cellTriRS opk)))
      cell_fires =
        impEqTrans (ap1 triStep opk) (ap1 triRestSu opk) (ap1 cellTriRS opk)
          (fork_false_to_snd_imp H cellTriZe triRestSu (testEq 0) opk
             (testEq_skip_imp H 4 0 opk w40 nieq))
          (impEqTrans (ap1 triRestSu opk) (ap1 triRestAd opk) (ap1 cellTriRS opk)
            (fork_false_to_snd_imp H cellTriSu triRestAd (testEq 1) opk
               (testEq_skip_imp H 4 1 opk w41 nieq))
            (impEqTrans (ap1 triRestAd opk) (ap1 triRestRO opk) (ap1 cellTriRS opk)
              (fork_false_to_snd_imp H adCellTriS triRestRO (testEq 2) opk
                 (testEq_skip_imp H 4 2 opk w42 nieq))
              (impEqTrans (ap1 triRestRO opk) (ap1 triRestRS opk) (ap1 cellTriRS opk)
                (fork_false_to_snd_imp H cellTriRO triRestRS (testEq 3) opk
                   (testEq_skip_imp H 4 3 opk w43 nieq))
                (fork_true_to_fst_imp H cellTriRS cellTriZe (testEq 4) opk
                   (testEq_fire_imp H 4 opk nieq)))))
      recL : Deriv (eqF (ap1 (lookupAt lIdx) opk) (ap1 triFSized (pL p)))
      recL = lookup_op Z triStep lIdx (ap1 predecessor p) (pL p)
               (op_pL p ne) (pLValueBound p ne)
      recR : Deriv (eqF (ap1 (lookupAt rIdx) opk) (ap1 triFSized (pR p)))
      recR = lookup_op Z triStep rIdx (ap1 predecessor p) (pR p)
               (op_pR p ne) (pRValueBound p ne)
      innerAd : Deriv (eqF (ap1 (C szDerAdF (lookupAt lIdx) (lookupAt rIdx)) opk)
                           (szDerAd (ap1 triFSized (pL p)) (ap1 triFSized (pR p))))
      innerAd =
        ruleTrans (ax_C szDerAdF (lookupAt lIdx) (lookupAt rIdx) opk)
          (ruleTrans (congL szDerAdF (ap1 (lookupAt rIdx) opk) recL)
            (ruleTrans (congR szDerAdF (ap1 triFSized (pL p)) recR)
                       (szDerAdF_eq (ap1 triFSized (pL p)) (ap1 triFSized (pR p)))))
      cell_val : Deriv (eqF (ap1 cellTriRS opk)
                            (szDerSu (szDerAd (ap1 triFSized (pL p)) (ap1 triFSized (pR p)))))
      cell_val =
        ruleTrans (compose1U_eq szDerSuF (C szDerAdF (lookupAt lIdx) (lookupAt rIdx)) opk)
          (ruleTrans (cong1 szDerSuF innerAd)
                     (szDerSuF_eq (szDerAd (ap1 triFSized (pL p)) (ap1 triFSized (pR p)))))
  in impEqTrans (ap1 triFSized p) (ap1 triStep opk)
       (szDerSu (szDerAd (ap1 triFSized (pL p)) (ap1 triFSized (pR p))))
       (impLift {H} (opUnfold p ne))
       (impEqTrans (ap1 triStep opk) (ap1 cellTriRS opk)
         (szDerSu (szDerAd (ap1 triFSized (pL p)) (ap1 triFSized (pR p))))
         cell_fires (impLift {H} cell_val))
