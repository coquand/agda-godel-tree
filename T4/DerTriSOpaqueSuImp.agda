{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.DerTriSOpaqueSuImp -- the IMP-FORM opaque Su triFSized equation carrying
-- BOTH ne and htag in a SINGLE antecedent  H = (dtag q = dgSu) , with  q != O
-- derived internally from H (T4.NeSuImp).  This is the one Su unfold applied to
-- an OPAQUE child (the left child  pL  of an Ad node in the Ad_Su critical pair),
-- where ne is NOT available bare.  Composes the ne-form harness
-- (T4.OpaqueHarnessImp.Himp triStep) + lookup_op_imp + argValueBound_imp + ForkImp.
--
--   triFSized_op_Su_himp q :
--     imp (dtag q = dgSu) (triFSized q = szDerSu (triFSized (pArg q)))
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.DerTriSOpaqueSuImp where

open import T4.Base

open import T4.DerCodeS using ( szDerSu ; dtag ; pArg )
open import T4.DerCodeSFun using ( szDerSuF ; szDerSuF_eq )
open import T4.DerCode using ( dgSu )
open import T4.DerTriS
  using ( triStep ; triFSized
        ; cellTriZe ; cellTriSu ; triRestSu ; triRestAd )
open import T4.WfRedSized using ( w10 )
open import T4.DerSrc using ( testEq )
open import T4.FoldRec using ( lookupAt )
open import T4.BinTree using ( nIdx )

open import T4.OpaqueLookupImp using ( lookup_op_imp )
open import T4.DescSndImp using ( argValueBound_imp )
open import T4.NeSuImp using ( neSu_imp )
open import T4.ForkImp
  using ( testEq_fire_imp ; testEq_skip_imp
        ; fork_true_to_fst_imp ; fork_false_to_snd_imp )

open import BRA3.Church      using ( predecessor )
open import BRA3.PairAlgebra using ( compose1U_eq )
open import BRA3.Contrapositive using ( compI ; identP )
open import T4.Thm12.ImpHelpers using ( impLift ; impCong1 ; impEqTrans )

import T4.OpaqueHarnessImp
open T4.OpaqueHarnessImp.Himp triStep

------------------------------------------------------------------------

triFSized_op_Su_himp : (q : Term) ->
  Deriv (imp (eqF (dtag q) dgSu)
             (eqF (ap1 triFSized q) (szDerSu (ap1 triFSized (pArg q)))))
triFSized_op_Su_himp q =
  let H : Formula
      H = eqF (dtag q) dgSu
      opk : Term
      opk = opkg q
      neH : Deriv (imp H (neg (eqF q O)))
      neH = neSu_imp q
      nieqH : Deriv (imp H (eqF (ap1 nIdx opk) dgSu))
      nieqH = impEqTrans (ap1 nIdx opk) (dtag q) dgSu
                (compI neH (op_nIdx_imp q)) (identP H)
      cell_fires : Deriv (imp H (eqF (ap1 triStep opk) (ap1 cellTriSu opk)))
      cell_fires =
        impEqTrans (ap1 triStep opk) (ap1 triRestSu opk) (ap1 cellTriSu opk)
          (fork_false_to_snd_imp H cellTriZe triRestSu (testEq 0) opk
             (testEq_skip_imp H 1 0 opk w10 nieqH))
          (fork_true_to_fst_imp H cellTriSu triRestAd (testEq 1) opk
             (testEq_fire_imp H 1 opk nieqH))
      recArg : Deriv (imp H (eqF (ap1 (lookupAt argIdx) opk) (ap1 triFSized (pArg q))))
      recArg = lookup_op_imp H Z triStep argIdx (ap1 predecessor q) (pArg q)
                 (compI neH (op_argIdx_imp q))
                 (compI neH (argValueBound_imp q))
      cell_val : Deriv (imp H (eqF (ap1 cellTriSu opk) (szDerSu (ap1 triFSized (pArg q)))))
      cell_val =
        impEqTrans (ap1 cellTriSu opk)
                   (ap1 szDerSuF (ap1 (lookupAt argIdx) opk))
                   (szDerSu (ap1 triFSized (pArg q)))
          (impLift {H} (compose1U_eq szDerSuF (lookupAt argIdx) opk))
          (impEqTrans (ap1 szDerSuF (ap1 (lookupAt argIdx) opk))
                      (ap1 szDerSuF (ap1 triFSized (pArg q)))
                      (szDerSu (ap1 triFSized (pArg q)))
             (impCong1 szDerSuF (ap1 (lookupAt argIdx) opk) (ap1 triFSized (pArg q)) recArg)
             (impLift {H} (szDerSuF_eq (ap1 triFSized (pArg q)))))
  in impEqTrans (ap1 triFSized q) (ap1 triStep opk) (szDerSu (ap1 triFSized (pArg q)))
       (compI neH (opUnfold_imp q))
       (impEqTrans (ap1 triStep opk) (ap1 cellTriSu opk) (szDerSu (ap1 triFSized (pArg q)))
          cell_fires cell_val)
