{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.WfRedExtractSuHtag -- the IMP-FORM Su child VALIDITY extraction carrying
-- BOTH ne and htag in a SINGLE antecedent  H = (dtag q = dgSu) , with  q != O
-- derived internally (T4.NeSuImp).  This is the grandchild-validity case of the
-- Ad_Su critical pair: the left child  pL  is OPAQUE, so its Su unary child's
-- validity must be extracted with ne under htag rather than bare.
--
--   extractChild_Su_himp q :
--     imp (dtag q = dgSu) (imp (wfRedSized q = O) (wfRedSized (pArg q) = O))
--
-- Mirrors T4.WfRedExtractHtag.childU_H + cascadeSu_H but with the wfStep harness
-- in ne-form (T4.OpaqueHarnessImp.Himp wfStep) + lookup_op_imp + argValueBound_imp.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.WfRedExtractSuHtag where

open import T4.Base

open import T4.DerCodeS using ( dtag ; pArg )
open import T4.DerCode  using ( dgSu )
open import T4.WfRedSized
  using ( wfRedSized ; wfStep ; unaryCell ; chkU
        ; wfRestSu ; wfRestAd ; w10 )
open import T4.FoldRec using ( lookupAt )
open import T4.BinTree using ( nIdx )
open import T4.DerSrc using ( testEq )

open import T4.OpaqueLookupImp using ( lookup_op_imp )
open import T4.DescSndImp using ( argValueBound_imp )
open import T4.NeSuImp using ( neSu_imp )
open import T4.ForkImp
  using ( testEq_fire_imp ; testEq_skip_imp
        ; fork_true_to_fst_imp ; fork_false_to_snd_imp )
open import T4.CtxKit using ( lift2 ; get2b ; ap2c ; trans2c )

open import BRA3.Church      using ( sigma ; predecessor )
open import T4.SigmaZeroN    using ( sigmaZeroR )
open import BRA3.Logic       using ( eqSymImp )
open import BRA3.Contrapositive using ( compI ; identP )
open import T4.Thm12.ImpHelpers using ( impLift ; impEqTrans ; impRuleSym )

import T4.OpaqueHarnessImp
open T4.OpaqueHarnessImp.Himp wfStep

------------------------------------------------------------------------

extractChild_Su_himp : (q : Term) ->
  Deriv (imp (eqF (dtag q) dgSu)
             (imp (eqF (ap1 wfRedSized q) O) (eqF (ap1 wfRedSized (pArg q)) O)))
extractChild_Su_himp q =
  let H : Formula
      H = eqF (dtag q) dgSu
      A : Formula
      A = eqF (ap1 wfRedSized q) O
      opk : Term
      opk = opkg q
      neH : Deriv (imp H (neg (eqF q O)))
      neH = neSu_imp q
      -- nieq under H ; cascade to unaryCell.
      nieq : Deriv (imp H (eqF (ap1 nIdx opk) dgSu))
      nieq = impEqTrans (ap1 nIdx opk) (dtag q) dgSu
               (compI neH (op_nIdx_imp q)) (identP H)
      cfH : Deriv (imp H (eqF (ap1 wfStep opk) (ap1 unaryCell opk)))
      cfH =
        impEqTrans (ap1 wfStep opk) (ap1 wfRestSu opk) (ap1 unaryCell opk)
          (fork_false_to_snd_imp H Z wfRestSu (testEq 0) opk
             (testEq_skip_imp H 1 0 opk w10 nieq))
          (fork_true_to_fst_imp H unaryCell wfRestAd (testEq 1) opk
             (testEq_fire_imp H 1 opk nieq))
      -- the unary-cell child recovery, all in [H, A].
      lookupT : Term
      lookupT = ap1 (lookupAt argIdx) opk
      sigT : Term
      sigT = ap2 sigma (ap1 chkU opk) lookupT
      opUnfoldH : Deriv (imp H (eqF (ap1 wfRedSized q) (ap1 wfStep opk)))
      opUnfoldH = compI neH (opUnfold_imp q)
      UE : Deriv (imp H (eqF (ap1 wfRedSized q) sigT))
      UE = impEqTrans (ap1 wfRedSized q) (ap1 wfStep opk) sigT
             opUnfoldH
             (impEqTrans (ap1 wfStep opk) (ap1 unaryCell opk) sigT
               cfH (impLift {H} (ax_C sigma chkU (lookupAt argIdx) opk)))
      UE2 : Deriv (imp H (imp A (eqF (ap1 wfRedSized q) sigT)))
      UE2 = compI UE (axK (eqF (ap1 wfRedSized q) sigT) A)
      UE2flip : Deriv (imp H (imp A (eqF sigT (ap1 wfRedSized q))))
      UE2flip = ap2c (lift2 H A (eqSymImp (ap1 wfRedSized q) sigT)) UE2
      sig0 : Deriv (imp H (imp A (eqF sigT O)))
      sig0 = trans2c sigT (ap1 wfRedSized q) O UE2flip (get2b H A)
      lookupO : Deriv (imp H (imp A (eqF lookupT O)))
      lookupO = ap2c (lift2 H A (sigmaZeroR (ap1 chkU opk) lookupT)) sig0
      recArg_imp : Deriv (imp H (eqF lookupT (ap1 wfRedSized (pArg q))))
      recArg_imp = lookup_op_imp H Z wfStep argIdx (ap1 predecessor q) (pArg q)
                     (compI neH (op_argIdx_imp q))
                     (compI neH (argValueBound_imp q))
      recArg_flip : Deriv (imp H (imp A (eqF (ap1 wfRedSized (pArg q)) lookupT)))
      recArg_flip = compI (impRuleSym recArg_imp)
                      (axK (eqF (ap1 wfRedSized (pArg q)) lookupT) A)
  in trans2c (ap1 wfRedSized (pArg q)) lookupT O recArg_flip lookupO
