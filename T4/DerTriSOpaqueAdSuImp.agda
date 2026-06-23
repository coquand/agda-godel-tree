{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.DerTriSOpaqueAdSuImp -- the LAST opaque triFSized equation: the Ad_Su
-- critical pair, IMP-FORM, ctx [htag = (dtag p = dgAd), htagL = (dtag pL = dgSu)],
-- ne(p) bare.  This is the only case that unfolds the OPAQUE left child  pL  (cell
-- = szDerRS (triFSized (pArg pL)) (triFSized pR)), so it consumes the ne-form Su
-- unfold  triFSized_op_Su_himp (pL p)  under htagL (ne(pL) derived internally).
--
--   triFSized_op_Ad_Su_imp p ne :
--     imp (dtag p = dgAd)
--         (imp (dtag (pL p) = dgSu)
--              (triFSized p = szDerRS (triFSized (pArg (pL p))) (triFSized (pR p))))
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.DerTriSOpaqueAdSuImp where

open import T4.Base

open import T4.DerCodeS using ( szDerSu ; szDerRS ; dtag ; pArg ; pL ; pR ; pArg_Su )
open import T4.DerCodeSFun using ( szDerRSF ; szDerRSF_eq )
open import T4.DerCode using ( dgAd ; dgSu )
open import T4.DerTriS
  using ( triStep ; triFSized
        ; cellTriZe ; cellTriSu ; cellTriAdZe ; cellTriAdSu ; cellTriAdElse
        ; triRestSu ; triRestAd ; triRestRO ; adCellTriS ; restAdNodeS
        ; testAdZeS ; testAdSuS ; adLeftTag ; adLeftTagFrom ; pArgFn )
open import T4.WfRedSized using ( w10 ; w20 )
open import T4.DerSrc using ( testEq ; w21 )
open import T4.WfRedExtract using ( pLValueBound ; pRValueBound )
open import T4.OpaqueLookup using ( lookup_op )
open import T4.FoldRec using ( lookupAt )
open import T4.BinTree using ( nIdx ; lIdx ; rIdx )

open import T4.DerTriSOpaqueSuImp using ( triFSized_op_Su_himp )

open import T4.ForkImp
  using ( testEq_fire_imp ; testEq_skip_imp ; natEqFire_imp ; natEqSkip_imp
        ; fork_true_to_fst_imp ; fork_false_to_snd_imp )
open import T4.CtxKit using ( lift2 ; trans2c )

open import BRA3.Church      using ( predecessor )
open import BRA3.PairAlgebra using ( compose1U_eq )
open import BRA3.Logic       using ( prependEqLeft )
open import BRA3.Contrapositive using ( compI ; liftP )
open import T4.Thm12.ImpHelpers
  using ( impLift ; impCong1 ; impCongL ; impCongR ; impEqTrans )

import T4.OpaqueHarness
open T4.OpaqueHarness.H triStep

------------------------------------------------------------------------

triFSized_op_Ad_Su_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (eqF (dtag p) dgAd)
             (imp (eqF (dtag (pL p)) dgSu)
                  (eqF (ap1 triFSized p)
                       (szDerRS (ap1 triFSized (pArg (pL p))) (ap1 triFSized (pR p))))))
triFSized_op_Ad_Su_imp p ne =
  let H1 : Formula
      H1 = eqF (dtag p) dgAd
      H2 : Formula
      H2 = eqF (dtag (pL p)) dgSu
      opk : Term
      opk = opkg p
      RS : Term
      RS = szDerRS (ap1 triFSized (pArg (pL p))) (ap1 triFSized (pR p))
      -- cell_to_ad under H1 (reaches adCellTriS).
      nieqAd : Deriv (imp H1 (eqF (ap1 nIdx opk) dgAd))
      nieqAd = prependEqLeft (ap1 nIdx opk) (dtag p) dgAd (op_nIdx p ne)
      cell_to_ad : Deriv (imp H1 (eqF (ap1 triStep opk) (ap1 adCellTriS opk)))
      cell_to_ad =
        impEqTrans (ap1 triStep opk) (ap1 triRestSu opk) (ap1 adCellTriS opk)
          (fork_false_to_snd_imp H1 cellTriZe triRestSu (testEq 0) opk
             (testEq_skip_imp H1 2 0 opk w20 nieqAd))
          (impEqTrans (ap1 triRestSu opk) (ap1 triRestAd opk) (ap1 adCellTriS opk)
            (fork_false_to_snd_imp H1 cellTriSu triRestAd (testEq 1) opk
               (testEq_skip_imp H1 2 1 opk w21 nieqAd))
            (fork_true_to_fst_imp H1 adCellTriS triRestRO (testEq 2) opk
               (testEq_fire_imp H1 2 opk nieqAd)))
      cta : Deriv (imp H1 (imp H2 (eqF (ap1 triStep opk) (ap1 adCellTriS opk))))
      cta = compI cell_to_ad
              (axK (eqF (ap1 triStep opk) (ap1 adCellTriS opk)) H2)
      -- ad_fires under H2 (left tag = 1 : skip Ze, fire Su) -> cellTriAdSu.
      adLeftEq : Deriv (eqF (ap1 adLeftTag opk) (dtag (pL p)))
      adLeftEq = adLeftTagFrom opk (pL p) (op_pL p ne)
      adLeftH2 : Deriv (imp H2 (eqF (ap1 adLeftTag opk) (natCode 1)))
      adLeftH2 = prependEqLeft (ap1 adLeftTag opk) (dtag (pL p)) (natCode 1) adLeftEq
      ad_fires_H2 : Deriv (imp H2 (eqF (ap1 adCellTriS opk) (ap1 cellTriAdSu opk)))
      ad_fires_H2 =
        impEqTrans (ap1 adCellTriS opk) (ap1 restAdNodeS opk) (ap1 cellTriAdSu opk)
          (fork_false_to_snd_imp H2 cellTriAdZe restAdNodeS testAdZeS opk
             (natEqSkip_imp H2 adLeftTag 1 0 opk w10 adLeftH2))
          (fork_true_to_fst_imp H2 cellTriAdSu cellTriAdElse testAdSuS opk
             (natEqFire_imp H2 adLeftTag 1 opk adLeftH2))
      adf : Deriv (imp H1 (imp H2 (eqF (ap1 adCellTriS opk) (ap1 cellTriAdSu opk))))
      adf = liftP H1 ad_fires_H2
      -- right child recovery (bare), left child recovery + opaque Su unfold (H2).
      recR : Deriv (eqF (ap1 (lookupAt rIdx) opk) (ap1 triFSized (pR p)))
      recR = lookup_op Z triStep rIdx (ap1 predecessor p) (pR p)
               (op_pR p ne) (pRValueBound p ne)
      recL : Deriv (eqF (ap1 (lookupAt lIdx) opk) (ap1 triFSized (pL p)))
      recL = lookup_op Z triStep lIdx (ap1 predecessor p) (pL p)
               (op_pL p ne) (pLValueBound p ne)
      recL_su_H2 : Deriv (imp H2 (eqF (ap1 (lookupAt lIdx) opk)
                                      (szDerSu (ap1 triFSized (pArg (pL p))))))
      recL_su_H2 =
        impEqTrans (ap1 (lookupAt lIdx) opk) (ap1 triFSized (pL p))
                   (szDerSu (ap1 triFSized (pArg (pL p))))
          (impLift {H2} recL) (triFSized_op_Su_himp (pL p))
      leftRec_H2 : Deriv (imp H2
                     (eqF (ap1 (compose1U pArgFn (lookupAt lIdx)) opk)
                          (ap1 triFSized (pArg (pL p)))))
      leftRec_H2 =
        impEqTrans (ap1 (compose1U pArgFn (lookupAt lIdx)) opk)
                   (ap1 pArgFn (ap1 (lookupAt lIdx) opk))
                   (ap1 triFSized (pArg (pL p)))
          (impLift {H2} (compose1U_eq pArgFn (lookupAt lIdx) opk))
          (impEqTrans (ap1 pArgFn (ap1 (lookupAt lIdx) opk))
                      (ap1 pArgFn (szDerSu (ap1 triFSized (pArg (pL p)))))
                      (ap1 triFSized (pArg (pL p)))
            (impCong1 pArgFn (ap1 (lookupAt lIdx) opk)
                      (szDerSu (ap1 triFSized (pArg (pL p)))) recL_su_H2)
            (impLift {H2}
              (ruleTrans (compose1U_eq Snd Snd (szDerSu (ap1 triFSized (pArg (pL p)))))
                         (pArg_Su (ap1 triFSized (pArg (pL p)))))))
      cell_val_H2 : Deriv (imp H2 (eqF (ap1 cellTriAdSu opk) RS))
      cell_val_H2 =
        impEqTrans (ap1 cellTriAdSu opk)
                   (ap2 szDerRSF (ap1 (compose1U pArgFn (lookupAt lIdx)) opk)
                                 (ap1 (lookupAt rIdx) opk))
                   RS
          (impLift {H2} (ax_C szDerRSF (compose1U pArgFn (lookupAt lIdx)) (lookupAt rIdx) opk))
          (impEqTrans (ap2 szDerRSF (ap1 (compose1U pArgFn (lookupAt lIdx)) opk)
                                    (ap1 (lookupAt rIdx) opk))
                      (ap2 szDerRSF (ap1 triFSized (pArg (pL p)))
                                    (ap1 (lookupAt rIdx) opk))
                      RS
            (impCongL szDerRSF (ap1 (compose1U pArgFn (lookupAt lIdx)) opk)
                      (ap1 triFSized (pArg (pL p))) (ap1 (lookupAt rIdx) opk) leftRec_H2)
            (impEqTrans (ap2 szDerRSF (ap1 triFSized (pArg (pL p)))
                                      (ap1 (lookupAt rIdx) opk))
                        (ap2 szDerRSF (ap1 triFSized (pArg (pL p)))
                                      (ap1 triFSized (pR p)))
                        RS
              (impCongR szDerRSF (ap1 (lookupAt rIdx) opk) (ap1 triFSized (pR p))
                        (ap1 triFSized (pArg (pL p))) (impLift {H2} recR))
              (impLift {H2} (szDerRSF_eq (ap1 triFSized (pArg (pL p))) (ap1 triFSized (pR p))))))
      cvf : Deriv (imp H1 (imp H2 (eqF (ap1 cellTriAdSu opk) RS)))
      cvf = liftP H1 cell_val_H2
  in trans2c (ap1 triFSized p) (ap1 triStep opk) RS
       (lift2 H1 H2 (opUnfold p ne))
       (trans2c (ap1 triStep opk) (ap1 adCellTriS opk) RS cta
         (trans2c (ap1 adCellTriS opk) (ap1 cellTriAdSu opk) RS adf cvf))
