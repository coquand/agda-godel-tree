{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.DerTriSOpaqueAdImp -- IMP-FORM (htag-carrying) opaque triFSized equations
-- for the Ad critical pairs Ad_Ze and Ad_else (the two that do NOT unfold the
-- left child, so ne(p) stays bare).  htag and the left-tag fact(s) are carried as
-- antecedents (the object sub-dispatch supplies them).  Ze: ctx [htag, htagL=dgZe];
-- else: ctx [htag, neg(dtag pL=dgZe), neg(dtag pL=dgSu)].
--
-- (Ad_Su -- which unfolds the opaque left child and so needs ne(pL) under htagL --
-- is the remaining piece; see memory.)
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.DerTriSOpaqueAdImp where

open import T4.Base

open import T4.DerCodeS using ( szDerAd ; szDerRO ; dtag ; pL ; pR )
open import T4.DerCodeSFun using ( szDerROF ; szDerROF_eq ; szDerAdF ; szDerAdF_eq )
open import T4.DerCode using ( dgZe ; dgSu ; dgAd )
open import T4.DerTriS
  using ( triStep ; triFSized
        ; cellTriZe ; cellTriSu ; cellTriAdZe ; cellTriAdSu ; cellTriAdElse
        ; triRestSu ; triRestAd ; triRestRO ; adCellTriS ; restAdNodeS
        ; testAdZeS ; testAdSuS ; adLeftTag ; adLeftTagFrom )
open import T4.WfRedSized using ( w20 )
open import T4.WfRedExtract using ( pLValueBound ; pRValueBound )
open import T4.OpaqueLookup using ( lookup_op )
open import T4.FoldRec using ( lookupAt )
open import T4.BinTree using ( nIdx ; lIdx ; rIdx )

open import T4.DerSrc using ( testEq ; w21 )
open import T4.ForkImp
  using ( testEq_fire_imp ; testEq_skip_imp ; natEqFire_imp ; natEqSkipNeg_imp
        ; fork_true_to_fst_imp ; fork_false_to_snd_imp )
open import T4.CtxKit
  using ( lift2 ; lift3 ; trans2c ; trans3c )

open import BRA3.Church      using ( predecessor )
open import BRA3.PairAlgebra using ( compose1U_eq )
open import BRA3.Logic       using ( prependEqLeft )
open import BRA3.Classical   using ( axContrapos )
open import BRA3.Contrapositive using ( compI ; liftP ; bComb )
open import T4.Thm12.ImpHelpers using ( impEqTrans )

import T4.OpaqueHarness
open T4.OpaqueHarness.H triStep

------------------------------------------------------------------------
-- Shared: cell_to_ad over htag (single antecedent), reaching adCellTriS.

private
  cell_to_ad_H1 : (p : Term) -> Deriv (neg (eqF p O)) ->
    Deriv (imp (eqF (dtag p) dgAd) (eqF (ap1 triStep (opkg p)) (ap1 adCellTriS (opkg p))))
  cell_to_ad_H1 p ne =
    let H1 : Formula
        H1 = eqF (dtag p) dgAd
        opk : Term
        opk = opkg p
        nieq : Deriv (imp H1 (eqF (ap1 nIdx opk) dgAd))
        nieq = prependEqLeft (ap1 nIdx opk) (dtag p) dgAd (op_nIdx p ne)
    in impEqTrans (ap1 triStep opk) (ap1 triRestSu opk) (ap1 adCellTriS opk)
         (fork_false_to_snd_imp H1 cellTriZe triRestSu (testEq 0) opk
            (testEq_skip_imp H1 2 0 opk w20 nieq))
         (impEqTrans (ap1 triRestSu opk) (ap1 triRestAd opk) (ap1 adCellTriS opk)
           (fork_false_to_snd_imp H1 cellTriSu triRestAd (testEq 1) opk
              (testEq_skip_imp H1 2 1 opk w21 nieq))
           (fork_true_to_fst_imp H1 adCellTriS triRestRO (testEq 2) opk
              (testEq_fire_imp H1 2 opk nieq)))

  -- neg(dtag pL = natCode k) =>  neg(adLeftTag opk = natCode k) , given adLeftTag opk = dtag pL.
  negAdFromNeg : (opk a : Term) (k : Nat) -> Deriv (eqF (ap1 adLeftTag opk) a) ->
    Deriv (imp (neg (eqF a (natCode k))) (neg (eqF (ap1 adLeftTag opk) (natCode k))))
  negAdFromNeg opk a k adLeftEq =
    mp (axContrapos (eqF (ap1 adLeftTag opk) (natCode k)) (eqF a (natCode k)))
       (prependEqLeft a (ap1 adLeftTag opk) (natCode k) (ruleSym adLeftEq))

------------------------------------------------------------------------
-- Ad_Ze :  ctx [htag, htagL = (dtag pL = dgZe)] .

triFSized_op_Ad_Ze_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (eqF (dtag p) dgAd)
             (imp (eqF (dtag (pL p)) dgZe)
                  (eqF (ap1 triFSized p) (szDerRO (ap1 triFSized (pR p))))))
triFSized_op_Ad_Ze_imp p ne =
  let H1 : Formula
      H1 = eqF (dtag p) dgAd
      H2 : Formula
      H2 = eqF (dtag (pL p)) dgZe
      opk : Term
      opk = opkg p
      cta : Deriv (imp H1 (imp H2 (eqF (ap1 triStep opk) (ap1 adCellTriS opk))))
      cta = compI (cell_to_ad_H1 p ne)
              (axK (eqF (ap1 triStep opk) (ap1 adCellTriS opk)) H2)
      adLeftEq : Deriv (eqF (ap1 adLeftTag opk) (dtag (pL p)))
      adLeftEq = adLeftTagFrom opk (pL p) (op_pL p ne)
      adLeftH2 : Deriv (imp H2 (eqF (ap1 adLeftTag opk) (natCode 0)))
      adLeftH2 = prependEqLeft (ap1 adLeftTag opk) (dtag (pL p)) (natCode 0) adLeftEq
      adf1 : Deriv (imp H2 (eqF (ap1 adCellTriS opk) (ap1 cellTriAdZe opk)))
      adf1 = fork_true_to_fst_imp H2 cellTriAdZe restAdNodeS testAdZeS opk
               (natEqFire_imp H2 adLeftTag 0 opk adLeftH2)
      adf : Deriv (imp H1 (imp H2 (eqF (ap1 adCellTriS opk) (ap1 cellTriAdZe opk))))
      adf = liftP H1 adf1
      recR : Deriv (eqF (ap1 (lookupAt rIdx) opk) (ap1 triFSized (pR p)))
      recR = lookup_op Z triStep rIdx (ap1 predecessor p) (pR p)
               (op_pR p ne) (pRValueBound p ne)
      cell_val : Deriv (eqF (ap1 cellTriAdZe opk) (szDerRO (ap1 triFSized (pR p))))
      cell_val =
        ruleTrans (compose1U_eq szDerROF (lookupAt rIdx) opk)
          (ruleTrans (cong1 szDerROF recR) (szDerROF_eq (ap1 triFSized (pR p))))
  in trans2c (ap1 triFSized p) (ap1 triStep opk) (szDerRO (ap1 triFSized (pR p)))
       (lift2 H1 H2 (opUnfold p ne))
       (trans2c (ap1 triStep opk) (ap1 adCellTriS opk) (szDerRO (ap1 triFSized (pR p)))
         cta
         (trans2c (ap1 adCellTriS opk) (ap1 cellTriAdZe opk) (szDerRO (ap1 triFSized (pR p)))
           adf (lift2 H1 H2 cell_val)))

------------------------------------------------------------------------
-- Ad_else :  ctx [htag, neg(dtag pL=dgZe), neg(dtag pL=dgSu)] .

triFSized_op_Ad_else_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (eqF (dtag p) dgAd)
             (imp (neg (eqF (dtag (pL p)) dgZe))
                  (imp (neg (eqF (dtag (pL p)) dgSu))
                       (eqF (ap1 triFSized p)
                            (szDerAd (ap1 triFSized (pL p)) (ap1 triFSized (pR p)))))))
triFSized_op_Ad_else_imp p ne =
  let H1 : Formula
      H1 = eqF (dtag p) dgAd
      H2 : Formula
      H2 = neg (eqF (dtag (pL p)) dgZe)
      H3 : Formula
      H3 = neg (eqF (dtag (pL p)) dgSu)
      opk : Term
      opk = opkg p
      X : Formula
      X = eqF (ap1 triStep opk) (ap1 adCellTriS opk)
      constK2 : Deriv (imp X (imp H2 (imp H3 X)))
      constK2 = bComb (liftP X (axK (imp H3 X) H2)) (axK X H3)
      cta : Deriv (imp H1 (imp H2 (imp H3 X)))
      cta = compI (cell_to_ad_H1 p ne) constK2
      adLeftEq : Deriv (eqF (ap1 adLeftTag opk) (dtag (pL p)))
      adLeftEq = adLeftTagFrom opk (pL p) (op_pL p ne)
      skip_ze_H2 : Deriv (imp H2 (eqF (ap1 testAdZeS opk) O))
      skip_ze_H2 = natEqSkipNeg_imp H2 adLeftTag 0 opk
                     (negAdFromNeg opk (dtag (pL p)) 0 adLeftEq)
      skip_su_H3 : Deriv (imp H3 (eqF (ap1 testAdSuS opk) O))
      skip_su_H3 = natEqSkipNeg_imp H3 adLeftTag 1 opk
                     (negAdFromNeg opk (dtag (pL p)) 1 adLeftEq)
      adf_ze1 : Deriv (imp H2 (eqF (ap1 adCellTriS opk) (ap1 restAdNodeS opk)))
      adf_ze1 = fork_false_to_snd_imp H2 cellTriAdZe restAdNodeS testAdZeS opk skip_ze_H2
      adf_su1 : Deriv (imp H3 (eqF (ap1 restAdNodeS opk) (ap1 cellTriAdElse opk)))
      adf_su1 = fork_false_to_snd_imp H3 cellTriAdSu cellTriAdElse testAdSuS opk skip_su_H3
      adf_ze : Deriv (imp H1 (imp H2 (imp H3 (eqF (ap1 adCellTriS opk) (ap1 restAdNodeS opk)))))
      adf_ze = liftP H1 (compI adf_ze1
                 (axK (eqF (ap1 adCellTriS opk) (ap1 restAdNodeS opk)) H3))
      adf_su : Deriv (imp H1 (imp H2 (imp H3 (eqF (ap1 restAdNodeS opk) (ap1 cellTriAdElse opk)))))
      adf_su = lift2 H1 H2 adf_su1
      ad_chain : Deriv (imp H1 (imp H2 (imp H3 (eqF (ap1 adCellTriS opk) (ap1 cellTriAdElse opk)))))
      ad_chain = trans3c (ap1 adCellTriS opk) (ap1 restAdNodeS opk) (ap1 cellTriAdElse opk)
                   adf_ze adf_su
      recL : Deriv (eqF (ap1 (lookupAt lIdx) opk) (ap1 triFSized (pL p)))
      recL = lookup_op Z triStep lIdx (ap1 predecessor p) (pL p)
               (op_pL p ne) (pLValueBound p ne)
      recR : Deriv (eqF (ap1 (lookupAt rIdx) opk) (ap1 triFSized (pR p)))
      recR = lookup_op Z triStep rIdx (ap1 predecessor p) (pR p)
               (op_pR p ne) (pRValueBound p ne)
      cell_val : Deriv (eqF (ap1 cellTriAdElse opk)
                            (szDerAd (ap1 triFSized (pL p)) (ap1 triFSized (pR p))))
      cell_val =
        ruleTrans (ax_C szDerAdF (lookupAt lIdx) (lookupAt rIdx) opk)
          (ruleTrans (congL szDerAdF (ap1 (lookupAt rIdx) opk) recL)
            (ruleTrans (congR szDerAdF (ap1 triFSized (pL p)) recR)
                       (szDerAdF_eq (ap1 triFSized (pL p)) (ap1 triFSized (pR p)))))
  in trans3c (ap1 triFSized p) (ap1 triStep opk)
       (szDerAd (ap1 triFSized (pL p)) (ap1 triFSized (pR p)))
       (lift3 H1 H2 H3 (opUnfold p ne))
       (trans3c (ap1 triStep opk) (ap1 adCellTriS opk)
         (szDerAd (ap1 triFSized (pL p)) (ap1 triFSized (pR p)))
         cta
         (trans3c (ap1 adCellTriS opk) (ap1 cellTriAdElse opk)
           (szDerAd (ap1 triFSized (pL p)) (ap1 triFSized (pR p)))
           ad_chain (lift3 H1 H2 H3 cell_val)))
