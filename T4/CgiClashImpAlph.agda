{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.CgiClashImpAlph -- Carneiro-lifted (imp Rf) variant of T4.CgiClashAlph,
-- the  checkAlphN -guard analog of  T4.CgiClashImp .   The guard-independent
-- helpers ( imp_dPos / imp_chaitin_G1_assembly / ImpSomeProof ) are reused
-- verbatim from  T4.CgiClashImp ;  only the ClashBody ( which embeds the
-- guard atom + KcodeAlph ) is mirrored.

open import T4.Base

module T4.CgiClashImpAlph (Lstar_meta : Nat) where

open import T4.Tags using ( tag_sb )
open import T4.Code using ( codeFalse )
open import T4.Num  using ( num )
open import T4.ThmT using ( thmT )
open import T4.ThmTAtSb using ( thmT_at_sb )
open import T4.SbF using ( sbf )
open import T4.SbT using ( sbt )
open import T4.SbtAtVar using ( sbt_at_var_match ; sbt_at_var_nomatch )
open import T4.NumInert using ( sbt_num_inert )
open import T4.DefWit using ( cEqTm ; cNeg ; cImp )
open import T4.ConInj using ( cmp )
open import T4.Thm12.EncodedMp using ( imp_encoded_mp )
open import T4.EncodedProp using ( encoded_exfalso ; exfProof )
open import T4.EvalUEval using ( evalU )
open import T4.ProgParse using ( parse )
open import T4.Kdef using ( runProg )
open import T4.KdefAlph Lstar_meta using ( KcodeAlph ; KcodeAlph_eval )
open import T4.CgiDPos using ( D )
open import T4.CgiClashAlph Lstar_meta using
  ( SomeProof ; mkProof ; cgiClashAlph
  ; passK ; cAp1f ; cAp2f ; chkAtomT ; KT ; defEqT ; cVarc )
open import T4.CgiClashImp using
  ( ImpSomeProof ; mkImpProof ; imp_dPos ; imp_chaitin_G1_assembly )
open import T4.Thm12.All using ( thm12_Fun2 ; fst )

open import T4.Thm12.ImpHelpers using ( impLift ; impCongR )
open import T4.ImpExtras using ( imp_eqTrans_imp )

open import BRA3.Church using ( pi )

------------------------------------------------------------------------
-- Body of the imp-lifted clash as a parametric module.

module ClashBodyAlph
  (Rf : Formula) (gL n0 x' w0 cValid : Term)
  (imp_dNeg : Deriv (imp Rf (eqF (ap1 thmT w0) (ap1 KcodeAlph x'))))
  (dValid   : Deriv (eqF (ap1 thmT cValid)
                          (chkAtomT gL n0 x' (ap1 num gL))))
  (imp_run  : Deriv (imp Rf (eqF (ap2 evalU (ap1 parse gL) n0) (ap1 s x'))))
  where

  S0 : Term
  S0 = ap1 num gL
  S1 : Term
  S1 = ap1 num n0
  spec0 : Term
  spec0 = ap2 Pair (natCode zero) S0
  spec1 : Term
  spec1 = ap2 Pair (natCode (suc zero)) S1

  KOpen : Term
  KOpen = KT gL n0 x' (cVarc zero) (cVarc (suc zero))
  KMid : Term
  KMid  = KT gL n0 x' (cVarc zero) (ap1 num n0)
  KClosed : Term
  KClosed = KT gL n0 x' (ap1 num gL) (ap1 num n0)

  innerEq : Deriv (eqF (ap2 sbf spec1 KOpen) KMid)
  innerEq =
    passK gL n0 x' (suc zero) S1
      (cVarc zero) (cVarc zero) (cVarc (suc zero)) (ap1 num n0)
      (sbt_at_var_nomatch (suc zero) zero S1 refl)
      (sbt_at_var_match (suc zero) S1)

  outerEq : Deriv (eqF (ap2 sbf spec0 KMid) KClosed)
  outerEq =
    passK gL n0 x' zero S0
      (cVarc zero) (ap1 num gL) (ap1 num n0) (ap1 num n0)
      (sbt_at_var_match zero S0)
      (sbt_num_inert zero S0 n0)

  substBoth : Deriv (eqF (ap2 sbf spec0 (ap2 sbf spec1 KOpen)) KClosed)
  substBoth = ruleTrans (congR sbf spec0 innerEq) outerEq

  imp_dNegOpen : Deriv (imp Rf (eqF (ap1 thmT w0) KOpen))
  imp_dNegOpen = imp_eqTrans_imp imp_dNeg (impLift {Rf} (KcodeAlph_eval x'))

  innerWrap : Term
  innerWrap = ap2 pi (natCode tag_sb) (ap2 pi spec1 w0)
  outerWrap : Term
  outerWrap = ap2 pi (natCode tag_sb) (ap2 pi spec0 innerWrap)

  imp_congR_inner :
    Deriv (imp Rf (eqF (ap2 sbf spec1 (ap1 thmT w0)) (ap2 sbf spec1 KOpen)))
  imp_congR_inner = impCongR sbf (ap1 thmT w0) KOpen spec1 imp_dNegOpen

  imp_dInner :
    Deriv (imp Rf (eqF (ap1 thmT innerWrap) (ap2 sbf spec1 KOpen)))
  imp_dInner = imp_eqTrans_imp (impLift {Rf} (thmT_at_sb spec1 w0))
                               imp_congR_inner

  imp_congR_outer :
    Deriv (imp Rf (eqF (ap2 sbf spec0 (ap1 thmT innerWrap))
                        (ap2 sbf spec0 (ap2 sbf spec1 KOpen))))
  imp_congR_outer = impCongR sbf (ap1 thmT innerWrap) (ap2 sbf spec1 KOpen)
                      spec0 imp_dInner

  imp_d_to_substBoth :
    Deriv (imp Rf (eqF (ap1 thmT outerWrap)
                        (ap2 sbf spec0 (ap2 sbf spec1 KOpen))))
  imp_d_to_substBoth =
    imp_eqTrans_imp (impLift {Rf} (thmT_at_sb spec0 innerWrap))
                    imp_congR_outer

  imp_dInst : Deriv (imp Rf (eqF (ap1 thmT outerWrap) KClosed))
  imp_dInst = imp_eqTrans_imp imp_d_to_substBoth (impLift {Rf} substBoth)

  imp_dNegFinal :
    Deriv (imp Rf (eqF (ap1 thmT (cmp outerWrap cValid)) (cNeg (D gL n0 x'))))
  imp_dNegFinal =
    imp_encoded_mp Rf outerWrap cValid
      (chkAtomT gL n0 x' (ap1 num gL))
      (cNeg (D gL n0 x'))
      imp_dInst (impLift {Rf} dValid)

  cPos : Term
  cPos = ap2 (fst (thm12_Fun2 runProg)) gL n0

  imp_dPosD : Deriv (imp Rf (eqF (ap1 thmT cPos) (D gL n0 x')))
  imp_dPosD = imp_dPos Rf gL n0 x' imp_run

  imp_dExF :
    Deriv (imp Rf (eqF (ap1 thmT (exfProof (D gL n0 x') codeFalse))
                        (cImp (D gL n0 x') (cImp (cNeg (D gL n0 x')) codeFalse))))
  imp_dExF = impLift {Rf} (encoded_exfalso (D gL n0 x') codeFalse)

  pf : Term
  pf = cmp (cmp (exfProof (D gL n0 x') codeFalse) cPos)
           (cmp outerWrap cValid)

  imp_final : Deriv (imp Rf (eqF (ap1 thmT pf) codeFalse))
  imp_final =
    imp_chaitin_G1_assembly Rf (D gL n0 x') cPos
      (exfProof (D gL n0 x') codeFalse) (cmp outerWrap cValid)
      imp_dPosD imp_dNegFinal imp_dExF

imp_cgiClashAlph :
  (Rf : Formula) (gL n0 x' w0 cValid : Term) ->
  Deriv (imp Rf (eqF (ap1 thmT w0) (ap1 KcodeAlph x'))) ->
  Deriv (eqF (ap1 thmT cValid) (chkAtomT gL n0 x' (ap1 num gL))) ->
  Deriv (imp Rf (eqF (ap2 evalU (ap1 parse gL) n0) (ap1 s x'))) ->
  ImpSomeProof Rf
imp_cgiClashAlph Rf gL n0 x' w0 cValid imp_dNeg dValid imp_run =
  let open ClashBodyAlph Rf gL n0 x' w0 cValid imp_dNeg dValid imp_run
  in mkImpProof pf imp_final
