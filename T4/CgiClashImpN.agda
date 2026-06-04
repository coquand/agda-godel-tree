{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.CgiClashImpN -- the number-code re-pointing of T4.CgiClashImp : the
-- Carneiro-lifted (imp Rf) integrated clash at the honest p<N / runProgN
-- K-formula.   Mirrors CgiClashImp ( generic imp_thm13_binary /
-- imp_chaitin_G1_assembly reused ; only imp_dPos and the ClashBody re-point to
-- runProgN / DN / the binary leqAtomTN guard ).

module T4.CgiClashImpN where

open import T4.Base
open import T4.Tags using ( tag_sb ; tag_ap1 ; tag_ap2 ; tag_eq ; tag_var )
open import T4.Code using ( codeFun2 ; codeFalse ; codeTerm )
open import T4.Num  using ( num ; num_at_S )
open import T4.ThmT using ( thmT )
open import T4.ThmTAtSb using ( thmT_at_sb )
open import T4.SbF using ( sbf )
open import T4.SbT using ( sbt )
open import T4.SbtAtVar using ( sbt_at_var_match ; sbt_at_var_nomatch )
open import T4.NumInert using ( sbt_num_inert )
open import T4.DefWit using ( cEqTm ; cNeg ; cImp )
open import T4.ConInj using ( cmp )
open import T4.Thm12.EncodedMp using ( encoded_mp ; imp_encoded_mp )
open import T4.EncodedProp using ( encoded_exfalso ; exfProof )
open import T4.EvalUEval using ( evalU )
open import T4.ParseN using ( parseN ; runProgN ; runProgN_eq )
open import T4.CgiDPosN using ( DN )
open import T4.CgiClashN using
  ( passKN ; cAp1f ; cAp2f ; cVarc ; leqAtomTN ; defEqTN ; KTN )
open import T4.SbStep using ( NumCode )
open import T4.CgiClashImp using ( imp_thm13_binary ; imp_chaitin_G1_assembly
                                   ; ImpSomeProof ; Sigma ; mkImpProof )
open import T4.Thm12.All using ( thm12 ; thm12_Fun2 ; fst ; snd )
open import T4.Thm12.Thm13 using ( codeFXeqY2 ; thm13_binary )

open import T4.Thm12.ImpHelpers
  using ( impLift ; impMp ; impEqTrans ; impCong1 ; impCongL ; impCongR )
open import T4.ImpExtras using ( imp_eqTrans_imp )

import T4.KdefN

open import BRA3.Church using ( pi )

------------------------------------------------------------------------
-- imp_dPosN -- Carneiro-lifted CgiDPosN.dPosN ( runProgN ).

imp_dPosN :
  (Rf : Formula) (gL n0 x' : Term) ->
  Deriv (imp Rf (eqF (ap2 evalU (ap1 parseN gL) n0) (ap1 s x'))) ->
  Deriv (imp Rf (eqF (ap1 thmT (ap2 (fst (thm12_Fun2 runProgN)) gL n0))
                      (DN gL n0 x')))
imp_dPosN Rf gL n0 x' imp_rf =
  let run_eq : Deriv (eqF (ap2 runProgN gL n0) (ap2 evalU (ap1 parseN gL) n0))
      run_eq = runProgN_eq gL n0

      imp_run : Deriv (imp Rf (eqF (ap2 runProgN gL n0) (ap1 s x')))
      imp_run = impEqTrans (ap2 runProgN gL n0) (ap2 evalU (ap1 parseN gL) n0)
                  (ap1 s x') (impLift {Rf} run_eq) imp_rf

      imp_d1 : Deriv (imp Rf (eqF (ap1 thmT (ap2 (fst (thm12_Fun2 runProgN)) gL n0))
                                   (codeFXeqY2 runProgN gL n0 (ap1 s x'))))
      imp_d1 = imp_thm13_binary Rf runProgN gL n0 (ap1 s x') imp_run

      bridge : Deriv (eqF (codeFXeqY2 runProgN gL n0 (ap1 s x')) (DN gL n0 x'))
      bridge = congR Pair (natCode tag_eq)
                 (congR Pair (cAp2f runProgN (ap1 num gL) (ap1 num n0))
                   (num_at_S x'))

  in impEqTrans (ap1 thmT (ap2 (fst (thm12_Fun2 runProgN)) gL n0))
       (codeFXeqY2 runProgN gL n0 (ap1 s x')) (DN gL n0 x')
       imp_d1 (impLift {Rf} bridge)

------------------------------------------------------------------------
-- The integrated imp-lifted clash body.

module ClashBody
  (Rf : Formula) (Nthr : Term) (ncN : NumCode (codeTerm Nthr))
  (gL n0 x' w0 cSize : Term)
  (imp_dNeg : Deriv (imp Rf (eqF (ap1 thmT w0) (ap1 (T4.KdefN.KcodeN Nthr) x'))))
  (dSize    : Deriv (eqF (ap1 thmT cSize)
                          (leqAtomTN Nthr ncN gL n0 x' (ap1 num gL))))
  (imp_run  : Deriv (imp Rf (eqF (ap2 evalU (ap1 parseN gL) n0) (ap1 s x'))))
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
  KOpen = KTN Nthr ncN gL n0 x' (cVarc zero) (cVarc (suc zero))
  KMid : Term
  KMid  = KTN Nthr ncN gL n0 x' (cVarc zero) (ap1 num n0)
  KClosed : Term
  KClosed = KTN Nthr ncN gL n0 x' (ap1 num gL) (ap1 num n0)

  innerEq : Deriv (eqF (ap2 sbf spec1 KOpen) KMid)
  innerEq =
    passKN Nthr ncN gL n0 x' (suc zero) S1
      (cVarc zero) (cVarc zero) (cVarc (suc zero)) (ap1 num n0)
      (sbt_at_var_nomatch (suc zero) zero S1 refl)
      (sbt_at_var_match (suc zero) S1)

  outerEq : Deriv (eqF (ap2 sbf spec0 KMid) KClosed)
  outerEq =
    passKN Nthr ncN gL n0 x' zero S0
      (cVarc zero) (ap1 num gL) (ap1 num n0) (ap1 num n0)
      (sbt_at_var_match zero S0)
      (sbt_num_inert zero S0 n0)

  substBoth : Deriv (eqF (ap2 sbf spec0 (ap2 sbf spec1 KOpen)) KClosed)
  substBoth = ruleTrans (congR sbf spec0 innerEq) outerEq

  imp_dNegOpen : Deriv (imp Rf (eqF (ap1 thmT w0) KOpen))
  imp_dNegOpen = imp_eqTrans_imp imp_dNeg (impLift {Rf} (T4.KdefN.KcodeN_eval Nthr x'))

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
    Deriv (imp Rf (eqF (ap1 thmT (cmp outerWrap cSize)) (cNeg (DN gL n0 x'))))
  imp_dNegFinal =
    imp_encoded_mp Rf outerWrap cSize
      (leqAtomTN Nthr ncN gL n0 x' (ap1 num gL))
      (cNeg (DN gL n0 x'))
      imp_dInst (impLift {Rf} dSize)

  cPos : Term
  cPos = ap2 (fst (thm12_Fun2 runProgN)) gL n0

  imp_dPosD : Deriv (imp Rf (eqF (ap1 thmT cPos) (DN gL n0 x')))
  imp_dPosD = imp_dPosN Rf gL n0 x' imp_run

  imp_dExF :
    Deriv (imp Rf (eqF (ap1 thmT (exfProof (DN gL n0 x') codeFalse))
                        (cImp (DN gL n0 x') (cImp (cNeg (DN gL n0 x')) codeFalse))))
  imp_dExF = impLift {Rf} (encoded_exfalso (DN gL n0 x') codeFalse)

  pf : Term
  pf = cmp (cmp (exfProof (DN gL n0 x') codeFalse) cPos)
           (cmp outerWrap cSize)

  imp_final : Deriv (imp Rf (eqF (ap1 thmT pf) codeFalse))
  imp_final =
    imp_chaitin_G1_assembly Rf (DN gL n0 x') cPos
      (exfProof (DN gL n0 x') codeFalse) (cmp outerWrap cSize)
      imp_dPosD imp_dNegFinal imp_dExF

imp_cgiClashN :
  (Rf : Formula) (Nthr : Term) (ncN : NumCode (codeTerm Nthr))
  (gL n0 x' w0 cSize : Term) ->
  Deriv (imp Rf (eqF (ap1 thmT w0) (ap1 (T4.KdefN.KcodeN Nthr) x'))) ->
  Deriv (eqF (ap1 thmT cSize) (leqAtomTN Nthr ncN gL n0 x' (ap1 num gL))) ->
  Deriv (imp Rf (eqF (ap2 evalU (ap1 parseN gL) n0) (ap1 s x'))) ->
  ImpSomeProof Rf
imp_cgiClashN Rf Nthr ncN gL n0 x' w0 cSize imp_dNeg dSize imp_run =
  let open ClashBody Rf Nthr ncN gL n0 x' w0 cSize imp_dNeg dSize imp_run
  in mkImpProof pf imp_final
