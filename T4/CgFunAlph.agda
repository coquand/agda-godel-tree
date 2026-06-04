{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.CgFunAlph -- the  cgFunAlph / cgFalseAlph  decomposition of
-- CGI_core_num_raw_self_Alph , the  checkAlphN -guard analog of  T4.CgFun .

open import T4.Base

module T4.CgFunAlph (Lstar_meta : Nat) where

open import T4.Code             using ( codeFalse )
open import T4.Tags             using ( tag_sb )
open import T4.ThmT             using ( thmT )
open import T4.Num              using ( num )
open import T4.DefWit           using ( cEqTm )
open import T4.Kdef             using ( runProg )
open import T4.KdefAlph Lstar_meta using ( KcodeAlph )
open import T4.KdefRecogAlph Lstar_meta using ( hitKdefAlph ; hitKdefAlph_le_one ; outKdefAlph )
open import T4.KdefDiagAlph Lstar_meta using ( predFlipDefAlph )
open import T4.CheckAlphN       using ( checkAlphN )
open import T4.ProgEnc          using ( enc )
open import T4.CloseW           using ( closeW )
open import T4.KdefDiagAlph Lstar_meta using ( gLcodeDefAlph )
open import T4.CgiClashAlph Lstar_meta using ( cAp1f ; cAp2f )
open import T4.ConInj           using ( cmp )
open import T4.EncodedProp      using ( exfProof )
open import T4.StepU2Correct1New using ( correct1 ; correct2 )
open import T4.StepU2CorrectAPI using
  ( Correct1 ; Correct2 ; fuelF ; fuelG )
open import T4.ChaitinG1CoreNumRawAlph Lstar_meta using
  ( gLnameAlph ; cValidProofAlph )
  renaming ( snd to sig_snd )
open import T4.ChaitinG1CoreNumRawSelfAlph Lstar_meta using ( CGI_core_num_raw_self_Alph )

import T4.Thm12.All as ThmAll

import T4.FirstHit

open T4.FirstHit.Search
       (hitKdefAlph outKdefAlph)
       (hitKdefAlph_le_one outKdefAlph)
  using ( gRec )

open import BRA3.Church          using ( pi ; sigma ; sub )
open import BRA3.Fan             using ( Lift1 ; Lift2 ; Fan )
open import BRA3.PairAlgebra     using ( Pair ; Post )

------------------------------------------------------------------------
-- Local constants ( replicating the fuel pile  CGI_core_num_raw_Alph
-- produces, so the composite Term matches  fst (CGI_core_num_raw_self_Alph
-- _ w d)  by  refl ).

private
  Df_runProg : Fun2
  Df_runProg = ThmAll.fst (ThmAll.thm12_Fun2 runProg)

  outL_c : Fun1
  outL_c = outKdefAlph

  gFun_c : Fun1
  gFun_c = predFlipDefAlph

  bF_c : Correct1 gFun_c
  bF_c = correct1 gFun_c

  fG_c : Fun1
  fG_c = fuelF bF_c

  fuelBase_c : Fun1
  fuelBase_c = C sigma fG_c (constN 1)

  sub_at_s_c : Fun2
  sub_at_s_c = Fan (Lift1 u) (Lift2 s) sub

  fuelStepH2_c : Fun2
  fuelStepH2_c = Fan (Post fG_c sub_at_s_c) (Lift1 (constN 1)) sigma

  fuelMu_c : Fun2
  fuelMu_c = R fuelBase_c sigma fuelStepH2_c

  bG_c : Correct2 (Lift1 outL_c)
  bG_c = correct2 (Lift1 outL_c)

  fuelG_c : Fun2
  fuelG_c = fuelG bG_c

------------------------------------------------------------------------
-- cgFunAlph :  Term -> Term  -- the uniform-in- w  Term construction.

cgFunAlph : Term -> Term
cgFunAlph w =
  let cw           : Term
      cw           = closeW w

      k_max        : Term
      k_max        = ap2 gRec O (ap1 s cw)

      x'           : Term
      x'           = ap1 outL_c k_max

      seg2_mu_fuel : Term
      seg2_mu_fuel = ap2 sigma (ap1 s O) (ap2 fuelMu_c k_max k_max)

      fuelA        : Term
      fuelA        = ap1 s O

      fuelAB       : Term
      fuelAB       = ap2 sigma fuelA seg2_mu_fuel

      fuelABC      : Term
      fuelABC      = ap2 sigma fuelAB (ap1 s O)

      fuelD        : Term
      fuelD        = ap2 sigma fuelABC (ap1 s O)

      fuelE        : Term
      fuelE        = ap2 sigma fuelD (ap1 s O)

      fGouter      : Term
      fGouter      = ap2 fuelG_c k_max O

      fuelM        : Term
      fuelM        = ap2 sigma fuelE fGouter

      fuelN        : Term
      fuelN        = ap2 sigma fuelM (ap1 s O)

      nTerm        : Term
      nTerm        = fuelN

      S0           : Term
      S0           = ap1 num gLnameAlph

      S1           : Term
      S1           = ap1 num nTerm

      spec0        : Term
      spec0        = ap2 Pair (natCode zero) S0

      spec1        : Term
      spec1        = ap2 Pair (natCode (suc zero)) S1

      innerWrap    : Term
      innerWrap    = ap2 pi (natCode tag_sb) (ap2 pi spec1 k_max)

      outerWrap    : Term
      outerWrap    = ap2 pi (natCode tag_sb) (ap2 pi spec0 innerWrap)

      cPos         : Term
      cPos         = ap2 Df_runProg gLnameAlph nTerm

      D_eq         : Term
      D_eq         = cEqTm (cAp2f runProg (ap1 num gLnameAlph) (ap1 num nTerm))
                           (cAp1f s (ap1 num x'))
  in cmp (cmp (exfProof D_eq codeFalse) cPos)
         (cmp outerWrap cValidProofAlph)

------------------------------------------------------------------------
-- cgFalseAlph :  the self-referential Chaitin-Goedel-I conclusion at
--  cgFunAlph w , carrying the validity residual  checkFires .

cgFalseAlph :
  Deriv (eqF (ap1 (checkAlphN Lstar_meta) (enc gLcodeDefAlph)) (ap1 s O)) ->
  (w : Term) ->
  Deriv (eqF (ap1 thmT w) (ap1 KcodeAlph (ap1 outKdefAlph w))) ->
  Deriv (eqF (ap1 thmT (cgFunAlph w)) codeFalse)
cgFalseAlph checkFires w d = sig_snd (CGI_core_num_raw_self_Alph checkFires w d)
