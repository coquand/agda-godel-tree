{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.CgFun -- the  cgFun : Term -> Term  /  cgFalse  decomposition of
-- BRA4.ChaitinG1CoreNumRawSelf.CGI_core_num_raw_self .
--
-- =================================================================
-- WHAT THIS FILE SHIPS.
-- =================================================================
--
-- The  Sigma  payload of  CGI_core_num_raw_self  is  (z(w), proof(w, d))
-- where the Term  z(w)  is structurally  d -independent: every Term
-- piece passing through  DischargeKdef + ChainKdef + cgiClash  is built
-- from  closeW w  + constants ( gRec , predFlipDef , outKdef , runProg ,
-- fuelMu_fun , fuelG , Thm12 -derived  Df , and the  cmp / exfProof /
-- pi / sb -spec  tags), while the Deriv  d  is only consumed by the
-- (.snd) half ( SomeProof.isPf ).
--
-- Concretely (replicating the let-chain that  CGI_core_num_raw  /
-- ChainKdef  /  cgiClash  produce after Agda reductions):
--
--   cw       = closeW w
--   k_max    = ap2 gRec O (ap1 s cw)
--   x'       = ap1 (outKdef Lstar) k_max
--   nTerm    = fuelN   ( a sigma-pile in  k_max + bF/bG -fuel constants )
--   cPos     = ap2 (fst (thm12_Fun2 runProg)) gLnameDef nTerm
--   D_eq     = cEqTm (cAp2f runProg (num gLnameDef) (num nTerm))
--                    (cAp1f s (num x'))
--   wrap     = ap2 pi (natCode tag_sb)
--                (ap2 pi (Pair (natCode 0) (num gLnameDef))
--                    (ap2 pi (natCode tag_sb)
--                         (ap2 pi (Pair (natCode 1) (num nTerm)) k_max)))
--   cgFun w  = cmp (cmp (exfProof D_eq codeFalse) cPos) (cmp wrap cSizeProofDef)
--
-- Both halves of the decomposition (cgFun and cgFalse) typecheck
-- against the existing  CGI_core_num_raw_self  by  refl  -- no new
-- mathematics, just the Sigma projections with the Term half inlined.

module BRA4.CgFun where

open import BRA4.Base
open import BRA4.Code             using ( codeFalse )
open import BRA4.Tags             using ( tag_sb )
open import BRA4.ThmT             using ( thmT )
open import BRA4.Num              using ( num )
open import BRA4.DefWit           using ( cEqTm )
open import BRA4.Kdef             using ( runProg ; Kcode )
open import BRA4.KdefRecog        using ( hitKdef ; hitKdef_le_one ; outKdef )
open import BRA4.KdefDiag         using ( predFlipDef )
open import BRA4.KGodel1BridgeDef using ( Lstar )
open import BRA4.CloseW           using ( closeW )
open import BRA4.CgiClash         using ( cAp1f ; cAp2f )
open import BRA4.ConInj           using ( cmp )
open import BRA4.EncodedProp      using ( exfProof )
open import BRA4.StepU2Correct1New using ( correct1 ; correct2 )
open import BRA4.StepU2CorrectAPI using
  ( Correct1 ; Correct2 ; fuelF ; fuelG )
open import BRA4.ChaitinG1CoreNumRaw using
  ( gLnameDef ; cSizeProofDef )
  renaming ( snd to sig_snd )
open import BRA4.ChaitinG1CoreNumRawSelf using ( CGI_core_num_raw_self )

import BRA4.Thm12.All as ThmAll

import BRA4.FirstHit

open BRA4.FirstHit.Search
       (hitKdef Lstar (outKdef Lstar))
       (hitKdef_le_one Lstar (outKdef Lstar))
  using ( gRec )

open import BRA3.Church          using ( pi ; sigma ; sub )
open import BRA3.Fan             using ( Lift1 ; Lift2 ; Fan )
open import BRA3.PairAlgebra     using ( Pair ; Post )

------------------------------------------------------------------------
-- Local constants (replicating  Construct.fuelMu_fun  and the
--  bG = correct2 (Lift1 outL)  used in  ChainKdef , so the resulting
-- composite Term matches  fst (CGI_core_num_raw_self w d)  by  refl ).

private
  Df_runProg : Fun2
  Df_runProg = ThmAll.fst (ThmAll.thm12_Fun2 runProg)

  outL_c : Fun1
  outL_c = outKdef Lstar

  gFun_c : Fun1
  gFun_c = predFlipDef Lstar

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
-- cgFun :  Term -> Term  -- the uniform-in- w  Term construction.

cgFun : Term -> Term
cgFun w =
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
      S0           = ap1 num gLnameDef

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
      cPos         = ap2 Df_runProg gLnameDef nTerm

      D_eq         : Term
      D_eq         = cEqTm (cAp2f runProg (ap1 num gLnameDef) (ap1 num nTerm))
                           (cAp1f s (ap1 num x'))
  in cmp (cmp (exfProof D_eq codeFalse) cPos)
         (cmp outerWrap cSizeProofDef)

------------------------------------------------------------------------
-- cgFalse :  the self-referential Chaitin-Goedel-I conclusion at
--  cgFun w .   The proof is one line: project the (.snd) half of
--  CGI_core_num_raw_self ; the (.fst) half is  definitionally  cgFun w
-- (Agda's let-substitution + record-projection unfolding sees that the
-- DischargeKdef / ChainKdef / cgiClash chain collapses to exactly the
-- let-chain above).

cgFalse :
  (w : Term) ->
  Deriv (eqF (ap1 thmT w) (ap1 (Kcode Lstar) (ap1 (outKdef Lstar) w))) ->
  Deriv (eqF (ap1 thmT (cgFun w)) codeFalse)
cgFalse w d = sig_snd (CGI_core_num_raw_self w d)
