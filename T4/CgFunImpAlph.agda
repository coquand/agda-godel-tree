{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.CgFunImpAlph -- Carneiro-lifted (imp Rf) CGI-self at the  checkAlphN -
-- guard shape.   Analog of  T4.CgFunImp .   Carries the validity residual
-- checkFires  ( see  T4.ChaitinG1CoreNumRawAlph ).

open import T4.Base

module T4.CgFunImpAlph (Lstar_meta : Nat) where

open import T4.Code             using ( codeFalse )
open import T4.ThmT             using ( thmT )
open import T4.KdefAlph Lstar_meta using ( KcodeAlph )
open import T4.KdefRecogAlph Lstar_meta using ( hitKdefAlph ; hitKdefAlph_le_one ; outKdefAlph )
open import T4.KdefDiagAlph Lstar_meta using ( predFlipDefAlph ; gLcodeDefAlph )
open import T4.CheckAlphN       using ( checkAlphN )
open import T4.CloseW           using ( closeW )
open import T4.ChaitinG1CoreNumRawAlph Lstar_meta using
  ( gLnameAlph ; cValidProofAlph ; dValidAlph )

open import T4.EvalU using ( mcodeMu ; mcode1 ; cfgEV ; cfgRT )
open import T4.StepU2 using ( step )
open import T4.EvalUEval using ( evalU )
open import T4.ProgParse using ( parse )
open import T4.ProgEnc   using ( enc )

import T4.FirstHit
import T4.ChaitinG1DischargeKdefImpAlph as DKI
import T4.ChaitinG1ChainKdefImpAlph     as CKI
open import T4.CgiClashImpAlph Lstar_meta using ( imp_cgiClashAlph )
open import T4.CgiClashImp using ( ImpSomeProof ; Sigma ; mkSigma )

open T4.FirstHit.Search
       (hitKdefAlph outKdefAlph)
       (hitKdefAlph_le_one outKdefAlph)
  using ( gRec )

open import BRA3.Church          using ( pi ; sigma ; sub )
open import BRA3.RuleInst2       using ( simSubstT )
open import BRA3.CourseOfValues  using ( iter )

------------------------------------------------------------------------
-- cgFalseImpAlph_general .

cgFalseImpAlph_general :
  Deriv (eqF (ap1 (checkAlphN Lstar_meta) (enc gLcodeDefAlph)) (ap1 s O)) ->   -- checkFires
  (Rf : Formula) (w : Term) ->
  ((a : Term) -> Eq (substT zero a w) w) ->
  ((a : Term) -> Eq (substT (suc zero) a w) w) ->
  ((a b : Term) -> Eq (simSubstT zero a (suc zero) b w) w) ->
  Deriv (imp Rf (eqF (ap1 thmT w)
                      (ap1 KcodeAlph (ap1 outKdefAlph w)))) ->
  (fuelMu_fun : Fun2) ->
  ((x_outer K0 : Term) ->
     Deriv (imp Rf
            (eqF (ap2 (iter step)
                       (cfgEV (mcodeMu (mcode1 predFlipDefAlph))
                              x_outer K0)
                       (ap2 sigma (ap1 s O)
                                   (ap2 fuelMu_fun
                                        (ap2 gRec O (ap1 s w))
                                        (ap2 gRec O (ap1 s w)))))
                  (cfgRT (ap2 gRec O (ap1 s w)) K0)))) ->
  ImpSomeProof Rf
cgFalseImpAlph_general checkFires Rf w sub0_w sub1_w sim_w hyp_imp fuelMu_fun imp_runs_mu =
  let x_subj : Term
      x_subj = ap1 outKdefAlph w

      open DKI.DischargeKdefImpAlph Lstar_meta Rf w x_subj hyp_imp sub0_w sub1_w sim_w
        using ( k_max ; x' ; imp_dNeg_at_kmax )

      open CKI.ChainKdefImpAlph Lstar_meta Rf w x_subj hyp_imp sub0_w sub1_w sim_w
        using ( module Chain )

      open Chain fuelMu_fun imp_runs_mu
        using ( nTerm ; imp_dEval_witness )

  in imp_cgiClashAlph Rf gLnameAlph nTerm x' k_max cValidProofAlph
       imp_dNeg_at_kmax (dValidAlph checkFires) imp_dEval_witness
