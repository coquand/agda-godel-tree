{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.CgFunImp -- Carneiro-lifted (imp Rf) variant of T4.CgFun's
-- cgFalse.   Internalises the meta function  cgFalse : Deriv X -> Deriv Y
-- into a single closed Deriv of an internal implication.
--
-- HEADLINE.
--
--   cgFalseImp_general :
--     (Rf : Formula) (w : Term)
--     (sub0_w / sub1_w / sim_w : substitution-stability witnesses on w)
--     (hyp_imp : Deriv (imp Rf (eqF (ap1 thmT w) (ap1 (Kcode Lstar)
--                                                   (ap1 (outKdef Lstar) w)))))
--     (imp_runs_mu : Carneiro-lifted Construct.runs_mu -- the RESIDUAL,
--                    to be supplied by T4.StepU2MuCorrectImp in
--                    Phase 1's final step) ->
--     ImpSomeProof Rf
--
-- Returns an  ImpSomeProof  (= Sigma Term (\ pf -> Deriv (imp Rf (eqF
-- (ap1 thmT pf) codeFalse))) ) whose pf matches T4.CgFun.cgFun w by
-- Agda's definitional equality (both let-piles converge structurally).
--
-- The closing wrapper  cgFalseImp  (final Phase-1 deliverable, shipped
-- once  imp_runs_mu  is available) reads:
--
--   cgFalseImp : (Rf : Formula) (w : Term) ->
--     Deriv (imp Rf (eqF (ap1 thmT (closeW w))
--                         (ap1 (Kcode Lstar) (ap1 (outKdef Lstar) (closeW w))))) ->
--     Deriv (imp Rf (eqF (ap1 thmT (cgFun w)) codeFalse))
--   cgFalseImp Rf w hyp_imp =
--     Sigma.snd (cgFalseImp_general Rf (closeW w)
--                  (cl_w_sub0 w) (cl_w_sub1 w) (cl_w_sim w)
--                  hyp_imp imp_runs_mu_from_StepU2MuCorrectImp _)

module T4.CgFunImp where

open import T4.Base
open import T4.Code             using ( codeFalse )
open import T4.ThmT             using ( thmT )
open import T4.Kdef             using ( Kcode )
open import T4.KdefRecog        using ( hitKdef ; hitKdef_le_one ; outKdef )
open import T4.KdefDiag         using ( predFlipDef ; gLcodeDef )
open import T4.KGodel1BridgeDef using ( Lstar )
open import T4.CloseW           using ( closeW )
open import T4.ChaitinG1CoreNumRaw using
  ( gLnameDef ; cSizeProofDef ; dSizeDef )

open import T4.EvalU using ( mcodeMu ; mcode1 ; cfgEV ; cfgRT )
open import T4.StepU2 using ( step )
open import T4.EvalUEval using ( evalU )
open import T4.ProgParse using ( parse )
open import T4.ProgEnc   using ( enc )

import T4.FirstHit
import T4.ChaitinG1DischargeKdefImp as DKI
import T4.ChaitinG1ChainKdefImp     as CKI
open import T4.CgiClashImp using ( ImpSomeProof ; imp_cgiClash
                                   ; Sigma ; mkSigma )

open T4.FirstHit.Search
       (hitKdef Lstar (outKdef Lstar))
       (hitKdef_le_one Lstar (outKdef Lstar))
  using ( gRec )

open import BRA3.Church          using ( pi ; sigma ; sub )
open import BRA3.RuleInst2       using ( simSubstT )
open import BRA3.CourseOfValues  using ( iter )

------------------------------------------------------------------------
-- cgFalseImp_general -- the closure-witnessed Carneiro-lifted CGI-self.
--
-- Assembles the imp-lifted Discharge + Chain + CgiClash chain.   The
-- closed  imp_runs_mu  is the only residual; the rest is mechanical
-- mirroring of CgFun.agda's body.

cgFalseImp_general :
  (Rf : Formula) (w : Term) ->
  ((a : Term) -> Eq (substT zero a w) w) ->
  ((a : Term) -> Eq (substT (suc zero) a w) w) ->
  ((a b : Term) -> Eq (simSubstT zero a (suc zero) b w) w) ->
  Deriv (imp Rf (eqF (ap1 thmT w)
                      (ap1 (Kcode Lstar) (ap1 (outKdef Lstar) w)))) ->
  -- imp_runs_mu :  Carneiro-lifted Construct.runs_mu  residual.
  (fuelMu_fun : Fun2) ->
  ((x_outer K0 : Term) ->
     Deriv (imp Rf
            (eqF (ap2 (iter step)
                       (cfgEV (mcodeMu (mcode1 (predFlipDef Lstar)))
                              x_outer K0)
                       (ap2 sigma (ap1 s O)
                                   (ap2 fuelMu_fun
                                        (ap2 gRec O (ap1 s w))
                                        (ap2 gRec O (ap1 s w)))))
                  (cfgRT (ap2 gRec O (ap1 s w)) K0)))) ->
  ImpSomeProof Rf
cgFalseImp_general Rf w sub0_w sub1_w sim_w hyp_imp fuelMu_fun imp_runs_mu =
  let x_subj : Term
      x_subj = ap1 (outKdef Lstar) w

      open DKI.DischargeKdefImp Rf w x_subj hyp_imp sub0_w sub1_w sim_w
        using ( k_max ; x' ; imp_dNeg_at_kmax )

      open CKI.ChainKdefImp Rf w x_subj hyp_imp sub0_w sub1_w sim_w
        using ( module Chain )

      open Chain fuelMu_fun imp_runs_mu
        using ( nTerm ; imp_dEval_witness )

  in imp_cgiClash Rf Lstar gLnameDef nTerm x' k_max cSizeProofDef
       imp_dNeg_at_kmax dSizeDef imp_dEval_witness
