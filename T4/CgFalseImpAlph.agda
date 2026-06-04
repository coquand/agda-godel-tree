{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.CgFalseImpAlph -- Phase-1 closing wrapper at the  checkAlphN -guard
-- shape.   Analog of  T4.CgFalseImp .   Wires the generic ( gFun -parametric )
-- T4.StepU2MuCorrectImp.ImpConstruct  into  cgFalseImpAlph_general .
--
-- Headline ( deduction-theorem form, the assembly consumes this ):
--
--   cgFalseImpDedAlph :
--     (checkFires) (w : Term) (sub0_w / sub1_w / sim_w) ->
--     Deriv (imp (eqF (ap1 thmT w)
--                      (ap1 KcodeAlph (ap1 outKdefAlph w)))
--                 (eqF (ap1 thmT (cgFunAlph w)) codeFalse))
--
-- carrying the validity residual  checkFires  ( "the diagonal program is a
-- valid code of depth <= Lstar_meta" -- the  L*-large-enough  assumption ).

open import T4.Base

module T4.CgFalseImpAlph (Lstar_meta : Nat) where

open import T4.Code             using ( codeFalse )
open import T4.ThmT             using ( thmT )
open import T4.KdefAlph Lstar_meta using ( KcodeAlph )
open import T4.KdefRecogAlph Lstar_meta using ( outKdefAlph )
open import T4.KdefDiagAlph Lstar_meta using ( gLcodeDefAlph )
open import T4.CheckAlphN       using ( checkAlphN )
open import T4.CloseW           using ( closeW ; cl_w_sub0 ; cl_w_sub1 ; cl_w_sim )
open import T4.CgFunAlph Lstar_meta using ( cgFunAlph )
open import T4.StepU2Correct1New using ( correct1 )
open import T4.StepU2CorrectAPI  using ( Correct1 )
open import T4.ProgEnc          using ( enc )

open import T4.Thm12.ImpHelpers using ( impRefl )

import T4.ChaitinG1DischargeKdefImpAlph as DKI
import T4.StepU2MuCorrectImp            as MCI

open import T4.CgFunImpAlph Lstar_meta using ( cgFalseImpAlph_general )
open import T4.CgiClashImp using ( ImpSomeProof ; Sigma )

open import BRA3.RuleInst2 using ( simSubstT ; simSubstF )
open import BRA3.Formula   using ( substF )

------------------------------------------------------------------------
-- cgFalseImpAlph .

cgFalseImpAlph :
  Deriv (eqF (ap1 (checkAlphN Lstar_meta) (enc gLcodeDefAlph)) (ap1 s O)) ->
  (Rf : Formula) (w : Term) ->
  ((a : Term) -> Eq (substF zero a Rf) Rf) ->
  ((a : Term) -> Eq (substF (suc zero) a Rf) Rf) ->
  ((a b : Term) -> Eq (simSubstF zero a (suc zero) b Rf) Rf) ->
  Deriv (imp Rf (eqF (ap1 thmT (closeW w))
                      (ap1 KcodeAlph (ap1 outKdefAlph (closeW w))))) ->
  Deriv (imp Rf (eqF (ap1 thmT (cgFunAlph w)) codeFalse))
cgFalseImpAlph checkFires Rf w sub0_Rf sub1_Rf sim_Rf hyp_imp =
  let
    cw : Term
    cw = closeW w

    x_subj : Term
    x_subj = ap1 outKdefAlph cw

    open DKI.DischargeKdefImpAlph
      Lstar_meta Rf cw x_subj hyp_imp (cl_w_sub0 w) (cl_w_sub1 w) (cl_w_sim w)
      using ( gFun ; predFun ; k_max ; imp_isHit
            ; missSucc ; subSuccBridge_at ; leqDecrease_at ; subBoundsAux_at
            ; leqRefl_k_max ; sub_k_max_k_max
            ; k_max_sub0 ; k_max_sub1 ; k_max_sim )

    bF : Correct1 gFun
    bF = correct1 gFun

    open MCI.ImpConstruct
      Rf gFun bF k_max predFun
      imp_isHit
      missSucc subSuccBridge_at leqDecrease_at subBoundsAux_at
      leqRefl_k_max sub_k_max_k_max
      k_max_sub0 k_max_sub1 k_max_sim
      sub0_Rf sub1_Rf sim_Rf
      using ( fuelMu_fun ; imp_runs_mu )

    result : ImpSomeProof Rf
    result = cgFalseImpAlph_general checkFires Rf cw
              (cl_w_sub0 w) (cl_w_sub1 w) (cl_w_sim w)
              hyp_imp fuelMu_fun imp_runs_mu

  in Sigma.snd result

------------------------------------------------------------------------
-- cgFalseImpDedAlph :  deduction-theorem internalisation.

cgFalseImpDedAlph :
  Deriv (eqF (ap1 (checkAlphN Lstar_meta) (enc gLcodeDefAlph)) (ap1 s O)) ->
  (w : Term) ->
  ((a : Term) -> Eq (substT zero a w) w) ->
  ((a : Term) -> Eq (substT (suc zero) a w) w) ->
  ((a b : Term) -> Eq (simSubstT zero a (suc zero) b w) w) ->
  Deriv (imp (eqF (ap1 thmT w)
                   (ap1 KcodeAlph (ap1 outKdefAlph w)))
              (eqF (ap1 thmT (cgFunAlph w)) codeFalse))
cgFalseImpDedAlph checkFires w sub0_w sub1_w sim_w =
  let
    HypAt : Term -> Formula
    HypAt t = eqF (ap1 thmT t) (ap1 KcodeAlph (ap1 outKdefAlph t))

    Hyp : Formula
    Hyp = HypAt w

    sub0_Hyp : (a : Term) -> Eq (substF zero a Hyp) Hyp
    sub0_Hyp a = eqCong HypAt (sub0_w a)

    sub1_Hyp : (a : Term) -> Eq (substF (suc zero) a Hyp) Hyp
    sub1_Hyp a = eqCong HypAt (sub1_w a)

    sim_Hyp : (a b : Term) -> Eq (simSubstF zero a (suc zero) b Hyp) Hyp
    sim_Hyp a b = eqCong HypAt (sim_w a b)

    cw_eq_w : Eq (closeW w) w
    cw_eq_w =
      eqTrans
        (eqCong (substT zero O) (sub1_w O))
        (sub0_w O)

    hyp_imp :
      Deriv (imp Hyp
             (eqF (ap1 thmT (closeW w))
                   (ap1 KcodeAlph (ap1 outKdefAlph (closeW w)))))
    hyp_imp =
      eqSubst (\ t -> Deriv (imp Hyp (HypAt t)))
              (eqSym cw_eq_w) (impRefl Hyp)
  in cgFalseImpAlph checkFires Hyp w sub0_Hyp sub1_Hyp sim_Hyp hyp_imp
