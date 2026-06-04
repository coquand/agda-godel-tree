{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.CgFalseImpN -- the number-code re-pointing of T4.CgFalseImp : the
-- deduction-theorem internalisation of the Carneiro-lifted CGI-self.  Wires
-- DischargeKdefImpN + StepU2MuCorrectImp.ImpConstruct (generic) +
-- CgFunImpN.cgFalseImp_generalN, then internalises the meta arrow at Rf := the
-- hypothesis itself.   The diagonal  gFunN w  is the Sigma.fst projection (no
-- explicit diagonal-term replication needed).

module T4.CgFalseImpN where

open import T4.Base
open import T4.Code             using ( codeFalse )
open import T4.ThmT             using ( thmT )
open import T4.KGodel1BridgeDefN using ( NthrN )
open import T4.CloseW           using ( closeW ; cl_w_sub0 ; cl_w_sub1 ; cl_w_sim )
open import T4.StepU2Correct1New using ( correct1 )
open import T4.CgFunImpN        using ( cgFalseImp_generalN )
open import T4.CgiClashImp      using ( ImpSomeProof ; Sigma )

open import T4.KdefN     NthrN using ( KcodeN )
open import T4.KdefRecogN NthrN using ( outKdefN )

import T4.ChaitinG1DischargeKdefImpN as DKI
import T4.StepU2MuCorrectImp        as MCI

open import T4.Thm12.ImpHelpers using ( impRefl )

open import BRA3.RuleInst2 using ( simSubstT ; simSubstF )
open import BRA3.Formula   using ( substF )

------------------------------------------------------------------------
-- HypAtN  -- the self-referential K-form hypothesis.

HypAtN : Term -> Formula
HypAtN t = eqF (ap1 thmT t) (ap1 KcodeN (ap1 outKdefN t))

------------------------------------------------------------------------
-- cgFalseImpN -- the imp-lifted CGI-self ( ImpSomeProof at Rf, closeW-threaded ).

cgFalseImpN :
  (Rf : Formula) (w : Term) ->
  ((a : Term) -> Eq (substF zero a Rf) Rf) ->
  ((a : Term) -> Eq (substF (suc zero) a Rf) Rf) ->
  ((a b : Term) -> Eq (simSubstF zero a (suc zero) b Rf) Rf) ->
  Deriv (imp Rf (HypAtN (closeW w))) ->
  ImpSomeProof Rf
cgFalseImpN Rf w sub0_Rf sub1_Rf sim_Rf hyp_imp =
  let cw : Term
      cw = closeW w

      x_subj : Term
      x_subj = ap1 outKdefN cw

      open DKI.DischargeKdefImpN NthrN
        Rf cw x_subj hyp_imp (cl_w_sub0 w) (cl_w_sub1 w) (cl_w_sim w)
        using ( gFun ; predFun ; k_max ; imp_isHit
              ; missSucc ; subSuccBridge_at ; leqDecrease_at ; subBoundsAux_at
              ; leqRefl_k_max ; sub_k_max_k_max
              ; k_max_sub0 ; k_max_sub1 ; k_max_sim )

      bF = correct1 gFun

      open MCI.ImpConstruct
        Rf gFun bF k_max predFun
        imp_isHit
        missSucc subSuccBridge_at leqDecrease_at subBoundsAux_at
        leqRefl_k_max sub_k_max_k_max
        k_max_sub0 k_max_sub1 k_max_sim
        sub0_Rf sub1_Rf sim_Rf
        using ( fuelMu_fun ; imp_runs_mu )

  in cgFalseImp_generalN Rf cw (cl_w_sub0 w) (cl_w_sub1 w) (cl_w_sim w)
       hyp_imp fuelMu_fun imp_runs_mu

------------------------------------------------------------------------
-- cgFalseImpDedN -- internalise the meta arrow at Rf := HypAtN w .

cgFalseImpDedN :
  (w : Term) ->
  ((a : Term) -> Eq (substT zero a w) w) ->
  ((a : Term) -> Eq (substT (suc zero) a w) w) ->
  ((a b : Term) -> Eq (simSubstT zero a (suc zero) b w) w) ->
  Sigma Term (\ pf -> Deriv (imp (HypAtN w) (eqF (ap1 thmT pf) codeFalse)))
cgFalseImpDedN w sub0_w sub1_w sim_w =
  let Hyp : Formula
      Hyp = HypAtN w

      sub0_Hyp : (a : Term) -> Eq (substF zero a Hyp) Hyp
      sub0_Hyp a = eqCong HypAtN (sub0_w a)

      sub1_Hyp : (a : Term) -> Eq (substF (suc zero) a Hyp) Hyp
      sub1_Hyp a = eqCong HypAtN (sub1_w a)

      sim_Hyp : (a b : Term) -> Eq (simSubstF zero a (suc zero) b Hyp) Hyp
      sim_Hyp a b = eqCong HypAtN (sim_w a b)

      cw_eq_w : Eq (closeW w) w
      cw_eq_w =
        eqTrans (eqCong (substT zero O) (sub1_w O)) (sub0_w O)

      hyp_imp : Deriv (imp Hyp (HypAtN (closeW w)))
      hyp_imp =
        eqSubst (\ t -> Deriv (imp Hyp (HypAtN t))) (eqSym cw_eq_w) (impRefl Hyp)
  in cgFalseImpN Hyp w sub0_Hyp sub1_Hyp sim_Hyp hyp_imp
