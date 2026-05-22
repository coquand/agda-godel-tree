{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.ThmTAtAx11 -- axiom 11 (axK) :  A > (B > A) .  extra = pi codeA codeB.

module BRA4.ThmTAtAx11 where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code
open import BRA4.CoVSpec
open import BRA4.SbT          using ( get_tag ; get_body )
open import BRA4.ThmT
open import BRA4.PiPositivity
open import BRA4.ThmTAtAxCommon

open import BRA3.Church          using ( pi )
open import BRA3.ChurchT117      using ( Fst )
open import BRA3.ChurchT116      using ( Snd )
open import BRA3.PairAlgebra     using
  ( axFst ; axSnd ; compose1U ; compose1U_eq )
open import BRA3.Dispatch        using ( constN ; constN_eq )
open import BRA3.SubT.V2NatNeq   using ( NatNeqWitness )

private
  N11 : Nat
  N11 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))

  -- Output : pi tag_imp (pi A (pi tag_imp (pi B A))) where A=Fst extra, B=Snd extra.
  outputRHS : Term -> Term
  outputRHS extra =
    ap2 pi (natCode tag_imp)
      (ap2 pi (ap1 Fst extra)
        (ap2 pi (natCode tag_imp)
          (ap2 pi (ap1 Snd extra) (ap1 Fst extra))))

  witness110 : NatNeqWitness N11 zero
  witness110 = natEqFalse_to_witness zero N11 refl
  witness111 : NatNeqWitness N11 (suc zero)
  witness111 = natEqFalse_to_witness (suc zero) N11 refl
  witness112 : NatNeqWitness N11 (suc (suc zero))
  witness112 = natEqFalse_to_witness (suc (suc zero)) N11 refl
  witness113 : NatNeqWitness N11 (suc (suc (suc zero)))
  witness113 = natEqFalse_to_witness (suc (suc (suc zero))) N11 refl
  witness114 : NatNeqWitness N11 (suc (suc (suc (suc zero))))
  witness114 = natEqFalse_to_witness (suc (suc (suc (suc zero)))) N11 refl
  witness115 : NatNeqWitness N11 (suc (suc (suc (suc (suc zero)))))
  witness115 = natEqFalse_to_witness (suc (suc (suc (suc (suc zero))))) N11 refl
  witness116 : NatNeqWitness N11 (suc (suc (suc (suc (suc (suc zero))))))
  witness116 = natEqFalse_to_witness (suc (suc (suc (suc (suc (suc zero)))))) N11 refl
  witness117 : NatNeqWitness N11 (suc (suc (suc (suc (suc (suc (suc zero)))))))
  witness117 = natEqFalse_to_witness (suc (suc (suc (suc (suc (suc (suc zero))))))) N11 refl
  witness118 : NatNeqWitness N11 (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
  witness118 = natEqFalse_to_witness (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) N11 refl
  witness119 : NatNeqWitness N11 (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
  witness119 = natEqFalse_to_witness (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) N11 refl
  witness1110 : NatNeqWitness N11 (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
  witness1110 = natEqFalse_to_witness (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) N11 refl

------------------------------------------------------------------------
-- axBranch11 evaluation.
-- axBranch11 = C pi (constN tag_imp)
--              (C pi get_extra_Fst
--                (C pi (constN tag_imp)
--                  (C pi get_extra_Snd get_extra_Fst)))

axBranch11_value :
  (input : Term) ->
  Deriv (eqF (ap1 axBranch11 input) (outputRHS (ap1 get_ax_extra input)))
axBranch11_value input =
  let GE : Term
      GE = ap1 get_ax_extra input

      get_eF_eq :
        Deriv (eqF (ap1 get_extra_Fst input) (ap1 Fst GE))
      get_eF_eq = compose1U_eq Fst get_ax_extra input

      get_eS_eq :
        Deriv (eqF (ap1 get_extra_Snd input) (ap1 Snd GE))
      get_eS_eq = compose1U_eq Snd get_ax_extra input

      -- C pi get_extra_Snd get_extra_Fst input = pi (Snd GE) (Fst GE).
      pi_SF :
        Deriv (eqF (ap1 (C pi get_extra_Snd get_extra_Fst) input)
                    (ap2 pi (ap1 Snd GE) (ap1 Fst GE)))
      pi_SF =
        ruleTrans (ax_C pi get_extra_Snd get_extra_Fst input)
          (ruleTrans (congL pi (ap1 get_extra_Fst input) get_eS_eq)
                     (congR pi (ap1 Snd GE) get_eF_eq))

      -- C pi (constN tag_imp) (C pi get_extra_Snd get_extra_Fst).
      inner_imp :
        Deriv (eqF (ap1 (C pi (constN tag_imp) (C pi get_extra_Snd get_extra_Fst)) input)
                    (ap2 pi (natCode tag_imp) (ap2 pi (ap1 Snd GE) (ap1 Fst GE))))
      inner_imp =
        ruleTrans (ax_C pi (constN tag_imp) (C pi get_extra_Snd get_extra_Fst) input)
          (ruleTrans (congL pi _ (constN_eq tag_imp input))
                     (congR pi (natCode tag_imp) pi_SF))

      -- C pi get_extra_Fst <inner_imp>.
      mid :
        Deriv (eqF (ap1 (C pi get_extra_Fst
                              (C pi (constN tag_imp)
                                    (C pi get_extra_Snd get_extra_Fst))) input)
                    (ap2 pi (ap1 Fst GE)
                            (ap2 pi (natCode tag_imp) (ap2 pi (ap1 Snd GE) (ap1 Fst GE)))))
      mid =
        ruleTrans (ax_C pi get_extra_Fst
                           (C pi (constN tag_imp) (C pi get_extra_Snd get_extra_Fst)) input)
          (ruleTrans (congL pi _ get_eF_eq) (congR pi (ap1 Fst GE) inner_imp))

  in ruleTrans (ax_C pi (constN tag_imp)
                       (C pi get_extra_Fst
                             (C pi (constN tag_imp) (C pi get_extra_Snd get_extra_Fst))) input)
       (ruleTrans (congL pi _ (constN_eq tag_imp input))
                  (congR pi (natCode tag_imp) mid))

------------------------------------------------------------------------
thmT_at_axN11 :
  (extra : Term) ->
  Deriv (eqF (ap1 thmT (ap2 pi (natCode tag_ax) (ap2 pi (natCode N11) extra)))
              (outputRHS extra))
thmT_at_axN11 extra =
  let input : Term
      input = ap2 pi (natCode tag_ax) (ap2 pi (natCode N11) extra)
      Y_body : Term
      Y_body = ap2 pi (natCode N11) extra
      A_outer : Term
      A_outer = O
      P_outer : Term
      P_outer = pi_succ_outer A_outer Y_body
      prev : Term
      prev = ap2 (cov_spec baseValue_thmT stepFun_thmT) O P_outer
      stateP : Term
      stateP = ap2 pi P_outer (ap1 Snd prev)

      input_eq_sP_outer = pi_at_succ A_outer Y_body
      chain_to_stepBody = thmT_at_pi_succ_to_stepBody input P_outer input_eq_sP_outer

      get_tag_eq_Fst_sP = get_tag_at_pi P_outer (ap1 Snd prev)
      Fst_input = axFst (natCode tag_ax) Y_body
      Fst_sP_to_Fst_input = cong1 Fst (ruleSym input_eq_sP_outer)
      get_tag_value :
        Deriv (eqF (ap1 get_tag stateP) (natCode tag_ax))
      get_tag_value = ruleTrans get_tag_eq_Fst_sP
                        (ruleTrans Fst_sP_to_Fst_input Fst_input)

      isAx_value = isAx_at_natCodeAx_sO stateP get_tag_value
      stepBody_to_axBranch = stepBody_thmT_to_ax_branch stateP isAx_value

      get_ax_index_eq = get_ax_index_at_pi P_outer (ap1 Snd prev)
      Snd_sP_eq = cong1 Snd (ruleSym input_eq_sP_outer)
      Snd_input_eq_Yb = axSnd (natCode tag_ax) Y_body
      Snd_sP_to_Y = ruleTrans Snd_sP_eq Snd_input_eq_Yb
      Fst_Y = axFst (natCode N11) extra

      get_ax_index_value :
        Deriv (eqF (ap1 get_ax_index stateP) (natCode N11))
      get_ax_index_value =
        ruleTrans get_ax_index_eq
          (ruleTrans (cong1 Fst Snd_sP_to_Y) Fst_Y)

      get_ax_extra_eq = get_ax_extra_at_pi P_outer (ap1 Snd prev)
      Snd_Y = axSnd (natCode N11) extra
      get_ax_extra_value :
        Deriv (eqF (ap1 get_ax_extra stateP) extra)
      get_ax_extra_value =
        ruleTrans get_ax_extra_eq
          (ruleTrans (cong1 Snd Snd_sP_to_Y) Snd_Y)

      isAx0_O = isAxOf_at_neq_O zero N11 witness110 stateP get_ax_index_value
      isAx1_O = isAxOf_at_neq_O (suc zero) N11 witness111 stateP get_ax_index_value
      isAx2_O = isAxOf_at_neq_O (suc (suc zero)) N11 witness112 stateP get_ax_index_value
      isAx3_O = isAxOf_at_neq_O (suc (suc (suc zero))) N11 witness113 stateP get_ax_index_value
      isAx4_O = isAxOf_at_neq_O (suc (suc (suc (suc zero)))) N11 witness114 stateP get_ax_index_value
      isAx5_O = isAxOf_at_neq_O (suc (suc (suc (suc (suc zero))))) N11 witness115 stateP get_ax_index_value
      isAx6_O = isAxOf_at_neq_O (suc (suc (suc (suc (suc (suc zero)))))) N11 witness116 stateP get_ax_index_value
      isAx7_O = isAxOf_at_neq_O (suc (suc (suc (suc (suc (suc (suc zero))))))) N11 witness117 stateP get_ax_index_value
      isAx8_O = isAxOf_at_neq_O (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) N11 witness118 stateP get_ax_index_value
      isAx9_O = isAxOf_at_neq_O (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) N11 witness119 stateP get_ax_index_value
      isAx10_O = isAxOf_at_neq_O (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) N11 witness1110 stateP get_ax_index_value
      isAx11_sO = isAxOf_at_eq_sO N11 stateP get_ax_index_value

      d0 = skipAt0 stateP isAx0_O
      d1 = skipAt1 stateP isAx1_O
      d2 = skipAt2 stateP isAx2_O
      d3 = skipAt3 stateP isAx3_O
      d4 = skipAt4 stateP isAx4_O
      d5 = skipAt5 stateP isAx5_O
      d6 = skipAt6 stateP isAx6_O
      d7 = skipAt7 stateP isAx7_O
      d8 = skipAt8 stateP isAx8_O
      d9 = skipAt9 stateP isAx9_O
      d10 = skipAt10 stateP isAx10_O
      d11 = landAt11 stateP isAx11_sO
      r10 = ruleTrans d10 d11
      r9 = ruleTrans d9 r10
      r8 = ruleTrans d8 r9
      r7 = ruleTrans d7 r8
      r6 = ruleTrans d6 r7
      r5 = ruleTrans d5 r6
      r4 = ruleTrans d4 r5
      r3 = ruleTrans d3 r4
      r2 = ruleTrans d2 r3
      r1 = ruleTrans d1 r2
      axBranch_to_branch11 = ruleTrans d0 r1

      axBranch11_eval = axBranch11_value stateP

      ge_eq = get_ax_extra_value
      GE = ap1 get_ax_extra stateP

      Fst_subst : Deriv (eqF (ap1 Fst GE) (ap1 Fst extra))
      Fst_subst = cong1 Fst ge_eq

      Snd_subst : Deriv (eqF (ap1 Snd GE) (ap1 Snd extra))
      Snd_subst = cong1 Snd ge_eq

      -- pi (Snd GE) (Fst GE) -> pi (Snd extra) (Fst extra).
      pi_SF_subst :
        Deriv (eqF (ap2 pi (ap1 Snd GE) (ap1 Fst GE))
                    (ap2 pi (ap1 Snd extra) (ap1 Fst extra)))
      pi_SF_subst =
        ruleTrans (congL pi (ap1 Fst GE) Snd_subst)
                  (congR pi (ap1 Snd extra) Fst_subst)

      inner_imp_subst :
        Deriv (eqF (ap2 pi (natCode tag_imp) (ap2 pi (ap1 Snd GE) (ap1 Fst GE)))
                    (ap2 pi (natCode tag_imp) (ap2 pi (ap1 Snd extra) (ap1 Fst extra))))
      inner_imp_subst = congR pi (natCode tag_imp) pi_SF_subst

      mid_subst :
        Deriv (eqF (ap2 pi (ap1 Fst GE)
                            (ap2 pi (natCode tag_imp) (ap2 pi (ap1 Snd GE) (ap1 Fst GE))))
                    (ap2 pi (ap1 Fst extra)
                            (ap2 pi (natCode tag_imp) (ap2 pi (ap1 Snd extra) (ap1 Fst extra)))))
      mid_subst =
        ruleTrans (congL pi _ Fst_subst) (congR pi (ap1 Fst extra) inner_imp_subst)

      final_subst :
        Deriv (eqF (outputRHS GE) (outputRHS extra))
      final_subst = congR pi (natCode tag_imp) mid_subst

      chain_to_axBranch = ruleTrans chain_to_stepBody stepBody_to_axBranch
      chain_to_branch11 = ruleTrans chain_to_axBranch axBranch_to_branch11
      chain_to_eval = ruleTrans chain_to_branch11 axBranch11_eval
  in ruleTrans chain_to_eval final_subst
