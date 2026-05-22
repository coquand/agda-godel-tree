{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.ThmTAtAx7 -- axiom 7 :  v0 = v1  >  g(v2, v0) = g(v2, v1) .  extra = codeFun2 g.

module BRA4.ThmTAtAx7 where

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
  N7 : Nat
  N7 = suc (suc (suc (suc (suc (suc (suc zero))))))

  cV0 cV1 cV2 cEq01 : Term
  cV0 = ap2 pi (natCode tag_var) (natCode zero)
  cV1 = ap2 pi (natCode tag_var) (natCode (suc zero))
  cV2 = ap2 pi (natCode tag_var) (natCode (suc (suc zero)))
  cEq01 = ap2 pi (natCode tag_eq) (ap2 pi cV0 cV1)

  cAp2_g_at : Term -> Term -> Term -> Term
  cAp2_g_at gT viT vjT = ap2 pi (natCode tag_ap2) (ap2 pi gT (ap2 pi viT vjT))

  -- ax7's consequent uses g(v2, v0) and g(v2, v1).
  outputRHS : Term -> Term
  outputRHS gT =
    ap2 pi (natCode tag_imp)
      (ap2 pi cEq01
        (ap2 pi (natCode tag_eq)
          (ap2 pi (cAp2_g_at gT cV2 cV0) (cAp2_g_at gT cV2 cV1))))

  witness70 : NatNeqWitness N7 zero
  witness70 = natEqFalse_to_witness zero N7 refl
  witness71 : NatNeqWitness N7 (suc zero)
  witness71 = natEqFalse_to_witness (suc zero) N7 refl
  witness72 : NatNeqWitness N7 (suc (suc zero))
  witness72 = natEqFalse_to_witness (suc (suc zero)) N7 refl
  witness73 : NatNeqWitness N7 (suc (suc (suc zero)))
  witness73 = natEqFalse_to_witness (suc (suc (suc zero))) N7 refl
  witness74 : NatNeqWitness N7 (suc (suc (suc (suc zero))))
  witness74 = natEqFalse_to_witness (suc (suc (suc (suc zero)))) N7 refl
  witness75 : NatNeqWitness N7 (suc (suc (suc (suc (suc zero)))))
  witness75 = natEqFalse_to_witness (suc (suc (suc (suc (suc zero))))) N7 refl
  witness76 : NatNeqWitness N7 (suc (suc (suc (suc (suc (suc zero))))))
  witness76 = natEqFalse_to_witness (suc (suc (suc (suc (suc (suc zero)))))) N7 refl

V0_F1_value :
  (input : Term) -> Deriv (eqF (ap1 V0_F1 input) cV0)
V0_F1_value input =
  ruleTrans (ax_C pi (constN tag_var) (constN zero) input)
    (ruleTrans (congL pi (ap1 (constN zero) input) (constN_eq tag_var input))
               (congR pi (natCode tag_var) (constN_eq zero input)))

V1_F1_value :
  (input : Term) -> Deriv (eqF (ap1 V1_F1 input) cV1)
V1_F1_value input =
  ruleTrans (ax_C pi (constN tag_var) (constN (suc zero)) input)
    (ruleTrans (congL pi (ap1 (constN (suc zero)) input) (constN_eq tag_var input))
               (congR pi (natCode tag_var) (constN_eq (suc zero) input)))

V2_F1_value :
  (input : Term) -> Deriv (eqF (ap1 V2_F1 input) cV2)
V2_F1_value input =
  ruleTrans (ax_C pi (constN tag_var) (constN (suc (suc zero))) input)
    (ruleTrans (congL pi (ap1 (constN (suc (suc zero))) input) (constN_eq tag_var input))
               (congR pi (natCode tag_var) (constN_eq (suc (suc zero)) input)))

codeEq_V0_V1_value :
  (input : Term) -> Deriv (eqF (ap1 codeEq_V0_V1 input) cEq01)
codeEq_V0_V1_value input =
  let V0_eval = V0_F1_value input
      V1_eval = V1_F1_value input
      pi_VV =
        ruleTrans (ax_C pi V0_F1 V1_F1 input)
          (ruleTrans (congL pi (ap1 V1_F1 input) V0_eval) (congR pi cV0 V1_eval))
  in ruleTrans (ax_C pi (constN tag_eq) (C pi V0_F1 V1_F1) input)
       (ruleTrans (congL pi (ap1 (C pi V0_F1 V1_F1) input) (constN_eq tag_eq input))
                  (congR pi (natCode tag_eq) pi_VV))

------------------------------------------------------------------------
axBranch7_value :
  (input : Term) ->
  Deriv (eqF (ap1 axBranch7 input) (outputRHS (ap1 get_ax_extra input)))
axBranch7_value input =
  let V0_eval = V0_F1_value input
      V1_eval = V1_F1_value input
      V2_eval = V2_F1_value input
      eq01_eval = codeEq_V0_V1_value input
      GE : Term
      GE = ap1 get_ax_extra input

      piV2V0 :
        Deriv (eqF (ap1 (C pi V2_F1 V0_F1) input) (ap2 pi cV2 cV0))
      piV2V0 =
        ruleTrans (ax_C pi V2_F1 V0_F1 input)
          (ruleTrans (congL pi (ap1 V0_F1 input) V2_eval) (congR pi cV2 V0_eval))

      piV2V1 :
        Deriv (eqF (ap1 (C pi V2_F1 V1_F1) input) (ap2 pi cV2 cV1))
      piV2V1 =
        ruleTrans (ax_C pi V2_F1 V1_F1 input)
          (ruleTrans (congL pi (ap1 V1_F1 input) V2_eval) (congR pi cV2 V1_eval))

      gV2V0 :
        Deriv (eqF (ap1 (C pi get_ax_extra (C pi V2_F1 V0_F1)) input)
                    (ap2 pi GE (ap2 pi cV2 cV0)))
      gV2V0 = ruleTrans (ax_C pi get_ax_extra (C pi V2_F1 V0_F1) input) (congR pi GE piV2V0)

      gV2V1 :
        Deriv (eqF (ap1 (C pi get_ax_extra (C pi V2_F1 V1_F1)) input)
                    (ap2 pi GE (ap2 pi cV2 cV1)))
      gV2V1 = ruleTrans (ax_C pi get_ax_extra (C pi V2_F1 V1_F1) input) (congR pi GE piV2V1)

      ap2V2V0 :
        Deriv (eqF (ap1 (C pi (constN tag_ap2) (C pi get_ax_extra (C pi V2_F1 V0_F1))) input)
                    (cAp2_g_at GE cV2 cV0))
      ap2V2V0 =
        ruleTrans (ax_C pi (constN tag_ap2) (C pi get_ax_extra (C pi V2_F1 V0_F1)) input)
          (ruleTrans (congL pi _ (constN_eq tag_ap2 input))
                     (congR pi (natCode tag_ap2) gV2V0))

      ap2V2V1 :
        Deriv (eqF (ap1 (C pi (constN tag_ap2) (C pi get_ax_extra (C pi V2_F1 V1_F1))) input)
                    (cAp2_g_at GE cV2 cV1))
      ap2V2V1 =
        ruleTrans (ax_C pi (constN tag_ap2) (C pi get_ax_extra (C pi V2_F1 V1_F1)) input)
          (ruleTrans (congL pi _ (constN_eq tag_ap2 input))
                     (congR pi (natCode tag_ap2) gV2V1))

      pair_ap2 :
        Deriv (eqF (ap1 (C pi (C pi (constN tag_ap2) (C pi get_ax_extra (C pi V2_F1 V0_F1)))
                              (C pi (constN tag_ap2) (C pi get_ax_extra (C pi V2_F1 V1_F1)))) input)
                    (ap2 pi (cAp2_g_at GE cV2 cV0) (cAp2_g_at GE cV2 cV1)))
      pair_ap2 =
        ruleTrans (ax_C pi (C pi (constN tag_ap2) (C pi get_ax_extra (C pi V2_F1 V0_F1)))
                            (C pi (constN tag_ap2) (C pi get_ax_extra (C pi V2_F1 V1_F1))) input)
          (ruleTrans (congL pi _ ap2V2V0) (congR pi (cAp2_g_at GE cV2 cV0) ap2V2V1))

      eq_pair :
        Deriv (eqF (ap1 (C pi (constN tag_eq)
                              (C pi (C pi (constN tag_ap2) (C pi get_ax_extra (C pi V2_F1 V0_F1)))
                                    (C pi (constN tag_ap2) (C pi get_ax_extra (C pi V2_F1 V1_F1))))) input)
                    (ap2 pi (natCode tag_eq)
                            (ap2 pi (cAp2_g_at GE cV2 cV0) (cAp2_g_at GE cV2 cV1))))
      eq_pair =
        ruleTrans (ax_C pi (constN tag_eq)
                           (C pi (C pi (constN tag_ap2) (C pi get_ax_extra (C pi V2_F1 V0_F1)))
                                 (C pi (constN tag_ap2) (C pi get_ax_extra (C pi V2_F1 V1_F1)))) input)
          (ruleTrans (congL pi _ (constN_eq tag_eq input))
                     (congR pi (natCode tag_eq) pair_ap2))

      pair_outer :
        Deriv (eqF (ap1 (C pi codeEq_V0_V1
                              (C pi (constN tag_eq)
                                    (C pi (C pi (constN tag_ap2) (C pi get_ax_extra (C pi V2_F1 V0_F1)))
                                          (C pi (constN tag_ap2) (C pi get_ax_extra (C pi V2_F1 V1_F1)))))) input)
                    (ap2 pi cEq01
                            (ap2 pi (natCode tag_eq)
                                    (ap2 pi (cAp2_g_at GE cV2 cV0) (cAp2_g_at GE cV2 cV1)))))
      pair_outer =
        ruleTrans (ax_C pi codeEq_V0_V1
                           (C pi (constN tag_eq)
                                 (C pi (C pi (constN tag_ap2) (C pi get_ax_extra (C pi V2_F1 V0_F1)))
                                       (C pi (constN tag_ap2) (C pi get_ax_extra (C pi V2_F1 V1_F1))))) input)
          (ruleTrans (congL pi _ eq01_eval) (congR pi cEq01 eq_pair))

  in ruleTrans (ax_C pi (constN tag_imp)
                       (C pi codeEq_V0_V1
                             (C pi (constN tag_eq)
                                   (C pi (C pi (constN tag_ap2) (C pi get_ax_extra (C pi V2_F1 V0_F1)))
                                         (C pi (constN tag_ap2) (C pi get_ax_extra (C pi V2_F1 V1_F1)))))) input)
       (ruleTrans (congL pi _ (constN_eq tag_imp input))
                  (congR pi (natCode tag_imp) pair_outer))

------------------------------------------------------------------------
thmT_at_axN7 :
  (extra : Term) ->
  Deriv (eqF (ap1 thmT (ap2 pi (natCode tag_ax) (ap2 pi (natCode N7) extra)))
              (outputRHS extra))
thmT_at_axN7 extra =
  let input : Term
      input = ap2 pi (natCode tag_ax) (ap2 pi (natCode N7) extra)
      Y_body : Term
      Y_body = ap2 pi (natCode N7) extra
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
      Fst_Y = axFst (natCode N7) extra

      get_ax_index_value :
        Deriv (eqF (ap1 get_ax_index stateP) (natCode N7))
      get_ax_index_value =
        ruleTrans get_ax_index_eq
          (ruleTrans (cong1 Fst Snd_sP_to_Y) Fst_Y)

      get_ax_extra_eq = get_ax_extra_at_pi P_outer (ap1 Snd prev)
      Snd_Y = axSnd (natCode N7) extra
      get_ax_extra_value :
        Deriv (eqF (ap1 get_ax_extra stateP) extra)
      get_ax_extra_value =
        ruleTrans get_ax_extra_eq
          (ruleTrans (cong1 Snd Snd_sP_to_Y) Snd_Y)

      isAx0_O = isAxOf_at_neq_O zero N7 witness70 stateP get_ax_index_value
      isAx1_O = isAxOf_at_neq_O (suc zero) N7 witness71 stateP get_ax_index_value
      isAx2_O = isAxOf_at_neq_O (suc (suc zero)) N7 witness72 stateP get_ax_index_value
      isAx3_O = isAxOf_at_neq_O (suc (suc (suc zero))) N7 witness73 stateP get_ax_index_value
      isAx4_O = isAxOf_at_neq_O (suc (suc (suc (suc zero)))) N7 witness74 stateP get_ax_index_value
      isAx5_O = isAxOf_at_neq_O (suc (suc (suc (suc (suc zero))))) N7 witness75 stateP get_ax_index_value
      isAx6_O = isAxOf_at_neq_O (suc (suc (suc (suc (suc (suc zero)))))) N7 witness76 stateP get_ax_index_value
      isAx7_sO = isAxOf_at_eq_sO N7 stateP get_ax_index_value

      axBranch_to_branch7 =
        ruleTrans (skipAt0 stateP isAx0_O)
          (ruleTrans (skipAt1 stateP isAx1_O)
            (ruleTrans (skipAt2 stateP isAx2_O)
              (ruleTrans (skipAt3 stateP isAx3_O)
                (ruleTrans (skipAt4 stateP isAx4_O)
                  (ruleTrans (skipAt5 stateP isAx5_O)
                    (ruleTrans (skipAt6 stateP isAx6_O)
                               (landAt7 stateP isAx7_sO)))))))

      axBranch7_eval = axBranch7_value stateP

      ge_eq = get_ax_extra_value
      GE = ap1 get_ax_extra stateP

      ap2_v2v0_subst :
        Deriv (eqF (cAp2_g_at GE cV2 cV0) (cAp2_g_at extra cV2 cV0))
      ap2_v2v0_subst = congR pi (natCode tag_ap2) (congL pi (ap2 pi cV2 cV0) ge_eq)

      ap2_v2v1_subst :
        Deriv (eqF (cAp2_g_at GE cV2 cV1) (cAp2_g_at extra cV2 cV1))
      ap2_v2v1_subst = congR pi (natCode tag_ap2) (congL pi (ap2 pi cV2 cV1) ge_eq)

      pair_subst :
        Deriv (eqF (ap2 pi (cAp2_g_at GE cV2 cV0) (cAp2_g_at GE cV2 cV1))
                    (ap2 pi (cAp2_g_at extra cV2 cV0) (cAp2_g_at extra cV2 cV1)))
      pair_subst =
        ruleTrans (congL pi (cAp2_g_at GE cV2 cV1) ap2_v2v0_subst)
                  (congR pi (cAp2_g_at extra cV2 cV0) ap2_v2v1_subst)

      eq_subst :
        Deriv (eqF (ap2 pi (natCode tag_eq)
                            (ap2 pi (cAp2_g_at GE cV2 cV0) (cAp2_g_at GE cV2 cV1)))
                    (ap2 pi (natCode tag_eq)
                            (ap2 pi (cAp2_g_at extra cV2 cV0) (cAp2_g_at extra cV2 cV1))))
      eq_subst = congR pi (natCode tag_eq) pair_subst

      outer_subst :
        Deriv (eqF (ap2 pi cEq01
                           (ap2 pi (natCode tag_eq)
                                   (ap2 pi (cAp2_g_at GE cV2 cV0) (cAp2_g_at GE cV2 cV1))))
                    (ap2 pi cEq01
                           (ap2 pi (natCode tag_eq)
                                   (ap2 pi (cAp2_g_at extra cV2 cV0) (cAp2_g_at extra cV2 cV1)))))
      outer_subst = congR pi cEq01 eq_subst

      final_subst :
        Deriv (eqF (outputRHS GE) (outputRHS extra))
      final_subst = congR pi (natCode tag_imp) outer_subst

      chain_to_axBranch = ruleTrans chain_to_stepBody stepBody_to_axBranch
      chain_to_branch7 = ruleTrans chain_to_axBranch axBranch_to_branch7
      chain_to_eval = ruleTrans chain_to_branch7 axBranch7_eval
  in ruleTrans chain_to_eval final_subst
