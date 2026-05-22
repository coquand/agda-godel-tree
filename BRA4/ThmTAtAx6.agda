{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.ThmTAtAx6 -- axiom 6 :  v0 = v1  >  g(v0, v2) = g(v1, v2)  ,  extra = codeFun2 g .

module BRA4.ThmTAtAx6 where

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
  N6 : Nat
  N6 = suc (suc (suc (suc (suc (suc zero)))))

  cV0 : Term
  cV0 = ap2 pi (natCode tag_var) (natCode zero)

  cV1 : Term
  cV1 = ap2 pi (natCode tag_var) (natCode (suc zero))

  cV2 : Term
  cV2 = ap2 pi (natCode tag_var) (natCode (suc (suc zero)))

  cEq01 : Term
  cEq01 = ap2 pi (natCode tag_eq) (ap2 pi cV0 cV1)

  -- code(ap2 g vi vj) = pi tag_ap2 (pi gT (pi vi vj))
  cAp2_g_at : Term -> Term -> Term -> Term
  cAp2_g_at gT viT vjT = ap2 pi (natCode tag_ap2) (ap2 pi gT (ap2 pi viT vjT))

  outputRHS : Term -> Term
  outputRHS gT =
    ap2 pi (natCode tag_imp)
      (ap2 pi cEq01
        (ap2 pi (natCode tag_eq)
          (ap2 pi (cAp2_g_at gT cV0 cV2) (cAp2_g_at gT cV1 cV2))))

  witness60 : NatNeqWitness N6 zero
  witness60 = natEqFalse_to_witness zero N6 refl

  witness61 : NatNeqWitness N6 (suc zero)
  witness61 = natEqFalse_to_witness (suc zero) N6 refl

  witness62 : NatNeqWitness N6 (suc (suc zero))
  witness62 = natEqFalse_to_witness (suc (suc zero)) N6 refl

  witness63 : NatNeqWitness N6 (suc (suc (suc zero)))
  witness63 = natEqFalse_to_witness (suc (suc (suc zero))) N6 refl

  witness64 : NatNeqWitness N6 (suc (suc (suc (suc zero))))
  witness64 = natEqFalse_to_witness (suc (suc (suc (suc zero)))) N6 refl

  witness65 : NatNeqWitness N6 (suc (suc (suc (suc (suc zero)))))
  witness65 = natEqFalse_to_witness (suc (suc (suc (suc (suc zero))))) N6 refl

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
          (ruleTrans (congL pi (ap1 V1_F1 input) V0_eval)
                     (congR pi cV0 V1_eval))
  in ruleTrans (ax_C pi (constN tag_eq) (C pi V0_F1 V1_F1) input)
       (ruleTrans (congL pi (ap1 (C pi V0_F1 V1_F1) input) (constN_eq tag_eq input))
                  (congR pi (natCode tag_eq) pi_VV))

------------------------------------------------------------------------
-- axBranch6 evaluation.
-- axBranch6 = C pi (constN tag_imp)
--             (C pi codeEq_V0_V1
--               (C pi (constN tag_eq)
--                 (C pi (C pi (constN tag_ap2) (C pi get_ax_extra (C pi V0_F1 V2_F1)))
--                       (C pi (constN tag_ap2) (C pi get_ax_extra (C pi V1_F1 V2_F1))))))

axBranch6_value :
  (input : Term) ->
  Deriv (eqF (ap1 axBranch6 input) (outputRHS (ap1 get_ax_extra input)))
axBranch6_value input =
  let V0_eval = V0_F1_value input
      V1_eval = V1_F1_value input
      V2_eval = V2_F1_value input
      eq01_eval = codeEq_V0_V1_value input
      GE : Term
      GE = ap1 get_ax_extra input

      -- C pi V0_F1 V2_F1 input = pi cV0 cV2.
      piV0V2 :
        Deriv (eqF (ap1 (C pi V0_F1 V2_F1) input) (ap2 pi cV0 cV2))
      piV0V2 =
        ruleTrans (ax_C pi V0_F1 V2_F1 input)
          (ruleTrans (congL pi (ap1 V2_F1 input) V0_eval) (congR pi cV0 V2_eval))

      piV1V2 :
        Deriv (eqF (ap1 (C pi V1_F1 V2_F1) input) (ap2 pi cV1 cV2))
      piV1V2 =
        ruleTrans (ax_C pi V1_F1 V2_F1 input)
          (ruleTrans (congL pi (ap1 V2_F1 input) V1_eval) (congR pi cV1 V2_eval))

      -- C pi get_ax_extra (C pi V0_F1 V2_F1) input = pi GE (pi cV0 cV2).
      gV0V2 :
        Deriv (eqF (ap1 (C pi get_ax_extra (C pi V0_F1 V2_F1)) input)
                    (ap2 pi GE (ap2 pi cV0 cV2)))
      gV0V2 =
        ruleTrans (ax_C pi get_ax_extra (C pi V0_F1 V2_F1) input)
          (congR pi GE piV0V2)

      gV1V2 :
        Deriv (eqF (ap1 (C pi get_ax_extra (C pi V1_F1 V2_F1)) input)
                    (ap2 pi GE (ap2 pi cV1 cV2)))
      gV1V2 =
        ruleTrans (ax_C pi get_ax_extra (C pi V1_F1 V2_F1) input)
          (congR pi GE piV1V2)

      -- C pi (constN tag_ap2) (C pi get_ax_extra (...)).
      ap2V0V2 :
        Deriv (eqF (ap1 (C pi (constN tag_ap2) (C pi get_ax_extra (C pi V0_F1 V2_F1))) input)
                    (cAp2_g_at GE cV0 cV2))
      ap2V0V2 =
        ruleTrans (ax_C pi (constN tag_ap2) (C pi get_ax_extra (C pi V0_F1 V2_F1)) input)
          (ruleTrans (congL pi _ (constN_eq tag_ap2 input))
                     (congR pi (natCode tag_ap2) gV0V2))

      ap2V1V2 :
        Deriv (eqF (ap1 (C pi (constN tag_ap2) (C pi get_ax_extra (C pi V1_F1 V2_F1))) input)
                    (cAp2_g_at GE cV1 cV2))
      ap2V1V2 =
        ruleTrans (ax_C pi (constN tag_ap2) (C pi get_ax_extra (C pi V1_F1 V2_F1)) input)
          (ruleTrans (congL pi _ (constN_eq tag_ap2 input))
                     (congR pi (natCode tag_ap2) gV1V2))

      -- Pair the two C pi <ap2V0V2> <ap2V1V2>.
      pair_ap2 :
        Deriv (eqF (ap1 (C pi (C pi (constN tag_ap2) (C pi get_ax_extra (C pi V0_F1 V2_F1)))
                              (C pi (constN tag_ap2) (C pi get_ax_extra (C pi V1_F1 V2_F1)))) input)
                    (ap2 pi (cAp2_g_at GE cV0 cV2) (cAp2_g_at GE cV1 cV2)))
      pair_ap2 =
        ruleTrans (ax_C pi (C pi (constN tag_ap2) (C pi get_ax_extra (C pi V0_F1 V2_F1)))
                            (C pi (constN tag_ap2) (C pi get_ax_extra (C pi V1_F1 V2_F1))) input)
          (ruleTrans (congL pi _ ap2V0V2) (congR pi (cAp2_g_at GE cV0 cV2) ap2V1V2))

      -- C pi (constN tag_eq) <pair>.
      eq_pair :
        Deriv (eqF (ap1 (C pi (constN tag_eq)
                              (C pi (C pi (constN tag_ap2) (C pi get_ax_extra (C pi V0_F1 V2_F1)))
                                    (C pi (constN tag_ap2) (C pi get_ax_extra (C pi V1_F1 V2_F1))))) input)
                    (ap2 pi (natCode tag_eq)
                            (ap2 pi (cAp2_g_at GE cV0 cV2) (cAp2_g_at GE cV1 cV2))))
      eq_pair =
        ruleTrans (ax_C pi (constN tag_eq)
                           (C pi (C pi (constN tag_ap2) (C pi get_ax_extra (C pi V0_F1 V2_F1)))
                                 (C pi (constN tag_ap2) (C pi get_ax_extra (C pi V1_F1 V2_F1)))) input)
          (ruleTrans (congL pi _ (constN_eq tag_eq input)) (congR pi (natCode tag_eq) pair_ap2))

      -- C pi codeEq_V0_V1 <eq_pair>.
      pair_outer :
        Deriv (eqF (ap1 (C pi codeEq_V0_V1
                              (C pi (constN tag_eq)
                                    (C pi (C pi (constN tag_ap2) (C pi get_ax_extra (C pi V0_F1 V2_F1)))
                                          (C pi (constN tag_ap2) (C pi get_ax_extra (C pi V1_F1 V2_F1)))))) input)
                    (ap2 pi cEq01
                            (ap2 pi (natCode tag_eq)
                                    (ap2 pi (cAp2_g_at GE cV0 cV2) (cAp2_g_at GE cV1 cV2)))))
      pair_outer =
        ruleTrans (ax_C pi codeEq_V0_V1
                           (C pi (constN tag_eq)
                                 (C pi (C pi (constN tag_ap2) (C pi get_ax_extra (C pi V0_F1 V2_F1)))
                                       (C pi (constN tag_ap2) (C pi get_ax_extra (C pi V1_F1 V2_F1))))) input)
          (ruleTrans (congL pi _ eq01_eval) (congR pi cEq01 eq_pair))

  in ruleTrans (ax_C pi (constN tag_imp)
                       (C pi codeEq_V0_V1
                             (C pi (constN tag_eq)
                                   (C pi (C pi (constN tag_ap2) (C pi get_ax_extra (C pi V0_F1 V2_F1)))
                                         (C pi (constN tag_ap2) (C pi get_ax_extra (C pi V1_F1 V2_F1)))))) input)
       (ruleTrans (congL pi _ (constN_eq tag_imp input))
                  (congR pi (natCode tag_imp) pair_outer))

------------------------------------------------------------------------
thmT_at_axN6 :
  (extra : Term) ->
  Deriv (eqF (ap1 thmT (ap2 pi (natCode tag_ax) (ap2 pi (natCode N6) extra)))
              (outputRHS extra))
thmT_at_axN6 extra =
  let input : Term
      input = ap2 pi (natCode tag_ax) (ap2 pi (natCode N6) extra)
      Y_body : Term
      Y_body = ap2 pi (natCode N6) extra
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
      Fst_Y = axFst (natCode N6) extra

      get_ax_index_value :
        Deriv (eqF (ap1 get_ax_index stateP) (natCode N6))
      get_ax_index_value =
        ruleTrans get_ax_index_eq
          (ruleTrans (cong1 Fst Snd_sP_to_Y) Fst_Y)

      get_ax_extra_eq = get_ax_extra_at_pi P_outer (ap1 Snd prev)
      Snd_Y = axSnd (natCode N6) extra
      get_ax_extra_value :
        Deriv (eqF (ap1 get_ax_extra stateP) extra)
      get_ax_extra_value =
        ruleTrans get_ax_extra_eq
          (ruleTrans (cong1 Snd Snd_sP_to_Y) Snd_Y)

      isAx0_O = isAxOf_at_neq_O zero N6 witness60 stateP get_ax_index_value
      isAx1_O = isAxOf_at_neq_O (suc zero) N6 witness61 stateP get_ax_index_value
      isAx2_O = isAxOf_at_neq_O (suc (suc zero)) N6 witness62 stateP get_ax_index_value
      isAx3_O = isAxOf_at_neq_O (suc (suc (suc zero))) N6 witness63 stateP get_ax_index_value
      isAx4_O = isAxOf_at_neq_O (suc (suc (suc (suc zero)))) N6 witness64 stateP get_ax_index_value
      isAx5_O = isAxOf_at_neq_O (suc (suc (suc (suc (suc zero))))) N6 witness65 stateP get_ax_index_value
      isAx6_sO = isAxOf_at_eq_sO N6 stateP get_ax_index_value

      axBranch_to_branch6 =
        ruleTrans (skipAt0 stateP isAx0_O)
          (ruleTrans (skipAt1 stateP isAx1_O)
            (ruleTrans (skipAt2 stateP isAx2_O)
              (ruleTrans (skipAt3 stateP isAx3_O)
                (ruleTrans (skipAt4 stateP isAx4_O)
                  (ruleTrans (skipAt5 stateP isAx5_O)
                             (landAt6 stateP isAx6_sO))))))

      axBranch6_eval = axBranch6_value stateP

      ge_eq = get_ax_extra_value
      GE = ap1 get_ax_extra stateP

      ap2_v0v2_subst :
        Deriv (eqF (cAp2_g_at GE cV0 cV2) (cAp2_g_at extra cV0 cV2))
      ap2_v0v2_subst = congR pi (natCode tag_ap2) (congL pi (ap2 pi cV0 cV2) ge_eq)

      ap2_v1v2_subst :
        Deriv (eqF (cAp2_g_at GE cV1 cV2) (cAp2_g_at extra cV1 cV2))
      ap2_v1v2_subst = congR pi (natCode tag_ap2) (congL pi (ap2 pi cV1 cV2) ge_eq)

      pair_subst :
        Deriv (eqF (ap2 pi (cAp2_g_at GE cV0 cV2) (cAp2_g_at GE cV1 cV2))
                    (ap2 pi (cAp2_g_at extra cV0 cV2) (cAp2_g_at extra cV1 cV2)))
      pair_subst =
        ruleTrans (congL pi (cAp2_g_at GE cV1 cV2) ap2_v0v2_subst)
                  (congR pi (cAp2_g_at extra cV0 cV2) ap2_v1v2_subst)

      eq_subst :
        Deriv (eqF (ap2 pi (natCode tag_eq)
                            (ap2 pi (cAp2_g_at GE cV0 cV2) (cAp2_g_at GE cV1 cV2)))
                    (ap2 pi (natCode tag_eq)
                            (ap2 pi (cAp2_g_at extra cV0 cV2) (cAp2_g_at extra cV1 cV2))))
      eq_subst = congR pi (natCode tag_eq) pair_subst

      outer_subst :
        Deriv (eqF (ap2 pi cEq01
                           (ap2 pi (natCode tag_eq)
                                   (ap2 pi (cAp2_g_at GE cV0 cV2) (cAp2_g_at GE cV1 cV2))))
                    (ap2 pi cEq01
                           (ap2 pi (natCode tag_eq)
                                   (ap2 pi (cAp2_g_at extra cV0 cV2) (cAp2_g_at extra cV1 cV2)))))
      outer_subst = congR pi cEq01 eq_subst

      final_subst :
        Deriv (eqF (outputRHS GE) (outputRHS extra))
      final_subst = congR pi (natCode tag_imp) outer_subst

      chain_to_axBranch = ruleTrans chain_to_stepBody stepBody_to_axBranch
      chain_to_branch6 = ruleTrans chain_to_axBranch axBranch_to_branch6
      chain_to_eval = ruleTrans chain_to_branch6 axBranch6_eval
  in ruleTrans chain_to_eval final_subst
