{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.ThmTAtAx5 -- axiom 5 closure :  v0 = v1  >  f(v0) = f(v1)  ,  extra = codeFun1 f .
-- Universal in arbitrary  extra : Term .

module BRA4.ThmTAtAx5 where

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

-- Term-level RHS helpers.

private
  N5 : Nat
  N5 = suc (suc (suc (suc (suc zero))))

  cV0 : Term
  cV0 = ap2 pi (natCode tag_var) (natCode zero)

  cV1 : Term
  cV1 = ap2 pi (natCode tag_var) (natCode (suc zero))

  cEq01 : Term
  cEq01 = ap2 pi (natCode tag_eq) (ap2 pi cV0 cV1)

  cAp1_f_V_at : Term -> Term -> Term
  cAp1_f_V_at fT vT = ap2 pi (natCode tag_ap1) (ap2 pi fT vT)

  -- The output RHS, parametric on the functor encoding fT.
  outputRHS : Term -> Term
  outputRHS fT =
    ap2 pi (natCode tag_imp)
      (ap2 pi cEq01
        (ap2 pi (natCode tag_eq)
          (ap2 pi (cAp1_f_V_at fT cV0) (cAp1_f_V_at fT cV1))))

  witness50 : NatNeqWitness N5 zero
  witness50 = natEqFalse_to_witness zero N5 refl

  witness51 : NatNeqWitness N5 (suc zero)
  witness51 = natEqFalse_to_witness (suc zero) N5 refl

  witness52 : NatNeqWitness N5 (suc (suc zero))
  witness52 = natEqFalse_to_witness (suc (suc zero)) N5 refl

  witness53 : NatNeqWitness N5 (suc (suc (suc zero)))
  witness53 = natEqFalse_to_witness (suc (suc (suc zero))) N5 refl

  witness54 : NatNeqWitness N5 (suc (suc (suc (suc zero))))
  witness54 = natEqFalse_to_witness (suc (suc (suc (suc zero)))) N5 refl

V0_F1_value :
  (input : Term) ->
  Deriv (eqF (ap1 V0_F1 input) cV0)
V0_F1_value input =
  let e1 = ax_C pi (constN tag_var) (constN zero) input
  in ruleTrans e1
       (ruleTrans (congL pi (ap1 (constN zero) input) (constN_eq tag_var input))
                  (congR pi (natCode tag_var) (constN_eq zero input)))

V1_F1_value :
  (input : Term) ->
  Deriv (eqF (ap1 V1_F1 input) cV1)
V1_F1_value input =
  let e1 = ax_C pi (constN tag_var) (constN (suc zero)) input
  in ruleTrans e1
       (ruleTrans (congL pi (ap1 (constN (suc zero)) input) (constN_eq tag_var input))
                  (congR pi (natCode tag_var) (constN_eq (suc zero) input)))

codeEq_V0_V1_value :
  (input : Term) ->
  Deriv (eqF (ap1 codeEq_V0_V1 input) cEq01)
codeEq_V0_V1_value input =
  let V0_eval = V0_F1_value input
      V1_eval = V1_F1_value input
      pi_VV_unfold = ax_C pi V0_F1 V1_F1 input
      pi_VV_value :
        Deriv (eqF (ap1 (C pi V0_F1 V1_F1) input) (ap2 pi cV0 cV1))
      pi_VV_value =
        ruleTrans pi_VV_unfold
          (ruleTrans (congL pi (ap1 V1_F1 input) V0_eval)
                     (congR pi cV0 V1_eval))
      outer_unfold = ax_C pi (constN tag_eq) (C pi V0_F1 V1_F1) input
  in ruleTrans outer_unfold
       (ruleTrans (congL pi (ap1 (C pi V0_F1 V1_F1) input) (constN_eq tag_eq input))
                  (congR pi (natCode tag_eq) pi_VV_value))

------------------------------------------------------------------------
-- axBranch5 evaluation, parametric on (ap1 get_ax_extra input).

axBranch5_value :
  (input : Term) ->
  Deriv (eqF (ap1 axBranch5 input) (outputRHS (ap1 get_ax_extra input)))
axBranch5_value input =
  let V0_eval = V0_F1_value input
      V1_eval = V1_F1_value input
      eq01_eval = codeEq_V0_V1_value input

      GE : Term
      GE = ap1 get_ax_extra input

      -- (C pi get_ax_extra V0_F1) input = pi GE cV0.
      pi_eV0 :
        Deriv (eqF (ap1 (C pi get_ax_extra V0_F1) input) (ap2 pi GE cV0))
      pi_eV0 =
        ruleTrans (ax_C pi get_ax_extra V0_F1 input)
                  (congR pi GE V0_eval)

      pi_eV1 :
        Deriv (eqF (ap1 (C pi get_ax_extra V1_F1) input) (ap2 pi GE cV1))
      pi_eV1 =
        ruleTrans (ax_C pi get_ax_extra V1_F1 input)
                  (congR pi GE V1_eval)

      -- (C pi (constN tag_ap1) (C pi get_ax_extra V0_F1)) input = cAp1_f_V_at GE cV0.
      ap1_fV0 :
        Deriv (eqF (ap1 (C pi (constN tag_ap1) (C pi get_ax_extra V0_F1)) input)
                    (cAp1_f_V_at GE cV0))
      ap1_fV0 =
        ruleTrans (ax_C pi (constN tag_ap1) (C pi get_ax_extra V0_F1) input)
          (ruleTrans (congL pi (ap1 (C pi get_ax_extra V0_F1) input) (constN_eq tag_ap1 input))
                     (congR pi (natCode tag_ap1) pi_eV0))

      ap1_fV1 :
        Deriv (eqF (ap1 (C pi (constN tag_ap1) (C pi get_ax_extra V1_F1)) input)
                    (cAp1_f_V_at GE cV1))
      ap1_fV1 =
        ruleTrans (ax_C pi (constN tag_ap1) (C pi get_ax_extra V1_F1) input)
          (ruleTrans (congL pi (ap1 (C pi get_ax_extra V1_F1) input) (constN_eq tag_ap1 input))
                     (congR pi (natCode tag_ap1) pi_eV1))

      -- C pi <ap1_fV0> <ap1_fV1>.
      pair_ap1 :
        Deriv (eqF (ap1 (C pi (C pi (constN tag_ap1) (C pi get_ax_extra V0_F1))
                              (C pi (constN tag_ap1) (C pi get_ax_extra V1_F1))) input)
                    (ap2 pi (cAp1_f_V_at GE cV0) (cAp1_f_V_at GE cV1)))
      pair_ap1 =
        ruleTrans (ax_C pi (C pi (constN tag_ap1) (C pi get_ax_extra V0_F1))
                          (C pi (constN tag_ap1) (C pi get_ax_extra V1_F1)) input)
          (ruleTrans (congL pi (ap1 (C pi (constN tag_ap1) (C pi get_ax_extra V1_F1)) input)
                            ap1_fV0)
                     (congR pi (cAp1_f_V_at GE cV0) ap1_fV1))

      -- C pi (constN tag_eq) <pair_ap1>.
      eq_pair :
        Deriv (eqF (ap1 (C pi (constN tag_eq)
                              (C pi (C pi (constN tag_ap1) (C pi get_ax_extra V0_F1))
                                    (C pi (constN tag_ap1) (C pi get_ax_extra V1_F1)))) input)
                    (ap2 pi (natCode tag_eq)
                            (ap2 pi (cAp1_f_V_at GE cV0) (cAp1_f_V_at GE cV1))))
      eq_pair =
        ruleTrans (ax_C pi (constN tag_eq)
                           (C pi (C pi (constN tag_ap1) (C pi get_ax_extra V0_F1))
                                 (C pi (constN tag_ap1) (C pi get_ax_extra V1_F1))) input)
          (ruleTrans (congL pi (ap1 (C pi (C pi (constN tag_ap1) (C pi get_ax_extra V0_F1))
                                          (C pi (constN tag_ap1) (C pi get_ax_extra V1_F1))) input)
                            (constN_eq tag_eq input))
                     (congR pi (natCode tag_eq) pair_ap1))

      -- C pi codeEq_V0_V1 <eq_pair>.
      pair_outer :
        Deriv (eqF (ap1 (C pi codeEq_V0_V1
                              (C pi (constN tag_eq)
                                    (C pi (C pi (constN tag_ap1) (C pi get_ax_extra V0_F1))
                                          (C pi (constN tag_ap1) (C pi get_ax_extra V1_F1))))) input)
                    (ap2 pi cEq01
                            (ap2 pi (natCode tag_eq)
                                    (ap2 pi (cAp1_f_V_at GE cV0) (cAp1_f_V_at GE cV1)))))
      pair_outer =
        ruleTrans (ax_C pi codeEq_V0_V1
                           (C pi (constN tag_eq)
                                 (C pi (C pi (constN tag_ap1) (C pi get_ax_extra V0_F1))
                                       (C pi (constN tag_ap1) (C pi get_ax_extra V1_F1)))) input)
          (ruleTrans (congL pi _ eq01_eval) (congR pi cEq01 eq_pair))

      -- Outer C pi (constN tag_imp).
  in ruleTrans (ax_C pi (constN tag_imp)
                       (C pi codeEq_V0_V1
                             (C pi (constN tag_eq)
                                   (C pi (C pi (constN tag_ap1) (C pi get_ax_extra V0_F1))
                                         (C pi (constN tag_ap1) (C pi get_ax_extra V1_F1))))) input)
       (ruleTrans (congL pi _ (constN_eq tag_imp input))
                  (congR pi (natCode tag_imp) pair_outer))

------------------------------------------------------------------------
-- The main closure.

thmT_at_axN5 :
  (extra : Term) ->
  Deriv (eqF (ap1 thmT (ap2 pi (natCode tag_ax) (ap2 pi (natCode N5) extra)))
              (outputRHS extra))
thmT_at_axN5 extra =
  let input : Term
      input = ap2 pi (natCode tag_ax) (ap2 pi (natCode N5) extra)

      Y_body : Term
      Y_body = ap2 pi (natCode N5) extra

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
      Fst_Y = axFst (natCode N5) extra

      get_ax_index_value :
        Deriv (eqF (ap1 get_ax_index stateP) (natCode N5))
      get_ax_index_value =
        ruleTrans get_ax_index_eq
          (ruleTrans (cong1 Fst Snd_sP_to_Y) Fst_Y)

      -- get_ax_extra stateP = extra.
      get_ax_extra_eq = get_ax_extra_at_pi P_outer (ap1 Snd prev)
      Snd_Y = axSnd (natCode N5) extra
      get_ax_extra_value :
        Deriv (eqF (ap1 get_ax_extra stateP) extra)
      get_ax_extra_value =
        ruleTrans get_ax_extra_eq
          (ruleTrans (cong1 Snd Snd_sP_to_Y) Snd_Y)

      -- Cascade.
      isAx0_O = isAxOf_at_neq_O zero N5 witness50 stateP get_ax_index_value
      isAx1_O = isAxOf_at_neq_O (suc zero) N5 witness51 stateP get_ax_index_value
      isAx2_O = isAxOf_at_neq_O (suc (suc zero)) N5 witness52 stateP get_ax_index_value
      isAx3_O = isAxOf_at_neq_O (suc (suc (suc zero))) N5 witness53 stateP get_ax_index_value
      isAx4_O = isAxOf_at_neq_O (suc (suc (suc (suc zero)))) N5 witness54 stateP get_ax_index_value
      isAx5_sO = isAxOf_at_eq_sO N5 stateP get_ax_index_value

      d0 = skipAt0 stateP isAx0_O
      d1 = skipAt1 stateP isAx1_O
      d2 = skipAt2 stateP isAx2_O
      d3 = skipAt3 stateP isAx3_O
      d4 = skipAt4 stateP isAx4_O
      d5 = landAt5 stateP isAx5_sO

      axBranch_to_branch5 =
        ruleTrans d0 (ruleTrans d1 (ruleTrans d2 (ruleTrans d3 (ruleTrans d4 d5))))

      axBranch5_eval :
        Deriv (eqF (ap1 axBranch5 stateP) (outputRHS (ap1 get_ax_extra stateP)))
      axBranch5_eval = axBranch5_value stateP

      -- Substitute (ap1 get_ax_extra stateP) -> extra inside outputRHS.
      -- outputRHS GE substitutes GE at two positions inside (cAp1_f_V_at GE _).
      -- Use congruence on the outermost-to-innermost structure :
      --   substitute  GE -> extra  in  cAp1_f_V_at GE cV0  to get  cAp1_f_V_at extra cV0.

      ge_eq : Deriv (eqF (ap1 get_ax_extra stateP) extra)
      ge_eq = get_ax_extra_value

      ap1_fV0_subst :
        Deriv (eqF (cAp1_f_V_at (ap1 get_ax_extra stateP) cV0) (cAp1_f_V_at extra cV0))
      ap1_fV0_subst = congR pi (natCode tag_ap1) (congL pi cV0 ge_eq)

      ap1_fV1_subst :
        Deriv (eqF (cAp1_f_V_at (ap1 get_ax_extra stateP) cV1) (cAp1_f_V_at extra cV1))
      ap1_fV1_subst = congR pi (natCode tag_ap1) (congL pi cV1 ge_eq)

      pair_ap1_subst :
        Deriv (eqF (ap2 pi (cAp1_f_V_at (ap1 get_ax_extra stateP) cV0)
                            (cAp1_f_V_at (ap1 get_ax_extra stateP) cV1))
                    (ap2 pi (cAp1_f_V_at extra cV0) (cAp1_f_V_at extra cV1)))
      pair_ap1_subst =
        ruleTrans (congL pi (cAp1_f_V_at (ap1 get_ax_extra stateP) cV1) ap1_fV0_subst)
                  (congR pi (cAp1_f_V_at extra cV0) ap1_fV1_subst)

      eq_inner_subst :
        Deriv (eqF (ap2 pi (natCode tag_eq)
                            (ap2 pi (cAp1_f_V_at (ap1 get_ax_extra stateP) cV0)
                                    (cAp1_f_V_at (ap1 get_ax_extra stateP) cV1)))
                    (ap2 pi (natCode tag_eq)
                            (ap2 pi (cAp1_f_V_at extra cV0) (cAp1_f_V_at extra cV1))))
      eq_inner_subst = congR pi (natCode tag_eq) pair_ap1_subst

      pair_outer_subst :
        Deriv (eqF (ap2 pi cEq01
                           (ap2 pi (natCode tag_eq)
                                   (ap2 pi (cAp1_f_V_at (ap1 get_ax_extra stateP) cV0)
                                           (cAp1_f_V_at (ap1 get_ax_extra stateP) cV1))))
                    (ap2 pi cEq01
                           (ap2 pi (natCode tag_eq)
                                   (ap2 pi (cAp1_f_V_at extra cV0) (cAp1_f_V_at extra cV1)))))
      pair_outer_subst = congR pi cEq01 eq_inner_subst

      final_subst :
        Deriv (eqF (outputRHS (ap1 get_ax_extra stateP)) (outputRHS extra))
      final_subst = congR pi (natCode tag_imp) pair_outer_subst

      chain_to_axBranch = ruleTrans chain_to_stepBody stepBody_to_axBranch
      chain_to_branch5 = ruleTrans chain_to_axBranch axBranch_to_branch5
      chain_to_eval = ruleTrans chain_to_branch5 axBranch5_eval
  in ruleTrans chain_to_eval final_subst
