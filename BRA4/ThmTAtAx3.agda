{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.ThmTAtAx3 -- axiom 3 closure :  v(var 0, var 1) = var 1 .

module BRA4.ThmTAtAx3 where

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
  witness30 : NatNeqWitness (suc (suc (suc zero))) zero
  witness30 = natEqFalse_to_witness zero (suc (suc (suc zero))) refl

  witness31 : NatNeqWitness (suc (suc (suc zero))) (suc zero)
  witness31 = natEqFalse_to_witness (suc zero) (suc (suc (suc zero))) refl

  witness32 : NatNeqWitness (suc (suc (suc zero))) (suc (suc zero))
  witness32 = natEqFalse_to_witness (suc (suc zero)) (suc (suc (suc zero))) refl

V0_F1_value :
  (input : Term) ->
  Deriv (eqF (ap1 V0_F1 input) (ap2 pi (natCode tag_var) (natCode zero)))
V0_F1_value input =
  let e1 = ax_C pi (constN tag_var) (constN zero) input
      cN_var = constN_eq tag_var input
      cN0 = constN_eq zero input
  in ruleTrans e1
       (ruleTrans (congL pi (ap1 (constN zero) input) cN_var)
                  (congR pi (natCode tag_var) cN0))

V1_F1_value :
  (input : Term) ->
  Deriv (eqF (ap1 V1_F1 input) (ap2 pi (natCode tag_var) (natCode (suc zero))))
V1_F1_value input =
  let e1 = ax_C pi (constN tag_var) (constN (suc zero)) input
      cN_var = constN_eq tag_var input
      cN1 = constN_eq (suc zero) input
  in ruleTrans e1
       (ruleTrans (congL pi (ap1 (constN (suc zero)) input) cN_var)
                  (congR pi (natCode tag_var) cN1))

------------------------------------------------------------------------
-- axBranch3 evaluation.
-- axBranch3 = C pi (constN tag_eq)
--                  (C pi (C pi (constN tag_ap2)
--                              (C pi (constN tag_v) (C pi V0_F1 V1_F1)))
--                        V1_F1)
-- Result : pi 10 (pi (pi 3 (pi 8 (pi V0 V1))) V1)
--        = codeFormula (atomic (eqn (ap2 v (var 0) (var 1)) (var 1)))

axBranch3_value :
  (input : Term) ->
  Deriv (eqF (ap1 axBranch3 input)
              (codeFormula (atomic (eqn (ap2 v (var zero) (var (suc zero))) (var (suc zero))))))
axBranch3_value input =
  let V0_eval = V0_F1_value input
      V1_eval = V1_F1_value input

      -- C pi V0_F1 V1_F1 input = pi V0 V1.
      pi_V0V1_unfold = ax_C pi V0_F1 V1_F1 input
      pi_V0V1_value :
        Deriv (eqF (ap1 (C pi V0_F1 V1_F1) input)
                    (ap2 pi (ap2 pi (natCode tag_var) (natCode zero))
                            (ap2 pi (natCode tag_var) (natCode (suc zero)))))
      pi_V0V1_value =
        ruleTrans pi_V0V1_unfold
          (ruleTrans (congL pi (ap1 V1_F1 input) V0_eval)
                     (congR pi (ap2 pi (natCode tag_var) (natCode zero)) V1_eval))

      -- C pi (constN tag_v) <pi_V0V1>.
      inner_unfold = ax_C pi (constN tag_v) (C pi V0_F1 V1_F1) input
      cN_v = constN_eq tag_v input
      inner_value :
        Deriv (eqF (ap1 (C pi (constN tag_v) (C pi V0_F1 V1_F1)) input)
                    (ap2 pi (natCode tag_v)
                            (ap2 pi (ap2 pi (natCode tag_var) (natCode zero))
                                    (ap2 pi (natCode tag_var) (natCode (suc zero))))))
      inner_value =
        ruleTrans inner_unfold
          (ruleTrans (congL pi (ap1 (C pi V0_F1 V1_F1) input) cN_v)
                     (congR pi (natCode tag_v) pi_V0V1_value))

      -- C pi (constN tag_ap2) <inner>.
      mid_unfold = ax_C pi (constN tag_ap2) (C pi (constN tag_v) (C pi V0_F1 V1_F1)) input
      cN_ap2 = constN_eq tag_ap2 input
      mid_value :
        Deriv (eqF (ap1 (C pi (constN tag_ap2) (C pi (constN tag_v) (C pi V0_F1 V1_F1))) input)
                    (ap2 pi (natCode tag_ap2)
                            (ap2 pi (natCode tag_v)
                                    (ap2 pi (ap2 pi (natCode tag_var) (natCode zero))
                                            (ap2 pi (natCode tag_var) (natCode (suc zero)))))))
      mid_value =
        ruleTrans mid_unfold
          (ruleTrans (congL pi (ap1 (C pi (constN tag_v) (C pi V0_F1 V1_F1)) input) cN_ap2)
                     (congR pi (natCode tag_ap2) inner_value))

      -- C pi <mid> V1_F1.
      oi_unfold = ax_C pi (C pi (constN tag_ap2) (C pi (constN tag_v) (C pi V0_F1 V1_F1))) V1_F1 input
      oi_value :
        Deriv (eqF (ap1 (C pi (C pi (constN tag_ap2) (C pi (constN tag_v) (C pi V0_F1 V1_F1))) V1_F1) input)
                    (ap2 pi (ap2 pi (natCode tag_ap2)
                                    (ap2 pi (natCode tag_v)
                                            (ap2 pi (ap2 pi (natCode tag_var) (natCode zero))
                                                    (ap2 pi (natCode tag_var) (natCode (suc zero))))))
                            (ap2 pi (natCode tag_var) (natCode (suc zero)))))
      oi_value =
        ruleTrans oi_unfold
          (ruleTrans (congL pi (ap1 V1_F1 input) mid_value)
                     (congR pi (ap2 pi (natCode tag_ap2)
                                       (ap2 pi (natCode tag_v)
                                               (ap2 pi (ap2 pi (natCode tag_var) (natCode zero))
                                                       (ap2 pi (natCode tag_var) (natCode (suc zero))))))
                            V1_eval))

      -- Outer.
      out_unfold = ax_C pi (constN tag_eq)
                    (C pi (C pi (constN tag_ap2) (C pi (constN tag_v) (C pi V0_F1 V1_F1))) V1_F1)
                    input
      cN_eq = constN_eq tag_eq input
  in ruleTrans out_unfold
       (ruleTrans (congL pi (ap1 (C pi (C pi (constN tag_ap2) (C pi (constN tag_v) (C pi V0_F1 V1_F1))) V1_F1) input) cN_eq)
                  (congR pi (natCode tag_eq) oi_value))

------------------------------------------------------------------------
-- The main closure.

thmT_at_axN3 :
  (extra : Term) ->
  Deriv (eqF (ap1 thmT (ap2 pi (natCode tag_ax)
                                (ap2 pi (natCode (suc (suc (suc zero)))) extra)))
              (codeFormula (atomic (eqn (ap2 v (var zero) (var (suc zero)))
                                                (var (suc zero))))))
thmT_at_axN3 extra =
  let input : Term
      input = ap2 pi (natCode tag_ax) (ap2 pi (natCode (suc (suc (suc zero)))) extra)

      Y_body : Term
      Y_body = ap2 pi (natCode (suc (suc (suc zero)))) extra

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
      Fst_Y = axFst (natCode (suc (suc (suc zero)))) extra

      get_ax_index_value :
        Deriv (eqF (ap1 get_ax_index stateP) (natCode (suc (suc (suc zero)))))
      get_ax_index_value =
        ruleTrans get_ax_index_eq
          (ruleTrans (cong1 Fst Snd_sP_to_Y) Fst_Y)

      -- Cascade: skipAt0, skipAt1, skipAt2, landAt3.
      isAx0_O = isAxOf_at_neq_O zero (suc (suc (suc zero))) witness30 stateP get_ax_index_value
      isAx1_O = isAxOf_at_neq_O (suc zero) (suc (suc (suc zero))) witness31 stateP get_ax_index_value
      isAx2_O = isAxOf_at_neq_O (suc (suc zero)) (suc (suc (suc zero))) witness32 stateP get_ax_index_value
      isAx3_sO = isAxOf_at_eq_sO (suc (suc (suc zero))) stateP get_ax_index_value

      step_to_disp1 = skipAt0 stateP isAx0_O
      disp1_to_disp2 = skipAt1 stateP isAx1_O
      disp2_to_disp3 = skipAt2 stateP isAx2_O
      disp3_to_branch3 = landAt3 stateP isAx3_sO

      axBranch_to_branch3 =
        ruleTrans step_to_disp1
          (ruleTrans disp1_to_disp2
            (ruleTrans disp2_to_disp3 disp3_to_branch3))

      axBranch3_eval = axBranch3_value stateP

      chain_to_axBranch = ruleTrans chain_to_stepBody stepBody_to_axBranch
      chain_to_branch3 = ruleTrans chain_to_axBranch axBranch_to_branch3
  in ruleTrans chain_to_branch3 axBranch3_eval
