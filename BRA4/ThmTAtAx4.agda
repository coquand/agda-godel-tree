{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.ThmTAtAx4 -- axiom 4 closure :  v0 = v1  >  v0 = v2  >  v1 = v2 .

module BRA4.ThmTAtAx4 where

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
  witness40 : NatNeqWitness (suc (suc (suc (suc zero)))) zero
  witness40 = natEqFalse_to_witness zero (suc (suc (suc (suc zero)))) refl

  witness41 : NatNeqWitness (suc (suc (suc (suc zero)))) (suc zero)
  witness41 = natEqFalse_to_witness (suc zero) (suc (suc (suc (suc zero)))) refl

  witness42 : NatNeqWitness (suc (suc (suc (suc zero)))) (suc (suc zero))
  witness42 = natEqFalse_to_witness (suc (suc zero)) (suc (suc (suc (suc zero)))) refl

  witness43 : NatNeqWitness (suc (suc (suc (suc zero)))) (suc (suc (suc zero)))
  witness43 = natEqFalse_to_witness (suc (suc (suc zero))) (suc (suc (suc (suc zero)))) refl

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

V2_F1_value :
  (input : Term) ->
  Deriv (eqF (ap1 V2_F1 input) (ap2 pi (natCode tag_var) (natCode (suc (suc zero)))))
V2_F1_value input =
  let e1 = ax_C pi (constN tag_var) (constN (suc (suc zero))) input
      cN_var = constN_eq tag_var input
      cN2 = constN_eq (suc (suc zero)) input
  in ruleTrans e1
       (ruleTrans (congL pi (ap1 (constN (suc (suc zero))) input) cN_var)
                  (congR pi (natCode tag_var) cN2))

-- codeEq_Vi_Vj value lemmas.
codeEq_V0_V1_value :
  (input : Term) ->
  Deriv (eqF (ap1 codeEq_V0_V1 input)
              (ap2 pi (natCode tag_eq)
                      (ap2 pi (ap2 pi (natCode tag_var) (natCode zero))
                              (ap2 pi (natCode tag_var) (natCode (suc zero))))))
codeEq_V0_V1_value input =
  let V0_eval = V0_F1_value input
      V1_eval = V1_F1_value input
      pi_VV_unfold = ax_C pi V0_F1 V1_F1 input
      pi_VV_value =
        ruleTrans pi_VV_unfold
          (ruleTrans (congL pi (ap1 V1_F1 input) V0_eval)
                     (congR pi (ap2 pi (natCode tag_var) (natCode zero)) V1_eval))
      outer_unfold = ax_C pi (constN tag_eq) (C pi V0_F1 V1_F1) input
      cN_eq = constN_eq tag_eq input
  in ruleTrans outer_unfold
       (ruleTrans (congL pi (ap1 (C pi V0_F1 V1_F1) input) cN_eq)
                  (congR pi (natCode tag_eq) pi_VV_value))

codeEq_V0_V2_value :
  (input : Term) ->
  Deriv (eqF (ap1 codeEq_V0_V2 input)
              (ap2 pi (natCode tag_eq)
                      (ap2 pi (ap2 pi (natCode tag_var) (natCode zero))
                              (ap2 pi (natCode tag_var) (natCode (suc (suc zero)))))))
codeEq_V0_V2_value input =
  let V0_eval = V0_F1_value input
      V2_eval = V2_F1_value input
      pi_VV_unfold = ax_C pi V0_F1 V2_F1 input
      pi_VV_value =
        ruleTrans pi_VV_unfold
          (ruleTrans (congL pi (ap1 V2_F1 input) V0_eval)
                     (congR pi (ap2 pi (natCode tag_var) (natCode zero)) V2_eval))
      outer_unfold = ax_C pi (constN tag_eq) (C pi V0_F1 V2_F1) input
      cN_eq = constN_eq tag_eq input
  in ruleTrans outer_unfold
       (ruleTrans (congL pi (ap1 (C pi V0_F1 V2_F1) input) cN_eq)
                  (congR pi (natCode tag_eq) pi_VV_value))

codeEq_V1_V2_value :
  (input : Term) ->
  Deriv (eqF (ap1 codeEq_V1_V2 input)
              (ap2 pi (natCode tag_eq)
                      (ap2 pi (ap2 pi (natCode tag_var) (natCode (suc zero)))
                              (ap2 pi (natCode tag_var) (natCode (suc (suc zero)))))))
codeEq_V1_V2_value input =
  let V1_eval = V1_F1_value input
      V2_eval = V2_F1_value input
      pi_VV_unfold = ax_C pi V1_F1 V2_F1 input
      pi_VV_value =
        ruleTrans pi_VV_unfold
          (ruleTrans (congL pi (ap1 V2_F1 input) V1_eval)
                     (congR pi (ap2 pi (natCode tag_var) (natCode (suc zero))) V2_eval))
      outer_unfold = ax_C pi (constN tag_eq) (C pi V1_F1 V2_F1) input
      cN_eq = constN_eq tag_eq input
  in ruleTrans outer_unfold
       (ruleTrans (congL pi (ap1 (C pi V1_F1 V2_F1) input) cN_eq)
                  (congR pi (natCode tag_eq) pi_VV_value))

------------------------------------------------------------------------
-- axBranch4 evaluation.

axBranch4_value :
  (input : Term) ->
  Deriv (eqF (ap1 axBranch4 input)
              (codeFormula (imp (atomic (eqn (var zero) (var (suc zero))))
                                 (imp (atomic (eqn (var zero) (var (suc (suc zero)))))
                                      (atomic (eqn (var (suc zero)) (var (suc (suc zero)))))))))
axBranch4_value input =
  let e01 = codeEq_V0_V1_value input
      e02 = codeEq_V0_V2_value input
      e12 = codeEq_V1_V2_value input

      -- Inner: C pi codeEq_V0_V2 codeEq_V1_V2.
      inner_unfold = ax_C pi codeEq_V0_V2 codeEq_V1_V2 input
      inner_value :
        Deriv (eqF (ap1 (C pi codeEq_V0_V2 codeEq_V1_V2) input)
                    (ap2 pi (ap2 pi (natCode tag_eq)
                                    (ap2 pi (ap2 pi (natCode tag_var) (natCode zero))
                                            (ap2 pi (natCode tag_var) (natCode (suc (suc zero))))))
                            (ap2 pi (natCode tag_eq)
                                    (ap2 pi (ap2 pi (natCode tag_var) (natCode (suc zero)))
                                            (ap2 pi (natCode tag_var) (natCode (suc (suc zero))))))))
      inner_value =
        ruleTrans inner_unfold
          (ruleTrans (congL pi (ap1 codeEq_V1_V2 input) e02)
                     (congR pi _ e12))

      -- Middle: C pi (constN tag_imp) <inner>.
      mid_unfold = ax_C pi (constN tag_imp) (C pi codeEq_V0_V2 codeEq_V1_V2) input
      cN_imp1 = constN_eq tag_imp input
      mid_value :
        Deriv (eqF (ap1 (C pi (constN tag_imp) (C pi codeEq_V0_V2 codeEq_V1_V2)) input)
                    (ap2 pi (natCode tag_imp)
                            (ap2 pi (ap2 pi (natCode tag_eq)
                                            (ap2 pi (ap2 pi (natCode tag_var) (natCode zero))
                                                    (ap2 pi (natCode tag_var) (natCode (suc (suc zero))))))
                                    (ap2 pi (natCode tag_eq)
                                            (ap2 pi (ap2 pi (natCode tag_var) (natCode (suc zero)))
                                                    (ap2 pi (natCode tag_var) (natCode (suc (suc zero)))))))))
      mid_value =
        ruleTrans mid_unfold
          (ruleTrans (congL pi (ap1 (C pi codeEq_V0_V2 codeEq_V1_V2) input) cN_imp1)
                     (congR pi (natCode tag_imp) inner_value))

      -- Outer-inner: C pi codeEq_V0_V1 <mid>.
      oi_unfold = ax_C pi codeEq_V0_V1 (C pi (constN tag_imp) (C pi codeEq_V0_V2 codeEq_V1_V2)) input
      oi_value :
        Deriv (eqF (ap1 (C pi codeEq_V0_V1 (C pi (constN tag_imp) (C pi codeEq_V0_V2 codeEq_V1_V2))) input)
                    (ap2 pi (ap2 pi (natCode tag_eq)
                                    (ap2 pi (ap2 pi (natCode tag_var) (natCode zero))
                                            (ap2 pi (natCode tag_var) (natCode (suc zero)))))
                            (ap2 pi (natCode tag_imp)
                                    (ap2 pi (ap2 pi (natCode tag_eq)
                                                    (ap2 pi (ap2 pi (natCode tag_var) (natCode zero))
                                                            (ap2 pi (natCode tag_var) (natCode (suc (suc zero))))))
                                            (ap2 pi (natCode tag_eq)
                                                    (ap2 pi (ap2 pi (natCode tag_var) (natCode (suc zero)))
                                                            (ap2 pi (natCode tag_var) (natCode (suc (suc zero))))))))))
      oi_value =
        ruleTrans oi_unfold
          (ruleTrans (congL pi (ap1 (C pi (constN tag_imp) (C pi codeEq_V0_V2 codeEq_V1_V2)) input) e01)
                     (congR pi _ mid_value))

      -- Outer.
      out_unfold = ax_C pi (constN tag_imp)
                    (C pi codeEq_V0_V1 (C pi (constN tag_imp) (C pi codeEq_V0_V2 codeEq_V1_V2)))
                    input
      cN_imp2 = constN_eq tag_imp input
  in ruleTrans out_unfold
       (ruleTrans (congL pi (ap1 (C pi codeEq_V0_V1 (C pi (constN tag_imp) (C pi codeEq_V0_V2 codeEq_V1_V2))) input) cN_imp2)
                  (congR pi (natCode tag_imp) oi_value))

------------------------------------------------------------------------
-- The main closure.

thmT_at_axN4 :
  (extra : Term) ->
  Deriv (eqF (ap1 thmT (ap2 pi (natCode tag_ax)
                                (ap2 pi (natCode (suc (suc (suc (suc zero))))) extra)))
              (codeFormula (imp (atomic (eqn (var zero) (var (suc zero))))
                                 (imp (atomic (eqn (var zero) (var (suc (suc zero)))))
                                      (atomic (eqn (var (suc zero)) (var (suc (suc zero)))))))))
thmT_at_axN4 extra =
  let input : Term
      input = ap2 pi (natCode tag_ax) (ap2 pi (natCode (suc (suc (suc (suc zero))))) extra)

      Y_body : Term
      Y_body = ap2 pi (natCode (suc (suc (suc (suc zero))))) extra

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
      Fst_Y = axFst (natCode (suc (suc (suc (suc zero))))) extra

      get_ax_index_value :
        Deriv (eqF (ap1 get_ax_index stateP) (natCode (suc (suc (suc (suc zero))))))
      get_ax_index_value =
        ruleTrans get_ax_index_eq
          (ruleTrans (cong1 Fst Snd_sP_to_Y) Fst_Y)

      -- Cascade: skipAt0, skipAt1, skipAt2, skipAt3, landAt4.
      isAx0_O = isAxOf_at_neq_O zero (suc (suc (suc (suc zero)))) witness40 stateP get_ax_index_value
      isAx1_O = isAxOf_at_neq_O (suc zero) (suc (suc (suc (suc zero)))) witness41 stateP get_ax_index_value
      isAx2_O = isAxOf_at_neq_O (suc (suc zero)) (suc (suc (suc (suc zero)))) witness42 stateP get_ax_index_value
      isAx3_O = isAxOf_at_neq_O (suc (suc (suc zero))) (suc (suc (suc (suc zero)))) witness43 stateP get_ax_index_value
      isAx4_sO = isAxOf_at_eq_sO (suc (suc (suc (suc zero)))) stateP get_ax_index_value

      d0 = skipAt0 stateP isAx0_O
      d1 = skipAt1 stateP isAx1_O
      d2 = skipAt2 stateP isAx2_O
      d3 = skipAt3 stateP isAx3_O
      d4 = landAt4 stateP isAx4_sO

      axBranch_to_branch4 =
        ruleTrans d0 (ruleTrans d1 (ruleTrans d2 (ruleTrans d3 d4)))

      axBranch4_eval = axBranch4_value stateP

      chain_to_axBranch = ruleTrans chain_to_stepBody stepBody_to_axBranch
      chain_to_branch4 = ruleTrans chain_to_axBranch axBranch_to_branch4
  in ruleTrans chain_to_branch4 axBranch4_eval
