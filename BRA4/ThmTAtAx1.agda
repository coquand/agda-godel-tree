{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.ThmTAtAx1 -- axiom 1 closure :  o(var 0) = 0 .
--
--   thmT_at_axN1 :
--     (extra : Term) ->
--     Deriv (eqF (ap1 thmT (ap2 pi (natCode tag_ax) (ap2 pi (natCode (suc zero)) extra)))
--                 (codeFormula (atomic (eqn (ap1 o (var zero)) O))))

module BRA4.ThmTAtAx1 where

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
  -- Descent witnesses : N=1 needs NatNeqWitness 1 0.
  witness10 : NatNeqWitness (suc zero) zero
  witness10 = natEqFalse_to_witness zero (suc zero) refl

------------------------------------------------------------------------
-- V0_F1 evaluation :  ap1 V0_F1 input  =  pi (natCode tag_var) (natCode zero) .

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

------------------------------------------------------------------------
-- axBranch1 evaluation.
-- axBranch1 = C pi (constN tag_eq)
--                  (C pi (C pi (constN tag_ap1) (C pi (constN tag_o) V0_F1))
--                        o)
-- Result : pi 10 (pi (pi 2 (pi 5 (pi 1 0))) 0)
--        = codeFormula (atomic (eqn (ap1 o (var zero)) O))

axBranch1_value :
  (input : Term) ->
  Deriv (eqF (ap1 axBranch1 input)
              (codeFormula (atomic (eqn (ap1 o (var zero)) O))))
axBranch1_value input =
  let -- Inner: C pi (constN tag_o) V0_F1.
      inner_unfold :
        Deriv (eqF (ap1 (C pi (constN tag_o) V0_F1) input)
                    (ap2 pi (ap1 (constN tag_o) input) (ap1 V0_F1 input)))
      inner_unfold = ax_C pi (constN tag_o) V0_F1 input

      cN_o = constN_eq tag_o input
      V0_eval = V0_F1_value input

      inner_value :
        Deriv (eqF (ap1 (C pi (constN tag_o) V0_F1) input)
                    (ap2 pi (natCode tag_o) (ap2 pi (natCode tag_var) (natCode zero))))
      inner_value =
        ruleTrans inner_unfold
          (ruleTrans (congL pi (ap1 V0_F1 input) cN_o)
                     (congR pi (natCode tag_o) V0_eval))

      -- Middle: C pi (constN tag_ap1) <inner>.
      mid_unfold :
        Deriv (eqF (ap1 (C pi (constN tag_ap1) (C pi (constN tag_o) V0_F1)) input)
                    (ap2 pi (ap1 (constN tag_ap1) input)
                            (ap1 (C pi (constN tag_o) V0_F1) input)))
      mid_unfold = ax_C pi (constN tag_ap1) (C pi (constN tag_o) V0_F1) input

      cN_ap1 = constN_eq tag_ap1 input

      mid_value :
        Deriv (eqF (ap1 (C pi (constN tag_ap1) (C pi (constN tag_o) V0_F1)) input)
                    (ap2 pi (natCode tag_ap1)
                            (ap2 pi (natCode tag_o) (ap2 pi (natCode tag_var) (natCode zero)))))
      mid_value =
        ruleTrans mid_unfold
          (ruleTrans (congL pi (ap1 (C pi (constN tag_o) V0_F1) input) cN_ap1)
                     (congR pi (natCode tag_ap1) inner_value))

      -- Outer-inner: C pi <mid> o.
      oi_unfold :
        Deriv (eqF (ap1 (C pi (C pi (constN tag_ap1) (C pi (constN tag_o) V0_F1)) o) input)
                    (ap2 pi (ap1 (C pi (constN tag_ap1) (C pi (constN tag_o) V0_F1)) input)
                            (ap1 o input)))
      oi_unfold = ax_C pi (C pi (constN tag_ap1) (C pi (constN tag_o) V0_F1)) o input

      oO = ax_o input

      oi_value :
        Deriv (eqF (ap1 (C pi (C pi (constN tag_ap1) (C pi (constN tag_o) V0_F1)) o) input)
                    (ap2 pi (ap2 pi (natCode tag_ap1)
                                    (ap2 pi (natCode tag_o)
                                            (ap2 pi (natCode tag_var) (natCode zero))))
                            O))
      oi_value =
        ruleTrans oi_unfold
          (ruleTrans (congL pi (ap1 o input) mid_value)
                     (congR pi (ap2 pi (natCode tag_ap1)
                                       (ap2 pi (natCode tag_o)
                                               (ap2 pi (natCode tag_var) (natCode zero))))
                            oO))

      -- Outer: C pi (constN tag_eq) <oi>.
      out_unfold :
        Deriv (eqF (ap1 axBranch1 input)
                    (ap2 pi (ap1 (constN tag_eq) input)
                            (ap1 (C pi (C pi (constN tag_ap1) (C pi (constN tag_o) V0_F1)) o) input)))
      out_unfold = ax_C pi (constN tag_eq)
                    (C pi (C pi (constN tag_ap1) (C pi (constN tag_o) V0_F1)) o)
                    input

      cN_eq = constN_eq tag_eq input
  in ruleTrans out_unfold
       (ruleTrans (congL pi (ap1 (C pi (C pi (constN tag_ap1) (C pi (constN tag_o) V0_F1)) o) input) cN_eq)
                  (congR pi (natCode tag_eq) oi_value))

------------------------------------------------------------------------
-- The main closure.

thmT_at_axN1 :
  (extra : Term) ->
  Deriv (eqF (ap1 thmT (ap2 pi (natCode tag_ax) (ap2 pi (natCode (suc zero)) extra)))
              (codeFormula (atomic (eqn (ap1 o (var zero)) O))))
thmT_at_axN1 extra =
  let input : Term
      input = ap2 pi (natCode tag_ax) (ap2 pi (natCode (suc zero)) extra)

      Y_body : Term
      Y_body = ap2 pi (natCode (suc zero)) extra

      A_outer : Term
      A_outer = O

      P_outer : Term
      P_outer = pi_succ_outer A_outer Y_body

      prev : Term
      prev = ap2 (cov_spec baseValue_thmT stepFun_thmT) O P_outer

      stateP : Term
      stateP = ap2 pi P_outer (ap1 Snd prev)

      input_eq_sP_outer = pi_at_succ A_outer Y_body

      chain_to_stepBody :
        Deriv (eqF (ap1 thmT input) (ap1 stepBody_thmT stateP))
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
      Fst_Y = axFst (natCode (suc zero)) extra

      get_ax_index_value :
        Deriv (eqF (ap1 get_ax_index stateP) (natCode (suc zero)))
      get_ax_index_value =
        ruleTrans get_ax_index_eq
          (ruleTrans (cong1 Fst Snd_sP_to_Y) Fst_Y)

      -- Cascade: skipAt0 then landAt1.
      isAx0_O : Deriv (eqF (ap1 isAx0 stateP) O)
      isAx0_O = isAxOf_at_neq_O zero (suc zero) witness10 stateP get_ax_index_value

      isAx1_sO : Deriv (eqF (ap1 isAx1 stateP) (ap1 s O))
      isAx1_sO = isAxOf_at_eq_sO (suc zero) stateP get_ax_index_value

      step_to_disp1 = skipAt0 stateP isAx0_O
      disp1_to_branch1 = landAt1 stateP isAx1_sO

      axBranch_to_branch1 :
        Deriv (eqF (ap1 ax_branch_thmT stateP) (ap1 axBranch1 stateP))
      axBranch_to_branch1 = ruleTrans step_to_disp1 disp1_to_branch1

      axBranch1_eval = axBranch1_value stateP

      chain_to_axBranch :
        Deriv (eqF (ap1 thmT input) (ap1 ax_branch_thmT stateP))
      chain_to_axBranch = ruleTrans chain_to_stepBody stepBody_to_axBranch

      chain_to_branch1 :
        Deriv (eqF (ap1 thmT input) (ap1 axBranch1 stateP))
      chain_to_branch1 = ruleTrans chain_to_axBranch axBranch_to_branch1
  in ruleTrans chain_to_branch1 axBranch1_eval
