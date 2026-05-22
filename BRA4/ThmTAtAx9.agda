{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.ThmTAtAx9 -- axiom 9 (R_base) :  R g h1 h2 (v0, O) = g(v0) .
-- extra = codeFun2 (R g h1 h2) = pi tag_R (pi codeG (pi codeH1 codeH2)).

module BRA4.ThmTAtAx9 where

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
  N9 : Nat
  N9 = suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))

  cV0 : Term
  cV0 = ap2 pi (natCode tag_var) (natCode zero)

  outputRHS : Term -> Term
  outputRHS extra =
    let G = ap1 Fst (ap1 Snd extra)
        codeLHS = ap2 pi (natCode tag_ap2) (ap2 pi extra (ap2 pi cV0 O))
        codeRHS = ap2 pi (natCode tag_ap1) (ap2 pi G cV0)
    in ap2 pi (natCode tag_eq) (ap2 pi codeLHS codeRHS)

  mkW : (M : Nat) -> Eq (natEq M N9) false -> NatNeqWitness N9 M
  mkW M pf = natEqFalse_to_witness M N9 pf

  w0 = mkW zero refl
  w1 = mkW (suc zero) refl
  w2 = mkW (suc (suc zero)) refl
  w3 = mkW (suc (suc (suc zero))) refl
  w4 = mkW (suc (suc (suc (suc zero)))) refl
  w5 = mkW (suc (suc (suc (suc (suc zero))))) refl
  w6 = mkW (suc (suc (suc (suc (suc (suc zero)))))) refl
  w7 = mkW (suc (suc (suc (suc (suc (suc (suc zero))))))) refl
  w8 = mkW (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) refl

V0_F1_value :
  (input : Term) -> Deriv (eqF (ap1 V0_F1 input) cV0)
V0_F1_value input =
  ruleTrans (ax_C pi (constN tag_var) (constN zero) input)
    (ruleTrans (congL pi (ap1 (constN zero) input) (constN_eq tag_var input))
               (congR pi (natCode tag_var) (constN_eq zero input)))

------------------------------------------------------------------------
-- axBranch9 = C pi (constN tag_eq)
--             (C pi (C pi (constN tag_ap2) (C pi get_ax_extra (C pi V0_F1 o)))
--                   (C pi (constN tag_ap1) (C pi get_extra_g_after_tag V0_F1)))

axBranch9_value :
  (input : Term) ->
  Deriv (eqF (ap1 axBranch9 input) (outputRHS (ap1 get_ax_extra input)))
axBranch9_value input =
  let V0_eval = V0_F1_value input
      GE = ap1 get_ax_extra input
      G = ap1 Fst (ap1 Snd GE)

      get_g_eq :
        Deriv (eqF (ap1 get_extra_g_after_tag input) G)
      get_g_eq =
        ruleTrans (compose1U_eq Fst (compose1U Snd get_ax_extra) input)
                  (cong1 Fst (compose1U_eq Snd get_ax_extra input))

      -- C pi V0_F1 o input = pi V0 O.
      piV0O :
        Deriv (eqF (ap1 (C pi V0_F1 o) input) (ap2 pi cV0 O))
      piV0O =
        ruleTrans (ax_C pi V0_F1 o input)
          (ruleTrans (congL pi (ap1 o input) V0_eval) (congR pi cV0 (ax_o input)))

      -- C pi get_ax_extra (C pi V0_F1 o) input = pi GE (pi V0 O).
      pi_GE_V0O :
        Deriv (eqF (ap1 (C pi get_ax_extra (C pi V0_F1 o)) input)
                    (ap2 pi GE (ap2 pi cV0 O)))
      pi_GE_V0O =
        ruleTrans (ax_C pi get_ax_extra (C pi V0_F1 o) input)
          (congR pi GE piV0O)

      -- C pi (constN tag_ap2) <pi_GE_V0O>.
      codeLHS_eq :
        Deriv (eqF (ap1 (C pi (constN tag_ap2) (C pi get_ax_extra (C pi V0_F1 o))) input)
                    (ap2 pi (natCode tag_ap2) (ap2 pi GE (ap2 pi cV0 O))))
      codeLHS_eq =
        ruleTrans (ax_C pi (constN tag_ap2) (C pi get_ax_extra (C pi V0_F1 o)) input)
          (ruleTrans (congL pi _ (constN_eq tag_ap2 input))
                     (congR pi (natCode tag_ap2) pi_GE_V0O))

      -- C pi get_extra_g_after_tag V0_F1 input = pi G V0.
      pi_G_V0 :
        Deriv (eqF (ap1 (C pi get_extra_g_after_tag V0_F1) input) (ap2 pi G cV0))
      pi_G_V0 =
        ruleTrans (ax_C pi get_extra_g_after_tag V0_F1 input)
          (ruleTrans (congL pi (ap1 V0_F1 input) get_g_eq) (congR pi G V0_eval))

      codeRHS_eq :
        Deriv (eqF (ap1 (C pi (constN tag_ap1) (C pi get_extra_g_after_tag V0_F1)) input)
                    (ap2 pi (natCode tag_ap1) (ap2 pi G cV0)))
      codeRHS_eq =
        ruleTrans (ax_C pi (constN tag_ap1) (C pi get_extra_g_after_tag V0_F1) input)
          (ruleTrans (congL pi _ (constN_eq tag_ap1 input))
                     (congR pi (natCode tag_ap1) pi_G_V0))

      -- C pi <codeLHS_eq> <codeRHS_eq>.
      pair_LR :
        Deriv (eqF (ap1 (C pi (C pi (constN tag_ap2) (C pi get_ax_extra (C pi V0_F1 o)))
                              (C pi (constN tag_ap1) (C pi get_extra_g_after_tag V0_F1))) input)
                    (ap2 pi (ap2 pi (natCode tag_ap2) (ap2 pi GE (ap2 pi cV0 O)))
                            (ap2 pi (natCode tag_ap1) (ap2 pi G cV0))))
      pair_LR =
        ruleTrans (ax_C pi (C pi (constN tag_ap2) (C pi get_ax_extra (C pi V0_F1 o)))
                            (C pi (constN tag_ap1) (C pi get_extra_g_after_tag V0_F1)) input)
          (ruleTrans (congL pi _ codeLHS_eq) (congR pi _ codeRHS_eq))

  in ruleTrans (ax_C pi (constN tag_eq)
                       (C pi (C pi (constN tag_ap2) (C pi get_ax_extra (C pi V0_F1 o)))
                             (C pi (constN tag_ap1) (C pi get_extra_g_after_tag V0_F1))) input)
       (ruleTrans (congL pi _ (constN_eq tag_eq input))
                  (congR pi (natCode tag_eq) pair_LR))

------------------------------------------------------------------------
thmT_at_axN9 :
  (extra : Term) ->
  Deriv (eqF (ap1 thmT (ap2 pi (natCode tag_ax) (ap2 pi (natCode N9) extra)))
              (outputRHS extra))
thmT_at_axN9 extra =
  let input : Term
      input = ap2 pi (natCode tag_ax) (ap2 pi (natCode N9) extra)
      Y_body : Term
      Y_body = ap2 pi (natCode N9) extra
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
      Fst_Y = axFst (natCode N9) extra

      get_ax_index_value :
        Deriv (eqF (ap1 get_ax_index stateP) (natCode N9))
      get_ax_index_value =
        ruleTrans get_ax_index_eq
          (ruleTrans (cong1 Fst Snd_sP_to_Y) Fst_Y)

      get_ax_extra_eq = get_ax_extra_at_pi P_outer (ap1 Snd prev)
      Snd_Y = axSnd (natCode N9) extra
      get_ax_extra_value :
        Deriv (eqF (ap1 get_ax_extra stateP) extra)
      get_ax_extra_value =
        ruleTrans get_ax_extra_eq
          (ruleTrans (cong1 Snd Snd_sP_to_Y) Snd_Y)

      n0 = isAxOf_at_neq_O zero N9 w0 stateP get_ax_index_value
      n1 = isAxOf_at_neq_O (suc zero) N9 w1 stateP get_ax_index_value
      n2 = isAxOf_at_neq_O (suc (suc zero)) N9 w2 stateP get_ax_index_value
      n3 = isAxOf_at_neq_O (suc (suc (suc zero))) N9 w3 stateP get_ax_index_value
      n4 = isAxOf_at_neq_O (suc (suc (suc (suc zero)))) N9 w4 stateP get_ax_index_value
      n5 = isAxOf_at_neq_O (suc (suc (suc (suc (suc zero))))) N9 w5 stateP get_ax_index_value
      n6 = isAxOf_at_neq_O (suc (suc (suc (suc (suc (suc zero)))))) N9 w6 stateP get_ax_index_value
      n7 = isAxOf_at_neq_O (suc (suc (suc (suc (suc (suc (suc zero))))))) N9 w7 stateP get_ax_index_value
      n8 = isAxOf_at_neq_O (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) N9 w8 stateP get_ax_index_value
      n9s = isAxOf_at_eq_sO N9 stateP get_ax_index_value

      d0 = skipAt0 stateP n0
      d1 = skipAt1 stateP n1
      d2 = skipAt2 stateP n2
      d3 = skipAt3 stateP n3
      d4 = skipAt4 stateP n4
      d5 = skipAt5 stateP n5
      d6 = skipAt6 stateP n6
      d7 = skipAt7 stateP n7
      d8 = skipAt8 stateP n8
      d9 = landAt9 stateP n9s
      r8 = ruleTrans d8 d9
      r7 = ruleTrans d7 r8
      r6 = ruleTrans d6 r7
      r5 = ruleTrans d5 r6
      r4 = ruleTrans d4 r5
      r3 = ruleTrans d3 r4
      r2 = ruleTrans d2 r3
      r1 = ruleTrans d1 r2
      axBranch_to_branch9 = ruleTrans d0 r1

      axBranch9_eval = axBranch9_value stateP

      ge_eq = get_ax_extra_value
      GE = ap1 get_ax_extra stateP

      cong_Snd : Deriv (eqF (ap1 Snd GE) (ap1 Snd extra))
      cong_Snd = cong1 Snd ge_eq
      cong_FstSnd : Deriv (eqF (ap1 Fst (ap1 Snd GE)) (ap1 Fst (ap1 Snd extra)))
      cong_FstSnd = cong1 Fst cong_Snd

      -- LHS subst : pi extra (pi V0 O) -> pi extra' (pi V0 O), wrapped in tag_ap2.
      cong_GE_pair :
        Deriv (eqF (ap2 pi GE (ap2 pi cV0 O)) (ap2 pi extra (ap2 pi cV0 O)))
      cong_GE_pair = congL pi (ap2 pi cV0 O) ge_eq
      cong_LHS :
        Deriv (eqF (ap2 pi (natCode tag_ap2) (ap2 pi GE (ap2 pi cV0 O)))
                    (ap2 pi (natCode tag_ap2) (ap2 pi extra (ap2 pi cV0 O))))
      cong_LHS = congR pi (natCode tag_ap2) cong_GE_pair

      cong_G_V0 :
        Deriv (eqF (ap2 pi (ap1 Fst (ap1 Snd GE)) cV0)
                    (ap2 pi (ap1 Fst (ap1 Snd extra)) cV0))
      cong_G_V0 = congL pi cV0 cong_FstSnd
      cong_RHS :
        Deriv (eqF (ap2 pi (natCode tag_ap1) (ap2 pi (ap1 Fst (ap1 Snd GE)) cV0))
                    (ap2 pi (natCode tag_ap1) (ap2 pi (ap1 Fst (ap1 Snd extra)) cV0)))
      cong_RHS = congR pi (natCode tag_ap1) cong_G_V0

      cong_pair_LR :
        Deriv (eqF (ap2 pi (ap2 pi (natCode tag_ap2) (ap2 pi GE (ap2 pi cV0 O)))
                            (ap2 pi (natCode tag_ap1) (ap2 pi (ap1 Fst (ap1 Snd GE)) cV0)))
                    (ap2 pi (ap2 pi (natCode tag_ap2) (ap2 pi extra (ap2 pi cV0 O)))
                            (ap2 pi (natCode tag_ap1) (ap2 pi (ap1 Fst (ap1 Snd extra)) cV0))))
      cong_pair_LR = ruleTrans (congL pi _ cong_LHS) (congR pi _ cong_RHS)

      final_subst :
        Deriv (eqF (outputRHS GE) (outputRHS extra))
      final_subst = congR pi (natCode tag_eq) cong_pair_LR

      chain_to_axBranch = ruleTrans chain_to_stepBody stepBody_to_axBranch
      chain_to_branch9 = ruleTrans chain_to_axBranch axBranch_to_branch9
      chain_to_eval = ruleTrans chain_to_branch9 axBranch9_eval
  in ruleTrans chain_to_eval final_subst
