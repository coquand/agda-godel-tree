{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.ThmTAtAx8 -- axiom 8 :  C g h1 h2 (v0) = g (h1 v0) (h2 v0) .
-- extra = codeFun1 (C g h1 h2) = pi tag_C (pi codeG (pi codeH1 codeH2)).

module BRA4.ThmTAtAx8 where

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
  N8 : Nat
  N8 = suc (suc (suc (suc (suc (suc (suc (suc zero)))))))

  cV0 : Term
  cV0 = ap2 pi (natCode tag_var) (natCode zero)

  -- Output RHS, parametric on extra.
  --   pi 10 (pi (pi 2 (pi extra V0))
  --             (pi 3 (pi (Fst (Snd extra))
  --                       (pi (pi 2 (pi (Fst (Snd (Snd extra))) V0))
  --                           (pi 2 (pi (Snd (Snd (Snd extra))) V0))))))
  outputRHS : Term -> Term
  outputRHS extra =
    let G = ap1 Fst (ap1 Snd extra)
        H1 = ap1 Fst (ap1 Snd (ap1 Snd extra))
        H2 = ap1 Snd (ap1 Snd (ap1 Snd extra))
        codeLHS = ap2 pi (natCode tag_ap1) (ap2 pi extra cV0)
        codeH1V0 = ap2 pi (natCode tag_ap1) (ap2 pi H1 cV0)
        codeH2V0 = ap2 pi (natCode tag_ap1) (ap2 pi H2 cV0)
        codeRHS = ap2 pi (natCode tag_ap2) (ap2 pi G (ap2 pi codeH1V0 codeH2V0))
    in ap2 pi (natCode tag_eq) (ap2 pi codeLHS codeRHS)

  witness80 : NatNeqWitness N8 zero
  witness80 = natEqFalse_to_witness zero N8 refl
  witness81 : NatNeqWitness N8 (suc zero)
  witness81 = natEqFalse_to_witness (suc zero) N8 refl
  witness82 : NatNeqWitness N8 (suc (suc zero))
  witness82 = natEqFalse_to_witness (suc (suc zero)) N8 refl
  witness83 : NatNeqWitness N8 (suc (suc (suc zero)))
  witness83 = natEqFalse_to_witness (suc (suc (suc zero))) N8 refl
  witness84 : NatNeqWitness N8 (suc (suc (suc (suc zero))))
  witness84 = natEqFalse_to_witness (suc (suc (suc (suc zero)))) N8 refl
  witness85 : NatNeqWitness N8 (suc (suc (suc (suc (suc zero)))))
  witness85 = natEqFalse_to_witness (suc (suc (suc (suc (suc zero))))) N8 refl
  witness86 : NatNeqWitness N8 (suc (suc (suc (suc (suc (suc zero))))))
  witness86 = natEqFalse_to_witness (suc (suc (suc (suc (suc (suc zero)))))) N8 refl
  witness87 : NatNeqWitness N8 (suc (suc (suc (suc (suc (suc (suc zero)))))))
  witness87 = natEqFalse_to_witness (suc (suc (suc (suc (suc (suc (suc zero))))))) N8 refl

V0_F1_value :
  (input : Term) -> Deriv (eqF (ap1 V0_F1 input) cV0)
V0_F1_value input =
  ruleTrans (ax_C pi (constN tag_var) (constN zero) input)
    (ruleTrans (congL pi (ap1 (constN zero) input) (constN_eq tag_var input))
               (congR pi (natCode tag_var) (constN_eq zero input)))

------------------------------------------------------------------------
-- axBranch8 evaluation.
-- axBranch8 = C pi (constN tag_eq)
--             (C pi (C pi (constN tag_ap1) (C pi get_ax_extra V0_F1))
--                   (C pi (constN tag_ap2)
--                         (C pi get_extra_g_after_tag
--                               (C pi (C pi (constN tag_ap1) (C pi get_extra_h1_after_tag V0_F1))
--                                     (C pi (constN tag_ap1) (C pi get_extra_h2_after_tag V0_F1))))))

axBranch8_value :
  (input : Term) ->
  Deriv (eqF (ap1 axBranch8 input) (outputRHS (ap1 get_ax_extra input)))
axBranch8_value input =
  let V0_eval = V0_F1_value input
      GE : Term
      GE = ap1 get_ax_extra input
      G : Term
      G = ap1 Fst (ap1 Snd GE)
      H1 : Term
      H1 = ap1 Fst (ap1 Snd (ap1 Snd GE))
      H2 : Term
      H2 = ap1 Snd (ap1 Snd (ap1 Snd GE))

      -- get_extra_g_after_tag input = Fst (Snd GE).
      get_g_eq :
        Deriv (eqF (ap1 get_extra_g_after_tag input) G)
      get_g_eq =
        let s1 = compose1U_eq Fst (compose1U Snd get_ax_extra) input
            s2 = compose1U_eq Snd get_ax_extra input
        in ruleTrans s1 (cong1 Fst s2)

      get_h1_eq :
        Deriv (eqF (ap1 get_extra_h1_after_tag input) H1)
      get_h1_eq =
        let s1 = compose1U_eq Fst (compose1U Snd (compose1U Snd get_ax_extra)) input
            s2 = compose1U_eq Snd (compose1U Snd get_ax_extra) input
            s3 = compose1U_eq Snd get_ax_extra input
            inner = ruleTrans s2 (cong1 Snd s3)
        in ruleTrans s1 (cong1 Fst inner)

      get_h2_eq :
        Deriv (eqF (ap1 get_extra_h2_after_tag input) H2)
      get_h2_eq =
        let s1 = compose1U_eq Snd (compose1U Snd (compose1U Snd get_ax_extra)) input
            s2 = compose1U_eq Snd (compose1U Snd get_ax_extra) input
            s3 = compose1U_eq Snd get_ax_extra input
            inner = ruleTrans s2 (cong1 Snd s3)
        in ruleTrans s1 (cong1 Snd inner)

      -- C pi get_ax_extra V0_F1 input = pi GE V0.
      pi_GE_V0 :
        Deriv (eqF (ap1 (C pi get_ax_extra V0_F1) input) (ap2 pi GE cV0))
      pi_GE_V0 = ruleTrans (ax_C pi get_ax_extra V0_F1 input) (congR pi GE V0_eval)

      -- C pi (constN tag_ap1) (C pi get_ax_extra V0_F1) input.
      codeLHS_eq :
        Deriv (eqF (ap1 (C pi (constN tag_ap1) (C pi get_ax_extra V0_F1)) input)
                    (ap2 pi (natCode tag_ap1) (ap2 pi GE cV0)))
      codeLHS_eq =
        ruleTrans (ax_C pi (constN tag_ap1) (C pi get_ax_extra V0_F1) input)
          (ruleTrans (congL pi _ (constN_eq tag_ap1 input))
                     (congR pi (natCode tag_ap1) pi_GE_V0))

      -- C pi get_extra_h1_after_tag V0_F1 input = pi H1 V0.
      pi_H1_V0 :
        Deriv (eqF (ap1 (C pi get_extra_h1_after_tag V0_F1) input) (ap2 pi H1 cV0))
      pi_H1_V0 =
        ruleTrans (ax_C pi get_extra_h1_after_tag V0_F1 input)
          (ruleTrans (congL pi (ap1 V0_F1 input) get_h1_eq) (congR pi H1 V0_eval))

      pi_H2_V0 :
        Deriv (eqF (ap1 (C pi get_extra_h2_after_tag V0_F1) input) (ap2 pi H2 cV0))
      pi_H2_V0 =
        ruleTrans (ax_C pi get_extra_h2_after_tag V0_F1 input)
          (ruleTrans (congL pi (ap1 V0_F1 input) get_h2_eq) (congR pi H2 V0_eval))

      -- C pi (constN tag_ap1) (C pi get_extra_h1_after_tag V0_F1) input.
      h1V0_full :
        Deriv (eqF (ap1 (C pi (constN tag_ap1) (C pi get_extra_h1_after_tag V0_F1)) input)
                    (ap2 pi (natCode tag_ap1) (ap2 pi H1 cV0)))
      h1V0_full =
        ruleTrans (ax_C pi (constN tag_ap1) (C pi get_extra_h1_after_tag V0_F1) input)
          (ruleTrans (congL pi _ (constN_eq tag_ap1 input))
                     (congR pi (natCode tag_ap1) pi_H1_V0))

      h2V0_full :
        Deriv (eqF (ap1 (C pi (constN tag_ap1) (C pi get_extra_h2_after_tag V0_F1)) input)
                    (ap2 pi (natCode tag_ap1) (ap2 pi H2 cV0)))
      h2V0_full =
        ruleTrans (ax_C pi (constN tag_ap1) (C pi get_extra_h2_after_tag V0_F1) input)
          (ruleTrans (congL pi _ (constN_eq tag_ap1 input))
                     (congR pi (natCode tag_ap1) pi_H2_V0))

      -- C pi <h1V0_full> <h2V0_full> input.
      pair_h_full :
        Deriv (eqF (ap1 (C pi (C pi (constN tag_ap1) (C pi get_extra_h1_after_tag V0_F1))
                              (C pi (constN tag_ap1) (C pi get_extra_h2_after_tag V0_F1))) input)
                    (ap2 pi (ap2 pi (natCode tag_ap1) (ap2 pi H1 cV0))
                            (ap2 pi (natCode tag_ap1) (ap2 pi H2 cV0))))
      pair_h_full =
        ruleTrans (ax_C pi (C pi (constN tag_ap1) (C pi get_extra_h1_after_tag V0_F1))
                            (C pi (constN tag_ap1) (C pi get_extra_h2_after_tag V0_F1)) input)
          (ruleTrans (congL pi _ h1V0_full)
                     (congR pi (ap2 pi (natCode tag_ap1) (ap2 pi H1 cV0)) h2V0_full))

      -- C pi get_extra_g_after_tag <pair_h_full> input.
      g_pair :
        Deriv (eqF (ap1 (C pi get_extra_g_after_tag
                              (C pi (C pi (constN tag_ap1) (C pi get_extra_h1_after_tag V0_F1))
                                    (C pi (constN tag_ap1) (C pi get_extra_h2_after_tag V0_F1)))) input)
                    (ap2 pi G
                            (ap2 pi (ap2 pi (natCode tag_ap1) (ap2 pi H1 cV0))
                                    (ap2 pi (natCode tag_ap1) (ap2 pi H2 cV0)))))
      g_pair =
        ruleTrans (ax_C pi get_extra_g_after_tag
                           (C pi (C pi (constN tag_ap1) (C pi get_extra_h1_after_tag V0_F1))
                                 (C pi (constN tag_ap1) (C pi get_extra_h2_after_tag V0_F1))) input)
          (ruleTrans (congL pi _ get_g_eq) (congR pi G pair_h_full))

      -- C pi (constN tag_ap2) <g_pair>.
      codeRHS_eq :
        Deriv (eqF (ap1 (C pi (constN tag_ap2)
                              (C pi get_extra_g_after_tag
                                    (C pi (C pi (constN tag_ap1) (C pi get_extra_h1_after_tag V0_F1))
                                          (C pi (constN tag_ap1) (C pi get_extra_h2_after_tag V0_F1))))) input)
                    (ap2 pi (natCode tag_ap2)
                            (ap2 pi G
                                    (ap2 pi (ap2 pi (natCode tag_ap1) (ap2 pi H1 cV0))
                                            (ap2 pi (natCode tag_ap1) (ap2 pi H2 cV0))))))
      codeRHS_eq =
        ruleTrans (ax_C pi (constN tag_ap2)
                           (C pi get_extra_g_after_tag
                                 (C pi (C pi (constN tag_ap1) (C pi get_extra_h1_after_tag V0_F1))
                                       (C pi (constN tag_ap1) (C pi get_extra_h2_after_tag V0_F1)))) input)
          (ruleTrans (congL pi _ (constN_eq tag_ap2 input))
                     (congR pi (natCode tag_ap2) g_pair))

      -- C pi <codeLHS_eq> <codeRHS_eq>.
      pair_LR :
        Deriv (eqF (ap1 (C pi (C pi (constN tag_ap1) (C pi get_ax_extra V0_F1))
                              (C pi (constN tag_ap2)
                                    (C pi get_extra_g_after_tag
                                          (C pi (C pi (constN tag_ap1) (C pi get_extra_h1_after_tag V0_F1))
                                                (C pi (constN tag_ap1) (C pi get_extra_h2_after_tag V0_F1)))))) input)
                    (ap2 pi (ap2 pi (natCode tag_ap1) (ap2 pi GE cV0))
                            (ap2 pi (natCode tag_ap2)
                                    (ap2 pi G
                                            (ap2 pi (ap2 pi (natCode tag_ap1) (ap2 pi H1 cV0))
                                                    (ap2 pi (natCode tag_ap1) (ap2 pi H2 cV0)))))))
      pair_LR =
        ruleTrans (ax_C pi (C pi (constN tag_ap1) (C pi get_ax_extra V0_F1))
                            (C pi (constN tag_ap2)
                                  (C pi get_extra_g_after_tag
                                        (C pi (C pi (constN tag_ap1) (C pi get_extra_h1_after_tag V0_F1))
                                              (C pi (constN tag_ap1) (C pi get_extra_h2_after_tag V0_F1))))) input)
          (ruleTrans (congL pi _ codeLHS_eq)
                     (congR pi (ap2 pi (natCode tag_ap1) (ap2 pi GE cV0)) codeRHS_eq))

  in ruleTrans (ax_C pi (constN tag_eq)
                       (C pi (C pi (constN tag_ap1) (C pi get_ax_extra V0_F1))
                             (C pi (constN tag_ap2)
                                   (C pi get_extra_g_after_tag
                                         (C pi (C pi (constN tag_ap1) (C pi get_extra_h1_after_tag V0_F1))
                                               (C pi (constN tag_ap1) (C pi get_extra_h2_after_tag V0_F1)))))) input)
       (ruleTrans (congL pi _ (constN_eq tag_eq input))
                  (congR pi (natCode tag_eq) pair_LR))

------------------------------------------------------------------------
thmT_at_axN8 :
  (extra : Term) ->
  Deriv (eqF (ap1 thmT (ap2 pi (natCode tag_ax) (ap2 pi (natCode N8) extra)))
              (outputRHS extra))
thmT_at_axN8 extra =
  let input : Term
      input = ap2 pi (natCode tag_ax) (ap2 pi (natCode N8) extra)
      Y_body : Term
      Y_body = ap2 pi (natCode N8) extra
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
      Fst_Y = axFst (natCode N8) extra

      get_ax_index_value :
        Deriv (eqF (ap1 get_ax_index stateP) (natCode N8))
      get_ax_index_value =
        ruleTrans get_ax_index_eq
          (ruleTrans (cong1 Fst Snd_sP_to_Y) Fst_Y)

      get_ax_extra_eq = get_ax_extra_at_pi P_outer (ap1 Snd prev)
      Snd_Y = axSnd (natCode N8) extra
      get_ax_extra_value :
        Deriv (eqF (ap1 get_ax_extra stateP) extra)
      get_ax_extra_value =
        ruleTrans get_ax_extra_eq
          (ruleTrans (cong1 Snd Snd_sP_to_Y) Snd_Y)

      isAx0_O = isAxOf_at_neq_O zero N8 witness80 stateP get_ax_index_value
      isAx1_O = isAxOf_at_neq_O (suc zero) N8 witness81 stateP get_ax_index_value
      isAx2_O = isAxOf_at_neq_O (suc (suc zero)) N8 witness82 stateP get_ax_index_value
      isAx3_O = isAxOf_at_neq_O (suc (suc (suc zero))) N8 witness83 stateP get_ax_index_value
      isAx4_O = isAxOf_at_neq_O (suc (suc (suc (suc zero)))) N8 witness84 stateP get_ax_index_value
      isAx5_O = isAxOf_at_neq_O (suc (suc (suc (suc (suc zero))))) N8 witness85 stateP get_ax_index_value
      isAx6_O = isAxOf_at_neq_O (suc (suc (suc (suc (suc (suc zero)))))) N8 witness86 stateP get_ax_index_value
      isAx7_O = isAxOf_at_neq_O (suc (suc (suc (suc (suc (suc (suc zero))))))) N8 witness87 stateP get_ax_index_value
      isAx8_sO = isAxOf_at_eq_sO N8 stateP get_ax_index_value

      d0 = skipAt0 stateP isAx0_O
      d1 = skipAt1 stateP isAx1_O
      d2 = skipAt2 stateP isAx2_O
      d3 = skipAt3 stateP isAx3_O
      d4 = skipAt4 stateP isAx4_O
      d5 = skipAt5 stateP isAx5_O
      d6 = skipAt6 stateP isAx6_O
      d7 = skipAt7 stateP isAx7_O
      d8 = landAt8 stateP isAx8_sO
      r7 = ruleTrans d7 d8
      r6 = ruleTrans d6 r7
      r5 = ruleTrans d5 r6
      r4 = ruleTrans d4 r5
      r3 = ruleTrans d3 r4
      r2 = ruleTrans d2 r3
      r1 = ruleTrans d1 r2
      axBranch_to_branch8 = ruleTrans d0 r1

      axBranch8_eval = axBranch8_value stateP

      ge_eq = get_ax_extra_value
      GE = ap1 get_ax_extra stateP

      -- Substitute (Fst (Snd GE)) -> Fst (Snd extra) etc., recursively.
      cong_Snd : Deriv (eqF (ap1 Snd GE) (ap1 Snd extra))
      cong_Snd = cong1 Snd ge_eq
      cong_FstSnd : Deriv (eqF (ap1 Fst (ap1 Snd GE)) (ap1 Fst (ap1 Snd extra)))
      cong_FstSnd = cong1 Fst cong_Snd
      cong_SndSnd : Deriv (eqF (ap1 Snd (ap1 Snd GE)) (ap1 Snd (ap1 Snd extra)))
      cong_SndSnd = cong1 Snd cong_Snd
      cong_FstSS : Deriv (eqF (ap1 Fst (ap1 Snd (ap1 Snd GE))) (ap1 Fst (ap1 Snd (ap1 Snd extra))))
      cong_FstSS = cong1 Fst cong_SndSnd
      cong_SndSS : Deriv (eqF (ap1 Snd (ap1 Snd (ap1 Snd GE))) (ap1 Snd (ap1 Snd (ap1 Snd extra))))
      cong_SndSS = cong1 Snd cong_SndSnd

      -- final_subst : outputRHS GE = outputRHS extra.
      -- The Term outputRHS GE has GE at one position (the codeLHS) and
      -- Fst (Snd GE), Fst (Snd (Snd GE)), Snd (Snd (Snd GE)) at the codeRHS positions.
      -- We rewrite each via congruence.

      -- pi extra V0 inside codeLHS.
      cong_LHS_inner : Deriv (eqF (ap2 pi GE cV0) (ap2 pi extra cV0))
      cong_LHS_inner = congL pi cV0 ge_eq

      cong_LHS : Deriv (eqF (ap2 pi (natCode tag_ap1) (ap2 pi GE cV0))
                             (ap2 pi (natCode tag_ap1) (ap2 pi extra cV0)))
      cong_LHS = congR pi (natCode tag_ap1) cong_LHS_inner

      -- pi H1_old V0 -> pi H1_new V0.
      cong_H1V0 :
        Deriv (eqF (ap2 pi (ap1 Fst (ap1 Snd (ap1 Snd GE))) cV0)
                    (ap2 pi (ap1 Fst (ap1 Snd (ap1 Snd extra))) cV0))
      cong_H1V0 = congL pi cV0 cong_FstSS

      cong_H1V0_wrap :
        Deriv (eqF (ap2 pi (natCode tag_ap1) (ap2 pi (ap1 Fst (ap1 Snd (ap1 Snd GE))) cV0))
                    (ap2 pi (natCode tag_ap1) (ap2 pi (ap1 Fst (ap1 Snd (ap1 Snd extra))) cV0)))
      cong_H1V0_wrap = congR pi (natCode tag_ap1) cong_H1V0

      cong_H2V0 :
        Deriv (eqF (ap2 pi (ap1 Snd (ap1 Snd (ap1 Snd GE))) cV0)
                    (ap2 pi (ap1 Snd (ap1 Snd (ap1 Snd extra))) cV0))
      cong_H2V0 = congL pi cV0 cong_SndSS

      cong_H2V0_wrap :
        Deriv (eqF (ap2 pi (natCode tag_ap1) (ap2 pi (ap1 Snd (ap1 Snd (ap1 Snd GE))) cV0))
                    (ap2 pi (natCode tag_ap1) (ap2 pi (ap1 Snd (ap1 Snd (ap1 Snd extra))) cV0)))
      cong_H2V0_wrap = congR pi (natCode tag_ap1) cong_H2V0

      -- Pair the H1V0 and H2V0 wraps.
      cong_pair_H :
        Deriv (eqF (ap2 pi (ap2 pi (natCode tag_ap1) (ap2 pi (ap1 Fst (ap1 Snd (ap1 Snd GE))) cV0))
                            (ap2 pi (natCode tag_ap1) (ap2 pi (ap1 Snd (ap1 Snd (ap1 Snd GE))) cV0)))
                    (ap2 pi (ap2 pi (natCode tag_ap1) (ap2 pi (ap1 Fst (ap1 Snd (ap1 Snd extra))) cV0))
                            (ap2 pi (natCode tag_ap1) (ap2 pi (ap1 Snd (ap1 Snd (ap1 Snd extra))) cV0))))
      cong_pair_H =
        ruleTrans (congL pi _ cong_H1V0_wrap) (congR pi _ cong_H2V0_wrap)

      -- pi G (pi <pair_H>).
      cong_g_pair :
        Deriv (eqF (ap2 pi (ap1 Fst (ap1 Snd GE))
                            (ap2 pi (ap2 pi (natCode tag_ap1) (ap2 pi (ap1 Fst (ap1 Snd (ap1 Snd GE))) cV0))
                                    (ap2 pi (natCode tag_ap1) (ap2 pi (ap1 Snd (ap1 Snd (ap1 Snd GE))) cV0))))
                    (ap2 pi (ap1 Fst (ap1 Snd extra))
                            (ap2 pi (ap2 pi (natCode tag_ap1) (ap2 pi (ap1 Fst (ap1 Snd (ap1 Snd extra))) cV0))
                                    (ap2 pi (natCode tag_ap1) (ap2 pi (ap1 Snd (ap1 Snd (ap1 Snd extra))) cV0)))))
      cong_g_pair =
        ruleTrans (congL pi _ cong_FstSnd) (congR pi (ap1 Fst (ap1 Snd extra)) cong_pair_H)

      -- pi tag_ap2 (...).
      cong_RHS :
        Deriv (eqF (ap2 pi (natCode tag_ap2)
                            (ap2 pi (ap1 Fst (ap1 Snd GE))
                                    (ap2 pi (ap2 pi (natCode tag_ap1) (ap2 pi (ap1 Fst (ap1 Snd (ap1 Snd GE))) cV0))
                                            (ap2 pi (natCode tag_ap1) (ap2 pi (ap1 Snd (ap1 Snd (ap1 Snd GE))) cV0)))))
                    (ap2 pi (natCode tag_ap2)
                            (ap2 pi (ap1 Fst (ap1 Snd extra))
                                    (ap2 pi (ap2 pi (natCode tag_ap1) (ap2 pi (ap1 Fst (ap1 Snd (ap1 Snd extra))) cV0))
                                            (ap2 pi (natCode tag_ap1) (ap2 pi (ap1 Snd (ap1 Snd (ap1 Snd extra))) cV0))))))
      cong_RHS = congR pi (natCode tag_ap2) cong_g_pair

      -- Pair LHS RHS.
      cong_pair_LR :
        Deriv (eqF (ap2 pi (ap2 pi (natCode tag_ap1) (ap2 pi GE cV0))
                            (ap2 pi (natCode tag_ap2)
                                    (ap2 pi (ap1 Fst (ap1 Snd GE))
                                            (ap2 pi (ap2 pi (natCode tag_ap1) (ap2 pi (ap1 Fst (ap1 Snd (ap1 Snd GE))) cV0))
                                                    (ap2 pi (natCode tag_ap1) (ap2 pi (ap1 Snd (ap1 Snd (ap1 Snd GE))) cV0))))))
                    (ap2 pi (ap2 pi (natCode tag_ap1) (ap2 pi extra cV0))
                            (ap2 pi (natCode tag_ap2)
                                    (ap2 pi (ap1 Fst (ap1 Snd extra))
                                            (ap2 pi (ap2 pi (natCode tag_ap1) (ap2 pi (ap1 Fst (ap1 Snd (ap1 Snd extra))) cV0))
                                                    (ap2 pi (natCode tag_ap1) (ap2 pi (ap1 Snd (ap1 Snd (ap1 Snd extra))) cV0)))))))
      cong_pair_LR =
        ruleTrans (congL pi _ cong_LHS) (congR pi _ cong_RHS)

      final_subst :
        Deriv (eqF (outputRHS GE) (outputRHS extra))
      final_subst = congR pi (natCode tag_eq) cong_pair_LR

      chain_to_axBranch = ruleTrans chain_to_stepBody stepBody_to_axBranch
      chain_to_branch8 = ruleTrans chain_to_axBranch axBranch_to_branch8
      chain_to_eval = ruleTrans chain_to_branch8 axBranch8_eval
  in ruleTrans chain_to_eval final_subst
