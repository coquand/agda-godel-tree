{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.ThmTAtAx10 -- axiom 10 (R_step) :
--   R g h1 h2 (v0, s v1) = h1 (h2 (v0, v1)) (R g h1 h2 (v0, v1)) .
-- extra = codeFun2 (R g h1 h2) = pi tag_R (pi codeG (pi codeH1 codeH2)).

module BRA4.ThmTAtAx10 where

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
  N10 : Nat
  N10 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))

  cV0 : Term
  cV0 = ap2 pi (natCode tag_var) (natCode zero)

  cV1 : Term
  cV1 = ap2 pi (natCode tag_var) (natCode (suc zero))

  -- codeTerm (ap1 s v1) = pi tag_ap1 (pi tag_s V1).
  codeS_V1 : Term
  codeS_V1 = ap2 pi (natCode tag_ap1) (ap2 pi (natCode tag_s) cV1)

  outputRHS : Term -> Term
  outputRHS extra =
    let H1 = ap1 Fst (ap1 Snd (ap1 Snd extra))
        H2 = ap1 Snd (ap1 Snd (ap1 Snd extra))
        codeLHS = ap2 pi (natCode tag_ap2) (ap2 pi extra (ap2 pi cV0 codeS_V1))
        codeH2v0v1 = ap2 pi (natCode tag_ap2) (ap2 pi H2 (ap2 pi cV0 cV1))
        codeR_v0v1 = ap2 pi (natCode tag_ap2) (ap2 pi extra (ap2 pi cV0 cV1))
        codeRHS = ap2 pi (natCode tag_ap2) (ap2 pi H1 (ap2 pi codeH2v0v1 codeR_v0v1))
    in ap2 pi (natCode tag_eq) (ap2 pi codeLHS codeRHS)

  mkW : (M : Nat) -> Eq (natEq M N10) false -> NatNeqWitness N10 M
  mkW M pf = natEqFalse_to_witness M N10 pf

  w0 = mkW zero refl
  w1 = mkW (suc zero) refl
  w2 = mkW (suc (suc zero)) refl
  w3 = mkW (suc (suc (suc zero))) refl
  w4 = mkW (suc (suc (suc (suc zero)))) refl
  w5 = mkW (suc (suc (suc (suc (suc zero))))) refl
  w6 = mkW (suc (suc (suc (suc (suc (suc zero)))))) refl
  w7 = mkW (suc (suc (suc (suc (suc (suc (suc zero))))))) refl
  w8 = mkW (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) refl
  w9 = mkW (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) refl

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

------------------------------------------------------------------------
-- axBranch10 evaluation.
-- axBranch10 = C pi (constN tag_eq)
--             (C pi (C pi (constN tag_ap2)
--                          (C pi get_ax_extra
--                                (C pi V0_F1 (C pi (constN tag_ap1) (C pi (constN tag_s) V1_F1)))))
--                   (C pi (constN tag_ap2)
--                         (C pi get_extra_h1_after_tag
--                               (C pi (C pi (constN tag_ap2) (C pi get_extra_h2_after_tag (C pi V0_F1 V1_F1)))
--                                     (C pi (constN tag_ap2) (C pi get_ax_extra (C pi V0_F1 V1_F1)))))))

axBranch10_value :
  (input : Term) ->
  Deriv (eqF (ap1 axBranch10 input) (outputRHS (ap1 get_ax_extra input)))
axBranch10_value input =
  let V0_eval = V0_F1_value input
      V1_eval = V1_F1_value input
      GE = ap1 get_ax_extra input
      H1 = ap1 Fst (ap1 Snd (ap1 Snd GE))
      H2 = ap1 Snd (ap1 Snd (ap1 Snd GE))

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

      -- LHS computation.
      -- C pi (constN tag_s) V1_F1 input = pi tag_s V1.
      pi_s_V1 :
        Deriv (eqF (ap1 (C pi (constN tag_s) V1_F1) input)
                    (ap2 pi (natCode tag_s) cV1))
      pi_s_V1 =
        ruleTrans (ax_C pi (constN tag_s) V1_F1 input)
          (ruleTrans (congL pi (ap1 V1_F1 input) (constN_eq tag_s input))
                     (congR pi (natCode tag_s) V1_eval))

      -- C pi (constN tag_ap1) (C pi (constN tag_s) V1_F1) input = codeS_V1.
      codeS_V1_eq :
        Deriv (eqF (ap1 (C pi (constN tag_ap1) (C pi (constN tag_s) V1_F1)) input) codeS_V1)
      codeS_V1_eq =
        ruleTrans (ax_C pi (constN tag_ap1) (C pi (constN tag_s) V1_F1) input)
          (ruleTrans (congL pi _ (constN_eq tag_ap1 input))
                     (congR pi (natCode tag_ap1) pi_s_V1))

      -- C pi V0_F1 <codeS_V1_eq> input = pi V0 codeS_V1.
      pi_V0_sV1 :
        Deriv (eqF (ap1 (C pi V0_F1 (C pi (constN tag_ap1) (C pi (constN tag_s) V1_F1))) input)
                    (ap2 pi cV0 codeS_V1))
      pi_V0_sV1 =
        ruleTrans (ax_C pi V0_F1 (C pi (constN tag_ap1) (C pi (constN tag_s) V1_F1)) input)
          (ruleTrans (congL pi _ V0_eval) (congR pi cV0 codeS_V1_eq))

      -- C pi get_ax_extra <pi_V0_sV1> input = pi GE (pi V0 codeS_V1).
      pi_GE_lhs :
        Deriv (eqF (ap1 (C pi get_ax_extra
                              (C pi V0_F1 (C pi (constN tag_ap1) (C pi (constN tag_s) V1_F1)))) input)
                    (ap2 pi GE (ap2 pi cV0 codeS_V1)))
      pi_GE_lhs =
        ruleTrans (ax_C pi get_ax_extra
                           (C pi V0_F1 (C pi (constN tag_ap1) (C pi (constN tag_s) V1_F1))) input)
          (congR pi GE pi_V0_sV1)

      codeLHS_eq :
        Deriv (eqF (ap1 (C pi (constN tag_ap2)
                              (C pi get_ax_extra
                                    (C pi V0_F1 (C pi (constN tag_ap1) (C pi (constN tag_s) V1_F1))))) input)
                    (ap2 pi (natCode tag_ap2) (ap2 pi GE (ap2 pi cV0 codeS_V1))))
      codeLHS_eq =
        ruleTrans (ax_C pi (constN tag_ap2)
                           (C pi get_ax_extra
                                 (C pi V0_F1 (C pi (constN tag_ap1) (C pi (constN tag_s) V1_F1)))) input)
          (ruleTrans (congL pi _ (constN_eq tag_ap2 input))
                     (congR pi (natCode tag_ap2) pi_GE_lhs))

      -- RHS computation.
      -- C pi V0_F1 V1_F1 input = pi V0 V1.
      pi_V0_V1 :
        Deriv (eqF (ap1 (C pi V0_F1 V1_F1) input) (ap2 pi cV0 cV1))
      pi_V0_V1 =
        ruleTrans (ax_C pi V0_F1 V1_F1 input)
          (ruleTrans (congL pi (ap1 V1_F1 input) V0_eval) (congR pi cV0 V1_eval))

      -- C pi get_extra_h2_after_tag (C pi V0_F1 V1_F1) input = pi H2 (pi V0 V1).
      pi_H2_V0V1 :
        Deriv (eqF (ap1 (C pi get_extra_h2_after_tag (C pi V0_F1 V1_F1)) input)
                    (ap2 pi H2 (ap2 pi cV0 cV1)))
      pi_H2_V0V1 =
        ruleTrans (ax_C pi get_extra_h2_after_tag (C pi V0_F1 V1_F1) input)
          (ruleTrans (congL pi _ get_h2_eq) (congR pi H2 pi_V0_V1))

      -- codeH2_v0v1.
      codeH2_v0v1_eq :
        Deriv (eqF (ap1 (C pi (constN tag_ap2)
                              (C pi get_extra_h2_after_tag (C pi V0_F1 V1_F1))) input)
                    (ap2 pi (natCode tag_ap2) (ap2 pi H2 (ap2 pi cV0 cV1))))
      codeH2_v0v1_eq =
        ruleTrans (ax_C pi (constN tag_ap2)
                           (C pi get_extra_h2_after_tag (C pi V0_F1 V1_F1)) input)
          (ruleTrans (congL pi _ (constN_eq tag_ap2 input))
                     (congR pi (natCode tag_ap2) pi_H2_V0V1))

      -- C pi get_ax_extra (C pi V0_F1 V1_F1) input = pi GE (pi V0 V1).
      pi_GE_V0V1 :
        Deriv (eqF (ap1 (C pi get_ax_extra (C pi V0_F1 V1_F1)) input)
                    (ap2 pi GE (ap2 pi cV0 cV1)))
      pi_GE_V0V1 =
        ruleTrans (ax_C pi get_ax_extra (C pi V0_F1 V1_F1) input)
          (congR pi GE pi_V0_V1)

      codeR_v0v1_eq :
        Deriv (eqF (ap1 (C pi (constN tag_ap2) (C pi get_ax_extra (C pi V0_F1 V1_F1))) input)
                    (ap2 pi (natCode tag_ap2) (ap2 pi GE (ap2 pi cV0 cV1))))
      codeR_v0v1_eq =
        ruleTrans (ax_C pi (constN tag_ap2) (C pi get_ax_extra (C pi V0_F1 V1_F1)) input)
          (ruleTrans (congL pi _ (constN_eq tag_ap2 input))
                     (congR pi (natCode tag_ap2) pi_GE_V0V1))

      -- C pi <codeH2_v0v1_eq> <codeR_v0v1_eq>.
      pair_H2_R :
        Deriv (eqF (ap1 (C pi (C pi (constN tag_ap2)
                                    (C pi get_extra_h2_after_tag (C pi V0_F1 V1_F1)))
                              (C pi (constN tag_ap2) (C pi get_ax_extra (C pi V0_F1 V1_F1)))) input)
                    (ap2 pi (ap2 pi (natCode tag_ap2) (ap2 pi H2 (ap2 pi cV0 cV1)))
                            (ap2 pi (natCode tag_ap2) (ap2 pi GE (ap2 pi cV0 cV1)))))
      pair_H2_R =
        ruleTrans (ax_C pi (C pi (constN tag_ap2)
                                  (C pi get_extra_h2_after_tag (C pi V0_F1 V1_F1)))
                            (C pi (constN tag_ap2) (C pi get_ax_extra (C pi V0_F1 V1_F1))) input)
          (ruleTrans (congL pi _ codeH2_v0v1_eq) (congR pi _ codeR_v0v1_eq))

      -- C pi get_extra_h1_after_tag <pair_H2_R>.
      pi_H1_pair :
        Deriv (eqF (ap1 (C pi get_extra_h1_after_tag
                              (C pi (C pi (constN tag_ap2)
                                          (C pi get_extra_h2_after_tag (C pi V0_F1 V1_F1)))
                                    (C pi (constN tag_ap2) (C pi get_ax_extra (C pi V0_F1 V1_F1))))) input)
                    (ap2 pi H1
                            (ap2 pi (ap2 pi (natCode tag_ap2) (ap2 pi H2 (ap2 pi cV0 cV1)))
                                    (ap2 pi (natCode tag_ap2) (ap2 pi GE (ap2 pi cV0 cV1))))))
      pi_H1_pair =
        ruleTrans (ax_C pi get_extra_h1_after_tag
                           (C pi (C pi (constN tag_ap2)
                                       (C pi get_extra_h2_after_tag (C pi V0_F1 V1_F1)))
                                 (C pi (constN tag_ap2) (C pi get_ax_extra (C pi V0_F1 V1_F1)))) input)
          (ruleTrans (congL pi _ get_h1_eq) (congR pi H1 pair_H2_R))

      codeRHS_eq :
        Deriv (eqF (ap1 (C pi (constN tag_ap2)
                              (C pi get_extra_h1_after_tag
                                    (C pi (C pi (constN tag_ap2)
                                                (C pi get_extra_h2_after_tag (C pi V0_F1 V1_F1)))
                                          (C pi (constN tag_ap2) (C pi get_ax_extra (C pi V0_F1 V1_F1)))))) input)
                    (ap2 pi (natCode tag_ap2)
                            (ap2 pi H1
                                    (ap2 pi (ap2 pi (natCode tag_ap2) (ap2 pi H2 (ap2 pi cV0 cV1)))
                                            (ap2 pi (natCode tag_ap2) (ap2 pi GE (ap2 pi cV0 cV1)))))))
      codeRHS_eq =
        ruleTrans (ax_C pi (constN tag_ap2)
                           (C pi get_extra_h1_after_tag
                                 (C pi (C pi (constN tag_ap2)
                                             (C pi get_extra_h2_after_tag (C pi V0_F1 V1_F1)))
                                       (C pi (constN tag_ap2) (C pi get_ax_extra (C pi V0_F1 V1_F1))))) input)
          (ruleTrans (congL pi _ (constN_eq tag_ap2 input))
                     (congR pi (natCode tag_ap2) pi_H1_pair))

      pair_LR :
        Deriv (eqF (ap1 (C pi (C pi (constN tag_ap2)
                                    (C pi get_ax_extra
                                          (C pi V0_F1 (C pi (constN tag_ap1) (C pi (constN tag_s) V1_F1)))))
                              (C pi (constN tag_ap2)
                                    (C pi get_extra_h1_after_tag
                                          (C pi (C pi (constN tag_ap2)
                                                      (C pi get_extra_h2_after_tag (C pi V0_F1 V1_F1)))
                                                (C pi (constN tag_ap2) (C pi get_ax_extra (C pi V0_F1 V1_F1))))))) input)
                    (ap2 pi (ap2 pi (natCode tag_ap2) (ap2 pi GE (ap2 pi cV0 codeS_V1)))
                            (ap2 pi (natCode tag_ap2)
                                    (ap2 pi H1
                                            (ap2 pi (ap2 pi (natCode tag_ap2) (ap2 pi H2 (ap2 pi cV0 cV1)))
                                                    (ap2 pi (natCode tag_ap2) (ap2 pi GE (ap2 pi cV0 cV1))))))))
      pair_LR =
        ruleTrans (ax_C pi (C pi (constN tag_ap2)
                                  (C pi get_ax_extra
                                        (C pi V0_F1 (C pi (constN tag_ap1) (C pi (constN tag_s) V1_F1)))))
                            (C pi (constN tag_ap2)
                                  (C pi get_extra_h1_after_tag
                                        (C pi (C pi (constN tag_ap2)
                                                    (C pi get_extra_h2_after_tag (C pi V0_F1 V1_F1)))
                                              (C pi (constN tag_ap2) (C pi get_ax_extra (C pi V0_F1 V1_F1)))))) input)
          (ruleTrans (congL pi _ codeLHS_eq) (congR pi _ codeRHS_eq))

  in ruleTrans (ax_C pi (constN tag_eq)
                       (C pi (C pi (constN tag_ap2)
                                    (C pi get_ax_extra
                                          (C pi V0_F1 (C pi (constN tag_ap1) (C pi (constN tag_s) V1_F1)))))
                             (C pi (constN tag_ap2)
                                   (C pi get_extra_h1_after_tag
                                         (C pi (C pi (constN tag_ap2)
                                                     (C pi get_extra_h2_after_tag (C pi V0_F1 V1_F1)))
                                               (C pi (constN tag_ap2) (C pi get_ax_extra (C pi V0_F1 V1_F1))))))) input)
       (ruleTrans (congL pi _ (constN_eq tag_eq input))
                  (congR pi (natCode tag_eq) pair_LR))

------------------------------------------------------------------------
thmT_at_axN10 :
  (extra : Term) ->
  Deriv (eqF (ap1 thmT (ap2 pi (natCode tag_ax) (ap2 pi (natCode N10) extra)))
              (outputRHS extra))
thmT_at_axN10 extra =
  let input : Term
      input = ap2 pi (natCode tag_ax) (ap2 pi (natCode N10) extra)
      Y_body : Term
      Y_body = ap2 pi (natCode N10) extra
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
      Fst_Y = axFst (natCode N10) extra

      get_ax_index_value :
        Deriv (eqF (ap1 get_ax_index stateP) (natCode N10))
      get_ax_index_value =
        ruleTrans get_ax_index_eq
          (ruleTrans (cong1 Fst Snd_sP_to_Y) Fst_Y)

      get_ax_extra_eq = get_ax_extra_at_pi P_outer (ap1 Snd prev)
      Snd_Y = axSnd (natCode N10) extra
      get_ax_extra_value :
        Deriv (eqF (ap1 get_ax_extra stateP) extra)
      get_ax_extra_value =
        ruleTrans get_ax_extra_eq
          (ruleTrans (cong1 Snd Snd_sP_to_Y) Snd_Y)

      n0 = isAxOf_at_neq_O zero N10 w0 stateP get_ax_index_value
      n1 = isAxOf_at_neq_O (suc zero) N10 w1 stateP get_ax_index_value
      n2 = isAxOf_at_neq_O (suc (suc zero)) N10 w2 stateP get_ax_index_value
      n3 = isAxOf_at_neq_O (suc (suc (suc zero))) N10 w3 stateP get_ax_index_value
      n4 = isAxOf_at_neq_O (suc (suc (suc (suc zero)))) N10 w4 stateP get_ax_index_value
      n5 = isAxOf_at_neq_O (suc (suc (suc (suc (suc zero))))) N10 w5 stateP get_ax_index_value
      n6 = isAxOf_at_neq_O (suc (suc (suc (suc (suc (suc zero)))))) N10 w6 stateP get_ax_index_value
      n7 = isAxOf_at_neq_O (suc (suc (suc (suc (suc (suc (suc zero))))))) N10 w7 stateP get_ax_index_value
      n8 = isAxOf_at_neq_O (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) N10 w8 stateP get_ax_index_value
      n9 = isAxOf_at_neq_O (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) N10 w9 stateP get_ax_index_value
      n10s = isAxOf_at_eq_sO N10 stateP get_ax_index_value

      d0 = skipAt0 stateP n0
      d1 = skipAt1 stateP n1
      d2 = skipAt2 stateP n2
      d3 = skipAt3 stateP n3
      d4 = skipAt4 stateP n4
      d5 = skipAt5 stateP n5
      d6 = skipAt6 stateP n6
      d7 = skipAt7 stateP n7
      d8 = skipAt8 stateP n8
      d9 = skipAt9 stateP n9
      d10 = landAt10 stateP n10s
      r9 = ruleTrans d9 d10
      r8 = ruleTrans d8 r9
      r7 = ruleTrans d7 r8
      r6 = ruleTrans d6 r7
      r5 = ruleTrans d5 r6
      r4 = ruleTrans d4 r5
      r3 = ruleTrans d3 r4
      r2 = ruleTrans d2 r3
      r1 = ruleTrans d1 r2
      axBranch_to_branch10 = ruleTrans d0 r1

      axBranch10_eval = axBranch10_value stateP

      ge_eq = get_ax_extra_value
      GE = ap1 get_ax_extra stateP

      H1old = ap1 Fst (ap1 Snd (ap1 Snd GE))
      H2old = ap1 Snd (ap1 Snd (ap1 Snd GE))
      H1new = ap1 Fst (ap1 Snd (ap1 Snd extra))
      H2new = ap1 Snd (ap1 Snd (ap1 Snd extra))

      cong_Snd : Deriv (eqF (ap1 Snd GE) (ap1 Snd extra))
      cong_Snd = cong1 Snd ge_eq
      cong_SS : Deriv (eqF (ap1 Snd (ap1 Snd GE)) (ap1 Snd (ap1 Snd extra)))
      cong_SS = cong1 Snd cong_Snd
      cong_H1 : Deriv (eqF H1old H1new)
      cong_H1 = cong1 Fst cong_SS
      cong_H2 : Deriv (eqF H2old H2new)
      cong_H2 = cong1 Snd cong_SS

      -- Substitute outputRHS GE -> outputRHS extra via congruence.
      cong_GE_at : (Y : Term) -> Deriv (eqF (ap2 pi GE Y) (ap2 pi extra Y))
      cong_GE_at Y = congL pi Y ge_eq

      cong_LHS_inner : Deriv (eqF (ap2 pi GE (ap2 pi cV0 codeS_V1))
                                   (ap2 pi extra (ap2 pi cV0 codeS_V1)))
      cong_LHS_inner = cong_GE_at (ap2 pi cV0 codeS_V1)
      cong_LHS_wrap :
        Deriv (eqF (ap2 pi (natCode tag_ap2) (ap2 pi GE (ap2 pi cV0 codeS_V1)))
                    (ap2 pi (natCode tag_ap2) (ap2 pi extra (ap2 pi cV0 codeS_V1))))
      cong_LHS_wrap = congR pi (natCode tag_ap2) cong_LHS_inner

      -- pi H2old V0V1 -> pi H2new V0V1.
      cong_H2_v0v1 :
        Deriv (eqF (ap2 pi H2old (ap2 pi cV0 cV1))
                    (ap2 pi H2new (ap2 pi cV0 cV1)))
      cong_H2_v0v1 = congL pi (ap2 pi cV0 cV1) cong_H2

      cong_codeH2_v0v1 :
        Deriv (eqF (ap2 pi (natCode tag_ap2) (ap2 pi H2old (ap2 pi cV0 cV1)))
                    (ap2 pi (natCode tag_ap2) (ap2 pi H2new (ap2 pi cV0 cV1))))
      cong_codeH2_v0v1 = congR pi (natCode tag_ap2) cong_H2_v0v1

      -- pi GE V0V1 -> pi extra V0V1.
      cong_GE_v0v1 :
        Deriv (eqF (ap2 pi GE (ap2 pi cV0 cV1)) (ap2 pi extra (ap2 pi cV0 cV1)))
      cong_GE_v0v1 = cong_GE_at (ap2 pi cV0 cV1)
      cong_codeR :
        Deriv (eqF (ap2 pi (natCode tag_ap2) (ap2 pi GE (ap2 pi cV0 cV1)))
                    (ap2 pi (natCode tag_ap2) (ap2 pi extra (ap2 pi cV0 cV1))))
      cong_codeR = congR pi (natCode tag_ap2) cong_GE_v0v1

      cong_pair_inner :
        Deriv (eqF (ap2 pi (ap2 pi (natCode tag_ap2) (ap2 pi H2old (ap2 pi cV0 cV1)))
                            (ap2 pi (natCode tag_ap2) (ap2 pi GE (ap2 pi cV0 cV1))))
                    (ap2 pi (ap2 pi (natCode tag_ap2) (ap2 pi H2new (ap2 pi cV0 cV1)))
                            (ap2 pi (natCode tag_ap2) (ap2 pi extra (ap2 pi cV0 cV1)))))
      cong_pair_inner =
        ruleTrans (congL pi _ cong_codeH2_v0v1) (congR pi _ cong_codeR)

      cong_H1_pair :
        Deriv (eqF (ap2 pi H1old
                            (ap2 pi (ap2 pi (natCode tag_ap2) (ap2 pi H2old (ap2 pi cV0 cV1)))
                                    (ap2 pi (natCode tag_ap2) (ap2 pi GE (ap2 pi cV0 cV1)))))
                    (ap2 pi H1new
                            (ap2 pi (ap2 pi (natCode tag_ap2) (ap2 pi H2new (ap2 pi cV0 cV1)))
                                    (ap2 pi (natCode tag_ap2) (ap2 pi extra (ap2 pi cV0 cV1))))))
      cong_H1_pair =
        ruleTrans (congL pi _ cong_H1) (congR pi H1new cong_pair_inner)

      cong_RHS :
        Deriv (eqF (ap2 pi (natCode tag_ap2)
                            (ap2 pi H1old
                                    (ap2 pi (ap2 pi (natCode tag_ap2) (ap2 pi H2old (ap2 pi cV0 cV1)))
                                            (ap2 pi (natCode tag_ap2) (ap2 pi GE (ap2 pi cV0 cV1))))))
                    (ap2 pi (natCode tag_ap2)
                            (ap2 pi H1new
                                    (ap2 pi (ap2 pi (natCode tag_ap2) (ap2 pi H2new (ap2 pi cV0 cV1)))
                                            (ap2 pi (natCode tag_ap2) (ap2 pi extra (ap2 pi cV0 cV1)))))))
      cong_RHS = congR pi (natCode tag_ap2) cong_H1_pair

      cong_pair_LR :
        Deriv (eqF (ap2 pi (ap2 pi (natCode tag_ap2) (ap2 pi GE (ap2 pi cV0 codeS_V1)))
                            (ap2 pi (natCode tag_ap2)
                                    (ap2 pi H1old
                                            (ap2 pi (ap2 pi (natCode tag_ap2) (ap2 pi H2old (ap2 pi cV0 cV1)))
                                                    (ap2 pi (natCode tag_ap2) (ap2 pi GE (ap2 pi cV0 cV1)))))))
                    (ap2 pi (ap2 pi (natCode tag_ap2) (ap2 pi extra (ap2 pi cV0 codeS_V1)))
                            (ap2 pi (natCode tag_ap2)
                                    (ap2 pi H1new
                                            (ap2 pi (ap2 pi (natCode tag_ap2) (ap2 pi H2new (ap2 pi cV0 cV1)))
                                                    (ap2 pi (natCode tag_ap2) (ap2 pi extra (ap2 pi cV0 cV1))))))))
      cong_pair_LR = ruleTrans (congL pi _ cong_LHS_wrap) (congR pi _ cong_RHS)

      final_subst :
        Deriv (eqF (outputRHS GE) (outputRHS extra))
      final_subst = congR pi (natCode tag_eq) cong_pair_LR

      chain_to_axBranch = ruleTrans chain_to_stepBody stepBody_to_axBranch
      chain_to_branch10 = ruleTrans chain_to_axBranch axBranch_to_branch10
      chain_to_eval = ruleTrans chain_to_branch10 axBranch10_eval
  in ruleTrans chain_to_eval final_subst
