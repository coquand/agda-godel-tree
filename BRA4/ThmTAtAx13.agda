{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.ThmTAtAx13 -- axiom 13 (axNeg) :  (~A > ~B) > (B > A) .  extra = pi codeA codeB.

module BRA4.ThmTAtAx13 where

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
  N13 : Nat
  N13 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))

  -- outputRHS : pi tag_imp (pi (pi tag_imp (pi (pi tag_neg A) (pi tag_neg B))) (pi tag_imp (pi B A))).
  outputRHS : Term -> Term
  outputRHS extra =
    let A = ap1 Fst extra
        B = ap1 Snd extra
    in ap2 pi (natCode tag_imp)
         (ap2 pi (ap2 pi (natCode tag_imp)
                          (ap2 pi (ap2 pi (natCode tag_neg) A)
                                  (ap2 pi (natCode tag_neg) B)))
                 (ap2 pi (natCode tag_imp) (ap2 pi B A)))

  -- Witnesses 0..12 vs N13.
  mkW : (M : Nat) -> Eq (natEq M N13) false -> NatNeqWitness N13 M
  mkW M pf = natEqFalse_to_witness M N13 pf

  w0 : NatNeqWitness N13 zero
  w0 = mkW zero refl
  w1 : NatNeqWitness N13 (suc zero)
  w1 = mkW (suc zero) refl
  w2 : NatNeqWitness N13 (suc (suc zero))
  w2 = mkW (suc (suc zero)) refl
  w3 : NatNeqWitness N13 (suc (suc (suc zero)))
  w3 = mkW (suc (suc (suc zero))) refl
  w4 : NatNeqWitness N13 (suc (suc (suc (suc zero))))
  w4 = mkW (suc (suc (suc (suc zero)))) refl
  w5 : NatNeqWitness N13 (suc (suc (suc (suc (suc zero)))))
  w5 = mkW (suc (suc (suc (suc (suc zero))))) refl
  w6 : NatNeqWitness N13 (suc (suc (suc (suc (suc (suc zero))))))
  w6 = mkW (suc (suc (suc (suc (suc (suc zero)))))) refl
  w7 : NatNeqWitness N13 (suc (suc (suc (suc (suc (suc (suc zero)))))))
  w7 = mkW (suc (suc (suc (suc (suc (suc (suc zero))))))) refl
  w8 : NatNeqWitness N13 (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
  w8 = mkW (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) refl
  w9 : NatNeqWitness N13 (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
  w9 = mkW (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) refl
  w10 : NatNeqWitness N13 (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
  w10 = mkW (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) refl
  w11 : NatNeqWitness N13 (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))
  w11 = mkW (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) refl
  w12 : NatNeqWitness N13 (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))
  w12 = mkW (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))) refl

------------------------------------------------------------------------
axBranch13_value :
  (input : Term) ->
  Deriv (eqF (ap1 axBranch13 input) (outputRHS (ap1 get_ax_extra input)))
axBranch13_value input =
  let GE = ap1 get_ax_extra input
      A = ap1 Fst GE
      B = ap1 Snd GE

      get_eF_eq : Deriv (eqF (ap1 get_extra_Fst input) A)
      get_eF_eq = compose1U_eq Fst get_ax_extra input

      get_eS_eq : Deriv (eqF (ap1 get_extra_Snd input) B)
      get_eS_eq = compose1U_eq Snd get_ax_extra input

      -- C pi (constN tag_neg) get_extra_Fst input = pi tag_neg A.
      neg_A :
        Deriv (eqF (ap1 (C pi (constN tag_neg) get_extra_Fst) input)
                    (ap2 pi (natCode tag_neg) A))
      neg_A =
        ruleTrans (ax_C pi (constN tag_neg) get_extra_Fst input)
          (ruleTrans (congL pi (ap1 get_extra_Fst input) (constN_eq tag_neg input))
                     (congR pi (natCode tag_neg) get_eF_eq))

      neg_B :
        Deriv (eqF (ap1 (C pi (constN tag_neg) get_extra_Snd) input)
                    (ap2 pi (natCode tag_neg) B))
      neg_B =
        ruleTrans (ax_C pi (constN tag_neg) get_extra_Snd input)
          (ruleTrans (congL pi (ap1 get_extra_Snd input) (constN_eq tag_neg input))
                     (congR pi (natCode tag_neg) get_eS_eq))

      pair_negA_negB :
        Deriv (eqF (ap1 (C pi (C pi (constN tag_neg) get_extra_Fst)
                              (C pi (constN tag_neg) get_extra_Snd)) input)
                    (ap2 pi (ap2 pi (natCode tag_neg) A) (ap2 pi (natCode tag_neg) B)))
      pair_negA_negB =
        ruleTrans (ax_C pi (C pi (constN tag_neg) get_extra_Fst)
                            (C pi (constN tag_neg) get_extra_Snd) input)
          (ruleTrans (congL pi _ neg_A)
                     (congR pi (ap2 pi (natCode tag_neg) A) neg_B))

      -- C pi (constN tag_imp) <pair_negA_negB>.
      imp_neg :
        Deriv (eqF (ap1 (C pi (constN tag_imp)
                              (C pi (C pi (constN tag_neg) get_extra_Fst)
                                    (C pi (constN tag_neg) get_extra_Snd))) input)
                    (ap2 pi (natCode tag_imp)
                            (ap2 pi (ap2 pi (natCode tag_neg) A) (ap2 pi (natCode tag_neg) B))))
      imp_neg =
        ruleTrans (ax_C pi (constN tag_imp)
                           (C pi (C pi (constN tag_neg) get_extra_Fst)
                                 (C pi (constN tag_neg) get_extra_Snd)) input)
          (ruleTrans (congL pi _ (constN_eq tag_imp input))
                     (congR pi (natCode tag_imp) pair_negA_negB))

      -- C pi get_extra_Snd get_extra_Fst input = pi B A.
      pi_B_A :
        Deriv (eqF (ap1 (C pi get_extra_Snd get_extra_Fst) input) (ap2 pi B A))
      pi_B_A =
        ruleTrans (ax_C pi get_extra_Snd get_extra_Fst input)
          (ruleTrans (congL pi (ap1 get_extra_Fst input) get_eS_eq)
                     (congR pi B get_eF_eq))

      -- C pi (constN tag_imp) (C pi get_extra_Snd get_extra_Fst) input.
      imp_BA :
        Deriv (eqF (ap1 (C pi (constN tag_imp) (C pi get_extra_Snd get_extra_Fst)) input)
                    (ap2 pi (natCode tag_imp) (ap2 pi B A)))
      imp_BA =
        ruleTrans (ax_C pi (constN tag_imp) (C pi get_extra_Snd get_extra_Fst) input)
          (ruleTrans (congL pi _ (constN_eq tag_imp input))
                     (congR pi (natCode tag_imp) pi_B_A))

      -- C pi <imp_neg> <imp_BA>.
      pair_outer :
        Deriv (eqF (ap1 (C pi (C pi (constN tag_imp)
                                    (C pi (C pi (constN tag_neg) get_extra_Fst)
                                          (C pi (constN tag_neg) get_extra_Snd)))
                              (C pi (constN tag_imp) (C pi get_extra_Snd get_extra_Fst))) input)
                    (ap2 pi (ap2 pi (natCode tag_imp)
                                    (ap2 pi (ap2 pi (natCode tag_neg) A)
                                            (ap2 pi (natCode tag_neg) B)))
                            (ap2 pi (natCode tag_imp) (ap2 pi B A))))
      pair_outer =
        ruleTrans (ax_C pi (C pi (constN tag_imp)
                                  (C pi (C pi (constN tag_neg) get_extra_Fst)
                                        (C pi (constN tag_neg) get_extra_Snd)))
                            (C pi (constN tag_imp) (C pi get_extra_Snd get_extra_Fst)) input)
          (ruleTrans (congL pi _ imp_neg)
                     (congR pi _ imp_BA))

  in ruleTrans (ax_C pi (constN tag_imp)
                       (C pi (C pi (constN tag_imp)
                                    (C pi (C pi (constN tag_neg) get_extra_Fst)
                                          (C pi (constN tag_neg) get_extra_Snd)))
                             (C pi (constN tag_imp) (C pi get_extra_Snd get_extra_Fst))) input)
       (ruleTrans (congL pi _ (constN_eq tag_imp input))
                  (congR pi (natCode tag_imp) pair_outer))

------------------------------------------------------------------------
thmT_at_axN13 :
  (extra : Term) ->
  Deriv (eqF (ap1 thmT (ap2 pi (natCode tag_ax) (ap2 pi (natCode N13) extra)))
              (outputRHS extra))
thmT_at_axN13 extra =
  let input : Term
      input = ap2 pi (natCode tag_ax) (ap2 pi (natCode N13) extra)
      Y_body : Term
      Y_body = ap2 pi (natCode N13) extra
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
      Fst_Y = axFst (natCode N13) extra

      get_ax_index_value :
        Deriv (eqF (ap1 get_ax_index stateP) (natCode N13))
      get_ax_index_value =
        ruleTrans get_ax_index_eq
          (ruleTrans (cong1 Fst Snd_sP_to_Y) Fst_Y)

      get_ax_extra_eq = get_ax_extra_at_pi P_outer (ap1 Snd prev)
      Snd_Y = axSnd (natCode N13) extra
      get_ax_extra_value :
        Deriv (eqF (ap1 get_ax_extra stateP) extra)
      get_ax_extra_value =
        ruleTrans get_ax_extra_eq
          (ruleTrans (cong1 Snd Snd_sP_to_Y) Snd_Y)

      n0 = isAxOf_at_neq_O zero N13 w0 stateP get_ax_index_value
      n1 = isAxOf_at_neq_O (suc zero) N13 w1 stateP get_ax_index_value
      n2 = isAxOf_at_neq_O (suc (suc zero)) N13 w2 stateP get_ax_index_value
      n3 = isAxOf_at_neq_O (suc (suc (suc zero))) N13 w3 stateP get_ax_index_value
      n4 = isAxOf_at_neq_O (suc (suc (suc (suc zero)))) N13 w4 stateP get_ax_index_value
      n5 = isAxOf_at_neq_O (suc (suc (suc (suc (suc zero))))) N13 w5 stateP get_ax_index_value
      n6 = isAxOf_at_neq_O (suc (suc (suc (suc (suc (suc zero)))))) N13 w6 stateP get_ax_index_value
      n7 = isAxOf_at_neq_O (suc (suc (suc (suc (suc (suc (suc zero))))))) N13 w7 stateP get_ax_index_value
      n8 = isAxOf_at_neq_O (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) N13 w8 stateP get_ax_index_value
      n9 = isAxOf_at_neq_O (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) N13 w9 stateP get_ax_index_value
      n10 = isAxOf_at_neq_O (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) N13 w10 stateP get_ax_index_value
      n11 = isAxOf_at_neq_O (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) N13 w11 stateP get_ax_index_value
      n12 = isAxOf_at_neq_O (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))) N13 w12 stateP get_ax_index_value
      n13s = isAxOf_at_eq_sO N13 stateP get_ax_index_value

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
      d10 = skipAt10 stateP n10
      d11 = skipAt11 stateP n11
      d12 = skipAt12 stateP n12
      d13 = landAt13 stateP n13s
      r12 = ruleTrans d12 d13
      r11 = ruleTrans d11 r12
      r10 = ruleTrans d10 r11
      r9 = ruleTrans d9 r10
      r8 = ruleTrans d8 r9
      r7 = ruleTrans d7 r8
      r6 = ruleTrans d6 r7
      r5 = ruleTrans d5 r6
      r4 = ruleTrans d4 r5
      r3 = ruleTrans d3 r4
      r2 = ruleTrans d2 r3
      r1 = ruleTrans d1 r2
      axBranch_to_branch13 = ruleTrans d0 r1

      axBranch13_eval = axBranch13_value stateP

      ge_eq = get_ax_extra_value
      GE = ap1 get_ax_extra stateP

      A_old = ap1 Fst GE
      B_old = ap1 Snd GE
      A_new = ap1 Fst extra
      B_new = ap1 Snd extra
      cong_A : Deriv (eqF A_old A_new)
      cong_A = cong1 Fst ge_eq
      cong_B : Deriv (eqF B_old B_new)
      cong_B = cong1 Snd ge_eq

      -- Rewrite outputRHS GE -> outputRHS extra.
      -- pi tag_neg A_old -> pi tag_neg A_new.
      cong_negA : Deriv (eqF (ap2 pi (natCode tag_neg) A_old)
                              (ap2 pi (natCode tag_neg) A_new))
      cong_negA = congR pi (natCode tag_neg) cong_A
      cong_negB : Deriv (eqF (ap2 pi (natCode tag_neg) B_old)
                              (ap2 pi (natCode tag_neg) B_new))
      cong_negB = congR pi (natCode tag_neg) cong_B
      cong_pair_neg :
        Deriv (eqF (ap2 pi (ap2 pi (natCode tag_neg) A_old) (ap2 pi (natCode tag_neg) B_old))
                    (ap2 pi (ap2 pi (natCode tag_neg) A_new) (ap2 pi (natCode tag_neg) B_new)))
      cong_pair_neg =
        ruleTrans (congL pi _ cong_negA) (congR pi _ cong_negB)
      cong_imp_neg :
        Deriv (eqF (ap2 pi (natCode tag_imp)
                            (ap2 pi (ap2 pi (natCode tag_neg) A_old) (ap2 pi (natCode tag_neg) B_old)))
                    (ap2 pi (natCode tag_imp)
                            (ap2 pi (ap2 pi (natCode tag_neg) A_new) (ap2 pi (natCode tag_neg) B_new))))
      cong_imp_neg = congR pi (natCode tag_imp) cong_pair_neg

      cong_BA :
        Deriv (eqF (ap2 pi B_old A_old) (ap2 pi B_new A_new))
      cong_BA = ruleTrans (congL pi A_old cong_B) (congR pi B_new cong_A)
      cong_imp_BA :
        Deriv (eqF (ap2 pi (natCode tag_imp) (ap2 pi B_old A_old))
                    (ap2 pi (natCode tag_imp) (ap2 pi B_new A_new)))
      cong_imp_BA = congR pi (natCode tag_imp) cong_BA

      cong_pair_outer :
        Deriv (eqF (ap2 pi (ap2 pi (natCode tag_imp)
                                    (ap2 pi (ap2 pi (natCode tag_neg) A_old) (ap2 pi (natCode tag_neg) B_old)))
                            (ap2 pi (natCode tag_imp) (ap2 pi B_old A_old)))
                    (ap2 pi (ap2 pi (natCode tag_imp)
                                    (ap2 pi (ap2 pi (natCode tag_neg) A_new) (ap2 pi (natCode tag_neg) B_new)))
                            (ap2 pi (natCode tag_imp) (ap2 pi B_new A_new))))
      cong_pair_outer =
        ruleTrans (congL pi _ cong_imp_neg) (congR pi _ cong_imp_BA)

      final_subst :
        Deriv (eqF (outputRHS GE) (outputRHS extra))
      final_subst = congR pi (natCode tag_imp) cong_pair_outer

      chain_to_axBranch = ruleTrans chain_to_stepBody stepBody_to_axBranch
      chain_to_branch13 = ruleTrans chain_to_axBranch axBranch_to_branch13
      chain_to_eval = ruleTrans chain_to_branch13 axBranch13_eval
  in ruleTrans chain_to_eval final_subst
