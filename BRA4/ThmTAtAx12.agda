{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.ThmTAtAx12 -- axiom 12 (axS).
-- extra = pi codeA (pi codeB codeC).

module BRA4.ThmTAtAx12 where

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
  N12 : Nat
  N12 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))

  outputRHS : Term -> Term
  outputRHS extra =
    let A = ap1 Fst extra
        B = ap1 Fst (ap1 Snd extra)
        C2 = ap1 Snd (ap1 Snd extra)
        impAB = ap2 pi (natCode tag_imp) (ap2 pi A B)
        impAC = ap2 pi (natCode tag_imp) (ap2 pi A C2)
        impBC = ap2 pi (natCode tag_imp) (ap2 pi B C2)
        impA_impBC = ap2 pi (natCode tag_imp) (ap2 pi A impBC)
        impAB_impAC = ap2 pi (natCode tag_imp) (ap2 pi impAB impAC)
    in ap2 pi (natCode tag_imp) (ap2 pi impA_impBC impAB_impAC)

  mkW : (M : Nat) -> Eq (natEq M N12) false -> NatNeqWitness N12 M
  mkW M pf = natEqFalse_to_witness M N12 pf

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
  w10 = mkW (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) refl
  w11 = mkW (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) refl

------------------------------------------------------------------------
-- axBranch12 evaluation.

axBranch12_value :
  (input : Term) ->
  Deriv (eqF (ap1 axBranch12 input) (outputRHS (ap1 get_ax_extra input)))
axBranch12_value input =
  let GE = ap1 get_ax_extra input
      A = ap1 Fst GE
      B = ap1 Fst (ap1 Snd GE)
      C2 = ap1 Snd (ap1 Snd GE)

      get_eF_eq : Deriv (eqF (ap1 get_extra_Fst input) A)
      get_eF_eq = compose1U_eq Fst get_ax_extra input

      -- get_extra_Snd input = Snd GE.
      get_eS_eq : Deriv (eqF (ap1 get_extra_Snd input) (ap1 Snd GE))
      get_eS_eq = compose1U_eq Snd get_ax_extra input

      -- get_extra_FstSnd input = Fst (get_extra_Snd input) = Fst (Snd GE) = B.
      get_eFS_eq : Deriv (eqF (ap1 get_extra_FstSnd input) B)
      get_eFS_eq =
        ruleTrans (compose1U_eq Fst get_extra_Snd input)
                  (cong1 Fst get_eS_eq)

      -- get_extra_SndSnd input = Snd (Snd GE) = C2.
      get_eSS_eq : Deriv (eqF (ap1 get_extra_SndSnd input) C2)
      get_eSS_eq =
        ruleTrans (compose1U_eq Snd get_extra_Snd input)
                  (cong1 Snd get_eS_eq)

      cN_imp = constN_eq tag_imp input

      -- C pi get_extra_FstSnd get_extra_SndSnd input = pi B C2.
      pi_BC :
        Deriv (eqF (ap1 (C pi get_extra_FstSnd get_extra_SndSnd) input) (ap2 pi B C2))
      pi_BC =
        ruleTrans (ax_C pi get_extra_FstSnd get_extra_SndSnd input)
          (ruleTrans (congL pi (ap1 get_extra_SndSnd input) get_eFS_eq)
                     (congR pi B get_eSS_eq))

      -- C pi (constN tag_imp) (C pi get_extra_FstSnd get_extra_SndSnd) input = impBC.
      impBC_eq :
        Deriv (eqF (ap1 (C pi (constN tag_imp) (C pi get_extra_FstSnd get_extra_SndSnd)) input)
                    (ap2 pi (natCode tag_imp) (ap2 pi B C2)))
      impBC_eq =
        ruleTrans (ax_C pi (constN tag_imp) (C pi get_extra_FstSnd get_extra_SndSnd) input)
          (ruleTrans (congL pi _ cN_imp) (congR pi (natCode tag_imp) pi_BC))

      -- C pi get_extra_Fst (C pi (constN tag_imp) (C pi get_extra_FstSnd get_extra_SndSnd)) input
      --   = pi A impBC.
      pi_A_impBC :
        Deriv (eqF (ap1 (C pi get_extra_Fst
                              (C pi (constN tag_imp) (C pi get_extra_FstSnd get_extra_SndSnd))) input)
                    (ap2 pi A (ap2 pi (natCode tag_imp) (ap2 pi B C2))))
      pi_A_impBC =
        ruleTrans (ax_C pi get_extra_Fst
                           (C pi (constN tag_imp) (C pi get_extra_FstSnd get_extra_SndSnd)) input)
          (ruleTrans (congL pi _ get_eF_eq) (congR pi A impBC_eq))

      -- imp A impBC.
      impA_impBC_eq :
        Deriv (eqF (ap1 (C pi (constN tag_imp)
                              (C pi get_extra_Fst
                                    (C pi (constN tag_imp) (C pi get_extra_FstSnd get_extra_SndSnd)))) input)
                    (ap2 pi (natCode tag_imp) (ap2 pi A (ap2 pi (natCode tag_imp) (ap2 pi B C2)))))
      impA_impBC_eq =
        ruleTrans (ax_C pi (constN tag_imp)
                           (C pi get_extra_Fst
                                 (C pi (constN tag_imp) (C pi get_extra_FstSnd get_extra_SndSnd))) input)
          (ruleTrans (congL pi _ cN_imp) (congR pi (natCode tag_imp) pi_A_impBC))

      -- C pi get_extra_Fst get_extra_FstSnd input = pi A B.
      pi_AB :
        Deriv (eqF (ap1 (C pi get_extra_Fst get_extra_FstSnd) input) (ap2 pi A B))
      pi_AB =
        ruleTrans (ax_C pi get_extra_Fst get_extra_FstSnd input)
          (ruleTrans (congL pi (ap1 get_extra_FstSnd input) get_eF_eq)
                     (congR pi A get_eFS_eq))

      -- impAB.
      impAB_eq :
        Deriv (eqF (ap1 (C pi (constN tag_imp) (C pi get_extra_Fst get_extra_FstSnd)) input)
                    (ap2 pi (natCode tag_imp) (ap2 pi A B)))
      impAB_eq =
        ruleTrans (ax_C pi (constN tag_imp) (C pi get_extra_Fst get_extra_FstSnd) input)
          (ruleTrans (congL pi _ cN_imp) (congR pi (natCode tag_imp) pi_AB))

      -- C pi get_extra_Fst get_extra_SndSnd input = pi A C2.
      pi_AC :
        Deriv (eqF (ap1 (C pi get_extra_Fst get_extra_SndSnd) input) (ap2 pi A C2))
      pi_AC =
        ruleTrans (ax_C pi get_extra_Fst get_extra_SndSnd input)
          (ruleTrans (congL pi (ap1 get_extra_SndSnd input) get_eF_eq)
                     (congR pi A get_eSS_eq))

      -- impAC.
      impAC_eq :
        Deriv (eqF (ap1 (C pi (constN tag_imp) (C pi get_extra_Fst get_extra_SndSnd)) input)
                    (ap2 pi (natCode tag_imp) (ap2 pi A C2)))
      impAC_eq =
        ruleTrans (ax_C pi (constN tag_imp) (C pi get_extra_Fst get_extra_SndSnd) input)
          (ruleTrans (congL pi _ cN_imp) (congR pi (natCode tag_imp) pi_AC))

      -- pi impAB impAC.
      pi_impAB_impAC :
        Deriv (eqF (ap1 (C pi (C pi (constN tag_imp) (C pi get_extra_Fst get_extra_FstSnd))
                              (C pi (constN tag_imp) (C pi get_extra_Fst get_extra_SndSnd))) input)
                    (ap2 pi (ap2 pi (natCode tag_imp) (ap2 pi A B))
                            (ap2 pi (natCode tag_imp) (ap2 pi A C2))))
      pi_impAB_impAC =
        ruleTrans (ax_C pi (C pi (constN tag_imp) (C pi get_extra_Fst get_extra_FstSnd))
                            (C pi (constN tag_imp) (C pi get_extra_Fst get_extra_SndSnd)) input)
          (ruleTrans (congL pi _ impAB_eq) (congR pi _ impAC_eq))

      -- imp impAB impAC = impAB_impAC.
      impAB_impAC_eq :
        Deriv (eqF (ap1 (C pi (constN tag_imp)
                              (C pi (C pi (constN tag_imp) (C pi get_extra_Fst get_extra_FstSnd))
                                    (C pi (constN tag_imp) (C pi get_extra_Fst get_extra_SndSnd)))) input)
                    (ap2 pi (natCode tag_imp)
                            (ap2 pi (ap2 pi (natCode tag_imp) (ap2 pi A B))
                                    (ap2 pi (natCode tag_imp) (ap2 pi A C2)))))
      impAB_impAC_eq =
        ruleTrans (ax_C pi (constN tag_imp)
                           (C pi (C pi (constN tag_imp) (C pi get_extra_Fst get_extra_FstSnd))
                                 (C pi (constN tag_imp) (C pi get_extra_Fst get_extra_SndSnd))) input)
          (ruleTrans (congL pi _ cN_imp) (congR pi (natCode tag_imp) pi_impAB_impAC))

      -- pi impA_impBC impAB_impAC.
      pi_outer :
        Deriv (eqF (ap1 (C pi (C pi (constN tag_imp)
                                    (C pi get_extra_Fst
                                          (C pi (constN tag_imp) (C pi get_extra_FstSnd get_extra_SndSnd))))
                              (C pi (constN tag_imp)
                                    (C pi (C pi (constN tag_imp) (C pi get_extra_Fst get_extra_FstSnd))
                                          (C pi (constN tag_imp) (C pi get_extra_Fst get_extra_SndSnd))))) input)
                    (ap2 pi (ap2 pi (natCode tag_imp) (ap2 pi A (ap2 pi (natCode tag_imp) (ap2 pi B C2))))
                            (ap2 pi (natCode tag_imp)
                                    (ap2 pi (ap2 pi (natCode tag_imp) (ap2 pi A B))
                                            (ap2 pi (natCode tag_imp) (ap2 pi A C2))))))
      pi_outer =
        ruleTrans (ax_C pi (C pi (constN tag_imp)
                                  (C pi get_extra_Fst
                                        (C pi (constN tag_imp) (C pi get_extra_FstSnd get_extra_SndSnd))))
                            (C pi (constN tag_imp)
                                  (C pi (C pi (constN tag_imp) (C pi get_extra_Fst get_extra_FstSnd))
                                        (C pi (constN tag_imp) (C pi get_extra_Fst get_extra_SndSnd)))) input)
          (ruleTrans (congL pi _ impA_impBC_eq) (congR pi _ impAB_impAC_eq))

  in ruleTrans (ax_C pi (constN tag_imp)
                       (C pi (C pi (constN tag_imp)
                                    (C pi get_extra_Fst
                                          (C pi (constN tag_imp) (C pi get_extra_FstSnd get_extra_SndSnd))))
                             (C pi (constN tag_imp)
                                   (C pi (C pi (constN tag_imp) (C pi get_extra_Fst get_extra_FstSnd))
                                         (C pi (constN tag_imp) (C pi get_extra_Fst get_extra_SndSnd))))) input)
       (ruleTrans (congL pi _ cN_imp)
                  (congR pi (natCode tag_imp) pi_outer))

------------------------------------------------------------------------
thmT_at_axN12 :
  (extra : Term) ->
  Deriv (eqF (ap1 thmT (ap2 pi (natCode tag_ax) (ap2 pi (natCode N12) extra)))
              (outputRHS extra))
thmT_at_axN12 extra =
  let input : Term
      input = ap2 pi (natCode tag_ax) (ap2 pi (natCode N12) extra)
      Y_body : Term
      Y_body = ap2 pi (natCode N12) extra
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
      Fst_Y = axFst (natCode N12) extra

      get_ax_index_value :
        Deriv (eqF (ap1 get_ax_index stateP) (natCode N12))
      get_ax_index_value =
        ruleTrans get_ax_index_eq
          (ruleTrans (cong1 Fst Snd_sP_to_Y) Fst_Y)

      get_ax_extra_eq = get_ax_extra_at_pi P_outer (ap1 Snd prev)
      Snd_Y = axSnd (natCode N12) extra
      get_ax_extra_value :
        Deriv (eqF (ap1 get_ax_extra stateP) extra)
      get_ax_extra_value =
        ruleTrans get_ax_extra_eq
          (ruleTrans (cong1 Snd Snd_sP_to_Y) Snd_Y)

      n0 = isAxOf_at_neq_O zero N12 w0 stateP get_ax_index_value
      n1 = isAxOf_at_neq_O (suc zero) N12 w1 stateP get_ax_index_value
      n2 = isAxOf_at_neq_O (suc (suc zero)) N12 w2 stateP get_ax_index_value
      n3 = isAxOf_at_neq_O (suc (suc (suc zero))) N12 w3 stateP get_ax_index_value
      n4 = isAxOf_at_neq_O (suc (suc (suc (suc zero)))) N12 w4 stateP get_ax_index_value
      n5 = isAxOf_at_neq_O (suc (suc (suc (suc (suc zero))))) N12 w5 stateP get_ax_index_value
      n6 = isAxOf_at_neq_O (suc (suc (suc (suc (suc (suc zero)))))) N12 w6 stateP get_ax_index_value
      n7 = isAxOf_at_neq_O (suc (suc (suc (suc (suc (suc (suc zero))))))) N12 w7 stateP get_ax_index_value
      n8 = isAxOf_at_neq_O (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) N12 w8 stateP get_ax_index_value
      n9 = isAxOf_at_neq_O (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) N12 w9 stateP get_ax_index_value
      n10 = isAxOf_at_neq_O (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) N12 w10 stateP get_ax_index_value
      n11 = isAxOf_at_neq_O (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) N12 w11 stateP get_ax_index_value
      n12s = isAxOf_at_eq_sO N12 stateP get_ax_index_value

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
      d12 = landAt12 stateP n12s
      r11 = ruleTrans d11 d12
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
      axBranch_to_branch12 = ruleTrans d0 r1

      axBranch12_eval = axBranch12_value stateP

      ge_eq = get_ax_extra_value
      GE = ap1 get_ax_extra stateP

      -- Build pointwise congruence equation outputRHS GE = outputRHS extra.
      Aold = ap1 Fst GE
      Bold = ap1 Fst (ap1 Snd GE)
      Cold = ap1 Snd (ap1 Snd GE)
      Anew = ap1 Fst extra
      Bnew = ap1 Fst (ap1 Snd extra)
      Cnew = ap1 Snd (ap1 Snd extra)

      cong_A : Deriv (eqF Aold Anew)
      cong_A = cong1 Fst ge_eq
      cong_Snd_GE : Deriv (eqF (ap1 Snd GE) (ap1 Snd extra))
      cong_Snd_GE = cong1 Snd ge_eq
      cong_B : Deriv (eqF Bold Bnew)
      cong_B = cong1 Fst cong_Snd_GE
      cong_C : Deriv (eqF Cold Cnew)
      cong_C = cong1 Snd cong_Snd_GE

      cong_BC : Deriv (eqF (ap2 pi Bold Cold) (ap2 pi Bnew Cnew))
      cong_BC = ruleTrans (congL pi Cold cong_B) (congR pi Bnew cong_C)

      cong_impBC :
        Deriv (eqF (ap2 pi (natCode tag_imp) (ap2 pi Bold Cold))
                    (ap2 pi (natCode tag_imp) (ap2 pi Bnew Cnew)))
      cong_impBC = congR pi (natCode tag_imp) cong_BC

      cong_A_impBC :
        Deriv (eqF (ap2 pi Aold (ap2 pi (natCode tag_imp) (ap2 pi Bold Cold)))
                    (ap2 pi Anew (ap2 pi (natCode tag_imp) (ap2 pi Bnew Cnew))))
      cong_A_impBC = ruleTrans (congL pi _ cong_A) (congR pi Anew cong_impBC)

      cong_impA_impBC :
        Deriv (eqF (ap2 pi (natCode tag_imp) (ap2 pi Aold (ap2 pi (natCode tag_imp) (ap2 pi Bold Cold))))
                    (ap2 pi (natCode tag_imp) (ap2 pi Anew (ap2 pi (natCode tag_imp) (ap2 pi Bnew Cnew)))))
      cong_impA_impBC = congR pi (natCode tag_imp) cong_A_impBC

      cong_AB :
        Deriv (eqF (ap2 pi Aold Bold) (ap2 pi Anew Bnew))
      cong_AB = ruleTrans (congL pi Bold cong_A) (congR pi Anew cong_B)
      cong_impAB :
        Deriv (eqF (ap2 pi (natCode tag_imp) (ap2 pi Aold Bold))
                    (ap2 pi (natCode tag_imp) (ap2 pi Anew Bnew)))
      cong_impAB = congR pi (natCode tag_imp) cong_AB

      cong_AC :
        Deriv (eqF (ap2 pi Aold Cold) (ap2 pi Anew Cnew))
      cong_AC = ruleTrans (congL pi Cold cong_A) (congR pi Anew cong_C)
      cong_impAC :
        Deriv (eqF (ap2 pi (natCode tag_imp) (ap2 pi Aold Cold))
                    (ap2 pi (natCode tag_imp) (ap2 pi Anew Cnew)))
      cong_impAC = congR pi (natCode tag_imp) cong_AC

      cong_impAB_impAC :
        Deriv (eqF (ap2 pi (ap2 pi (natCode tag_imp) (ap2 pi Aold Bold))
                           (ap2 pi (natCode tag_imp) (ap2 pi Aold Cold)))
                    (ap2 pi (ap2 pi (natCode tag_imp) (ap2 pi Anew Bnew))
                           (ap2 pi (natCode tag_imp) (ap2 pi Anew Cnew))))
      cong_impAB_impAC =
        ruleTrans (congL pi _ cong_impAB) (congR pi _ cong_impAC)

      cong_impAB_impAC_imp :
        Deriv (eqF (ap2 pi (natCode tag_imp)
                            (ap2 pi (ap2 pi (natCode tag_imp) (ap2 pi Aold Bold))
                                    (ap2 pi (natCode tag_imp) (ap2 pi Aold Cold))))
                    (ap2 pi (natCode tag_imp)
                            (ap2 pi (ap2 pi (natCode tag_imp) (ap2 pi Anew Bnew))
                                    (ap2 pi (natCode tag_imp) (ap2 pi Anew Cnew)))))
      cong_impAB_impAC_imp = congR pi (natCode tag_imp) cong_impAB_impAC

      cong_pair_outer :
        Deriv (eqF (ap2 pi (ap2 pi (natCode tag_imp)
                                    (ap2 pi Aold (ap2 pi (natCode tag_imp) (ap2 pi Bold Cold))))
                           (ap2 pi (natCode tag_imp)
                                   (ap2 pi (ap2 pi (natCode tag_imp) (ap2 pi Aold Bold))
                                           (ap2 pi (natCode tag_imp) (ap2 pi Aold Cold)))))
                    (ap2 pi (ap2 pi (natCode tag_imp)
                                    (ap2 pi Anew (ap2 pi (natCode tag_imp) (ap2 pi Bnew Cnew))))
                           (ap2 pi (natCode tag_imp)
                                   (ap2 pi (ap2 pi (natCode tag_imp) (ap2 pi Anew Bnew))
                                           (ap2 pi (natCode tag_imp) (ap2 pi Anew Cnew))))))
      cong_pair_outer =
        ruleTrans (congL pi _ cong_impA_impBC) (congR pi _ cong_impAB_impAC_imp)

      final_subst :
        Deriv (eqF (outputRHS GE) (outputRHS extra))
      final_subst = congR pi (natCode tag_imp) cong_pair_outer

      chain_to_axBranch = ruleTrans chain_to_stepBody stepBody_to_axBranch
      chain_to_branch12 = ruleTrans chain_to_axBranch axBranch_to_branch12
      chain_to_eval = ruleTrans chain_to_branch12 axBranch12_eval
  in ruleTrans chain_to_eval final_subst
