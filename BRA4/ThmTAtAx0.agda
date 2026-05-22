{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.ThmTAtAx0 -- discharge of the  ax_0  (succ_nonzero) axiom closure
-- of  thmT  :
--
--   thmT_at_axN0 :
--     (extra : Term) ->
--     Deriv (eqF (ap1 thmT (ap2 pi (natCode tag_ax) (ap2 pi (natCode zero) extra)))
--                 (codeFormula (neg (atomic (eqn (ap1 s O) O)))))
--
-- Universal in  extra : Term  (ignored by axBranch0).  Output is the FIXED
-- codeFormula of axiom 0 (= ~(s O = O)) -- no codeFormula assumption to
-- bake in since axiom 0 has no Term/Formula parameters.  This is consistent
-- with [[feedback-bra4-closures-universal-form]] : the output is a raw Term
-- expression  codeFormula (neg (...))  which happens to be a codeFormula
-- by construction (the AXIOM SCHEMA codes ARE codeFormulas by definition).

module BRA4.ThmTAtAx0 where

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
  ( axFst ; axSnd ; compose1U ; compose1U_eq ; Post ; axPost )
open import BRA3.Dispatch        using ( condFork ; constN ; constN_eq )

------------------------------------------------------------------------
-- axBranch0 evaluation : ap1 axBranch0 stateP = codeFormula (neg (s O = O)).
--
-- axBranch0 = C pi (constN tag_neg)
--               (C pi (constN tag_eq)
--                     (C pi (C pi (constN tag_ap1) (C pi (constN tag_s) o)) o)) .
--
-- codeFormula (neg (atomic (eqn (ap1 s O) O)))
--   = pi (natCode tag_neg) (codeFormula (atomic (eqn (ap1 s O) O)))
--   = pi (natCode tag_neg) (pi (natCode tag_eq) (pi (codeTerm (ap1 s O)) (codeTerm O)))
--   = pi (natCode tag_neg) (pi (natCode tag_eq) (pi (pi (natCode tag_ap1) (pi (codeFun1 s) (codeTerm O))) (codeTerm O)))
--   = pi (natCode tag_neg) (pi (natCode tag_eq) (pi (pi (natCode tag_ap1) (pi (natCode tag_s) O)) O))
-- (since codeFun1 s = natCode tag_s and codeTerm O = O).

axBranch0_value :
  (input : Term) ->
  Deriv (eqF (ap1 axBranch0 input)
              (codeFormula (neg (atomic (eqn (ap1 s O) O)))))
axBranch0_value input =
  let -- Layer 1: C pi (constN tag_neg) <rest> input = pi (natCode tag_neg) (<rest> input).
      e1 :
        Deriv (eqF (ap1 axBranch0 input)
                    (ap2 pi (ap1 (constN tag_neg) input)
                            (ap1 (C pi (constN tag_eq)
                                       (C pi (C pi (constN tag_ap1) (C pi (constN tag_s) o)) o))
                                  input)))
      e1 = ax_C pi (constN tag_neg)
                  (C pi (constN tag_eq)
                       (C pi (C pi (constN tag_ap1) (C pi (constN tag_s) o)) o))
                  input

      cN_neg : Deriv (eqF (ap1 (constN tag_neg) input) (natCode tag_neg))
      cN_neg = constN_eq tag_neg input

      -- Layer 2: same for constN tag_eq.
      e2 :
        Deriv (eqF (ap1 (C pi (constN tag_eq)
                           (C pi (C pi (constN tag_ap1) (C pi (constN tag_s) o)) o)) input)
                    (ap2 pi (ap1 (constN tag_eq) input)
                            (ap1 (C pi (C pi (constN tag_ap1) (C pi (constN tag_s) o)) o)
                                  input)))
      e2 = ax_C pi (constN tag_eq)
                  (C pi (C pi (constN tag_ap1) (C pi (constN tag_s) o)) o)
                  input

      cN_eq : Deriv (eqF (ap1 (constN tag_eq) input) (natCode tag_eq))
      cN_eq = constN_eq tag_eq input

      -- Layer 3: C pi <inner-pi-of-s-codeterm> o.
      e3 :
        Deriv (eqF (ap1 (C pi (C pi (constN tag_ap1) (C pi (constN tag_s) o)) o) input)
                    (ap2 pi (ap1 (C pi (constN tag_ap1) (C pi (constN tag_s) o)) input)
                            (ap1 o input)))
      e3 = ax_C pi (C pi (constN tag_ap1) (C pi (constN tag_s) o)) o input

      oO1 : Deriv (eqF (ap1 o input) O)
      oO1 = ax_o input

      -- Layer 4: C pi (constN tag_ap1) (C pi (constN tag_s) o).
      e4 :
        Deriv (eqF (ap1 (C pi (constN tag_ap1) (C pi (constN tag_s) o)) input)
                    (ap2 pi (ap1 (constN tag_ap1) input)
                            (ap1 (C pi (constN tag_s) o) input)))
      e4 = ax_C pi (constN tag_ap1) (C pi (constN tag_s) o) input

      cN_ap1 : Deriv (eqF (ap1 (constN tag_ap1) input) (natCode tag_ap1))
      cN_ap1 = constN_eq tag_ap1 input

      -- Layer 5: C pi (constN tag_s) o.
      e5 :
        Deriv (eqF (ap1 (C pi (constN tag_s) o) input)
                    (ap2 pi (ap1 (constN tag_s) input) (ap1 o input)))
      e5 = ax_C pi (constN tag_s) o input

      cN_s : Deriv (eqF (ap1 (constN tag_s) input) (natCode tag_s))
      cN_s = constN_eq tag_s input

      oO2 : Deriv (eqF (ap1 o input) O)
      oO2 = ax_o input

      -- Assemble layer 5 to canonical form:
      --   (C pi (constN tag_s) o) input = pi (natCode tag_s) O .
      layer5_value :
        Deriv (eqF (ap1 (C pi (constN tag_s) o) input)
                    (ap2 pi (natCode tag_s) O))
      layer5_value =
        ruleTrans e5
          (ruleTrans (congL pi (ap1 o input) cN_s)
                     (congR pi (natCode tag_s) oO2))

      -- Assemble layer 4:
      --   (C pi (constN tag_ap1) (C pi (constN tag_s) o)) input
      --     = pi (natCode tag_ap1) (pi (natCode tag_s) O).
      layer4_value :
        Deriv (eqF (ap1 (C pi (constN tag_ap1) (C pi (constN tag_s) o)) input)
                    (ap2 pi (natCode tag_ap1) (ap2 pi (natCode tag_s) O)))
      layer4_value =
        ruleTrans e4
          (ruleTrans (congL pi (ap1 (C pi (constN tag_s) o) input) cN_ap1)
                     (congR pi (natCode tag_ap1) layer5_value))

      -- Assemble layer 3:
      --   (C pi <inner> o) input = pi <layer4-value> O.
      layer3_value :
        Deriv (eqF (ap1 (C pi (C pi (constN tag_ap1) (C pi (constN tag_s) o)) o) input)
                    (ap2 pi (ap2 pi (natCode tag_ap1) (ap2 pi (natCode tag_s) O)) O))
      layer3_value =
        ruleTrans e3
          (ruleTrans (congL pi (ap1 o input) layer4_value)
                     (congR pi (ap2 pi (natCode tag_ap1) (ap2 pi (natCode tag_s) O)) oO1))

      -- Assemble layer 2.
      layer2_value :
        Deriv (eqF (ap1 (C pi (constN tag_eq)
                           (C pi (C pi (constN tag_ap1) (C pi (constN tag_s) o)) o)) input)
                    (ap2 pi (natCode tag_eq)
                            (ap2 pi (ap2 pi (natCode tag_ap1) (ap2 pi (natCode tag_s) O)) O)))
      layer2_value =
        ruleTrans e2
          (ruleTrans (congL pi (ap1 (C pi (C pi (constN tag_ap1) (C pi (constN tag_s) o)) o) input) cN_eq)
                     (congR pi (natCode tag_eq) layer3_value))

      -- Assemble layer 1 (outermost).
      layer1_value :
        Deriv (eqF (ap1 axBranch0 input)
                    (ap2 pi (natCode tag_neg)
                            (ap2 pi (natCode tag_eq)
                              (ap2 pi (ap2 pi (natCode tag_ap1) (ap2 pi (natCode tag_s) O)) O))))
      layer1_value =
        ruleTrans e1
          (ruleTrans (congL pi (ap1 (C pi (constN tag_eq)
                                       (C pi (C pi (constN tag_ap1) (C pi (constN tag_s) o)) o))
                                    input)
                            cN_neg)
                     (congR pi (natCode tag_neg) layer2_value))
  in layer1_value

------------------------------------------------------------------------
-- The main closure.

thmT_at_axN0 :
  (extra : Term) ->
  Deriv (eqF (ap1 thmT (ap2 pi (natCode tag_ax) (ap2 pi (natCode zero) extra)))
              (codeFormula (neg (atomic (eqn (ap1 s O) O)))))
thmT_at_axN0 extra =
  let input : Term
      input = ap2 pi (natCode tag_ax) (ap2 pi (natCode zero) extra)

      Y_body : Term
      Y_body = ap2 pi (natCode zero) extra

      -- natCode tag_ax = s O = s (natCode 0).  So A_outer = natCode 0 = O.
      A_outer : Term
      A_outer = O

      P_outer : Term
      P_outer = pi_succ_outer A_outer Y_body

      prev : Term
      prev = ap2 (cov_spec baseValue_thmT stepFun_thmT) O P_outer

      stateP : Term
      stateP = ap2 pi P_outer (ap1 Snd prev)

      -- (1) cov_spec/Post chain via the shared helper.
      input_eq_sP_outer :
        Deriv (eqF input (ap1 s P_outer))
      input_eq_sP_outer = pi_at_succ A_outer Y_body

      chain_to_stepBody :
        Deriv (eqF (ap1 thmT input) (ap1 stepBody_thmT stateP))
      chain_to_stepBody = thmT_at_pi_succ_to_stepBody input P_outer input_eq_sP_outer

      -- (2) Outer tag dispatch.  get_tag stateP = natCode tag_ax.
      get_tag_eq_Fst_sP :
        Deriv (eqF (ap1 get_tag stateP) (ap1 Fst (ap1 s P_outer)))
      get_tag_eq_Fst_sP = get_tag_at_pi P_outer (ap1 Snd prev)

      Fst_input :
        Deriv (eqF (ap1 Fst input) (natCode tag_ax))
      Fst_input = axFst (natCode tag_ax) Y_body

      Fst_sP_to_Fst_input :
        Deriv (eqF (ap1 Fst (ap1 s P_outer)) (ap1 Fst input))
      Fst_sP_to_Fst_input = cong1 Fst (ruleSym input_eq_sP_outer)

      get_tag_value :
        Deriv (eqF (ap1 get_tag stateP) (natCode tag_ax))
      get_tag_value = ruleTrans get_tag_eq_Fst_sP
                        (ruleTrans Fst_sP_to_Fst_input Fst_input)

      isAx_value : Deriv (eqF (ap1 isAx stateP) (ap1 s O))
      isAx_value = isAx_at_natCodeAx_sO stateP get_tag_value

      stepBody_to_axBranch :
        Deriv (eqF (ap1 stepBody_thmT stateP) (ap1 ax_branch_thmT stateP))
      stepBody_to_axBranch = stepBody_thmT_to_ax_branch stateP isAx_value

      -- (3) get_ax_index stateP = natCode 0.
      -- get_ax_index = Fst body = Fst (pi (natCode 0) extra) = natCode 0.
      get_ax_index_eq :
        Deriv (eqF (ap1 get_ax_index stateP) (ap1 Fst (ap1 Snd (ap1 s P_outer))))
      get_ax_index_eq = get_ax_index_at_pi P_outer (ap1 Snd prev)

      Snd_sP_eq :
        Deriv (eqF (ap1 Snd (ap1 s P_outer)) (ap1 Snd input))
      Snd_sP_eq = cong1 Snd (ruleSym input_eq_sP_outer)

      Snd_input_eq_Yb :
        Deriv (eqF (ap1 Snd input) Y_body)
      Snd_input_eq_Yb = axSnd (natCode tag_ax) Y_body

      Snd_sP_to_Y :
        Deriv (eqF (ap1 Snd (ap1 s P_outer)) Y_body)
      Snd_sP_to_Y = ruleTrans Snd_sP_eq Snd_input_eq_Yb

      Fst_Y :
        Deriv (eqF (ap1 Fst Y_body) (natCode zero))
      Fst_Y = axFst (natCode zero) extra

      get_ax_index_value :
        Deriv (eqF (ap1 get_ax_index stateP) (natCode zero))
      get_ax_index_value =
        ruleTrans get_ax_index_eq
          (ruleTrans (cong1 Fst Snd_sP_to_Y) Fst_Y)

      -- (4) isAx0 fires sO via isAxOf_at_eq_sO.
      -- isAxOf 0 = isAx0 (definitional).
      isAx0_value : Deriv (eqF (ap1 isAx0 stateP) (ap1 s O))
      isAx0_value = isAxOf_at_eq_sO zero stateP get_ax_index_value

      -- (5) ax_branch_thmT -> axBranch0 via landAt0.
      axBranch_to_branch0 :
        Deriv (eqF (ap1 ax_branch_thmT stateP) (ap1 axBranch0 stateP))
      axBranch_to_branch0 = landAt0 stateP isAx0_value

      -- (6) axBranch0 stateP = codeFormula (neg (...)).
      axBranch0_eval :
        Deriv (eqF (ap1 axBranch0 stateP)
                    (codeFormula (neg (atomic (eqn (ap1 s O) O)))))
      axBranch0_eval = axBranch0_value stateP

      -- (7) Chain.
      chain_to_axBranch :
        Deriv (eqF (ap1 thmT input) (ap1 ax_branch_thmT stateP))
      chain_to_axBranch = ruleTrans chain_to_stepBody stepBody_to_axBranch

      chain_to_branch0 :
        Deriv (eqF (ap1 thmT input) (ap1 axBranch0 stateP))
      chain_to_branch0 = ruleTrans chain_to_axBranch axBranch_to_branch0
  in ruleTrans chain_to_branch0 axBranch0_eval
