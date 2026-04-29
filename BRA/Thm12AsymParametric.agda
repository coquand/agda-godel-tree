{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm12AsymParametric
--
-- Parametric asymmetric Theorem 12 prototype, using the EXISTING
-- thmTDisp*_param dispatch lemmas in BRA.Thm.ThmT.
--
-- Two cases:
--   thm12_I_param         : parametric in  var 0  (single-variable
--                           primitive, no ruleIndBT needed).
--   thm12_Fst_pair_shape  : at  ap2 Pair (var v1) (var v2)  (the
--                           Pair-shape case of Fst's ruleIndBT
--                           dispatch).  Demonstrates the multi-variable
--                           parametric case that prior analyses
--                           claimed needed multi-var sb infrastructure.
--
-- Key insight: thmTDispAxI_param and thmTDispAxFst_param accept arbitrary
-- Term payloads.  Setting payload = ap1 cor (var k) gives exactly the
-- asymmetric form -- no encode + sbDefParam bridge needed.
--
-- No postulates, no holes.

module BRA.Thm12AsymParametric where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor
open import BRA.Thm14CodeFTeqAsym
open import BRA.Thm.ThmT using
  ( thmT ; tagCode_axI ; tagCode_axFst
  ; thmTDispAxI_param ; thmTDispAxFst_param )

------------------------------------------------------------------------
-- thm12_I_param : parametric Theorem 12 for I at variable input.

thm12_I_param :
  Sigma Term (\ Df_term ->
    Deriv (atomic (eqn (ap1 thmT Df_term) (codeFTeq1Asym I (var zero)))))
thm12_I_param =
  let
    -- Df_term: encoded axI index with payload = ap1 cor (var 0).
    Df_term : Term
    Df_term = ap2 Pair tagCode_axI (ap1 cor (var zero))

    -- thmTDispAxI_param at xT = ap1 cor (var 0) gives:
    --   thmT (Pair tagCode_axI (cor (var 0)))
    --     = mkEqT (mkAp1T (codeF1 I) (cor (var 0))) (cor (var 0))
    --
    -- which is codeFTeq1Asym I (var 0) modulo the RHS bridge:
    -- codeFTeq1Asym I (var 0) has  cor (ap1 I (var 0))  on the RHS,
    -- which reduces (in Deriv) via  cong1 cor (axI (var 0))  to
    -- cor (var 0) .

    disp : Deriv (atomic (eqn
            (ap1 thmT Df_term)
            (ap2 Pair (ap2 Pair (reify tagAp1)
                                (ap2 Pair (reify (codeF1 I))
                                           (ap1 cor (var zero))))
                       (ap1 cor (var zero)))))
    disp = thmTDispAxI_param (ap1 cor (var zero))

    -- Bridge RHS subterm: cor (var 0) -> cor (ap1 I (var 0))
    --   axI (var 0)         : ap1 I (var 0) = var 0
    --   cong1 cor (axI (...)) : cor (ap1 I (var 0)) = cor (var 0)
    --   ruleSym             : cor (var 0) = cor (ap1 I (var 0)) .

    bridge_RHS : Deriv (atomic (eqn (ap1 cor (var zero))
                                     (ap1 cor (ap1 I (var zero)))))
    bridge_RHS = ruleSym (cong1 cor (axI (var zero)))

    -- Bridge through the outer mkEqT (= ap2 Pair).
    bridge : Deriv (atomic (eqn
              (ap2 Pair (ap2 Pair (reify tagAp1)
                                  (ap2 Pair (reify (codeF1 I))
                                             (ap1 cor (var zero))))
                         (ap1 cor (var zero)))
              (codeFTeq1Asym I (var zero))))
    bridge = congR Pair
               (ap2 Pair (reify tagAp1)
                          (ap2 Pair (reify (codeF1 I))
                                     (ap1 cor (var zero))))
               bridge_RHS

    pf_final : Deriv (atomic (eqn (ap1 thmT Df_term)
                                   (codeFTeq1Asym I (var zero))))
    pf_final = ruleTrans disp bridge

  in mkSigma Df_term pf_final

------------------------------------------------------------------------
-- thm12_Fst_pair_shape : Theorem 12 for Fst at Pair input.
--
-- The hard case the prior analysis claimed required multi-variable sb.
-- It does not -- the existing thmTDispAxFst_param accepts arbitrary
-- aT, bT payloads and returns the matching encoded equation.

module FstPairShape (v1 v2 : Nat) where

  thm12_Fst_pair_shape :
    Sigma Term (\ Df_term ->
      Deriv (atomic (eqn (ap1 thmT Df_term)
                          (codeFTeq1Asym Fst (ap2 Pair (var v1) (var v2))))))
  thm12_Fst_pair_shape =
    let
      -- Df_term: encoded axFst index with payload (cor (var v1), cor (var v2)).
      Df_term : Term
      Df_term = ap2 Pair tagCode_axFst
                    (ap2 Pair (ap1 cor (var v1)) (ap1 cor (var v2)))

      -- thmTDispAxFst_param at aT = cor (var v1), bT = cor (var v2) gives:
      --   thmT (Pair tagCode_axFst (Pair (cor v1) (cor v2)))
      --     = mkEqT (mkAp1T (codeF1 Fst)
      --                     (mkAp2T (codeF2 Pair) (cor v1) (cor v2)))
      --             (cor v1)
      --
      -- codeFTeq1Asym Fst (Pair v1 v2) reduces (via cor's axRecNd +
      -- stepCorRed for the LHS, and cor-cong + axFst for the RHS) to
      --   mkEqT (mkAp1T (codeF1 Fst)
      --                 (mkAp2T pairCodeF2T (cor v1) (cor v2)))
      --         (cor v1) .
      --
      -- pairCodeF2T  =  reify (codeF2 Pair)  definitionally.

      disp : Deriv (atomic (eqn
              (ap1 thmT Df_term)
              (ap2 Pair
                (ap2 Pair (reify tagAp1)
                  (ap2 Pair (reify (codeF1 Fst))
                    (ap2 Pair (reify tagAp2)
                      (ap2 Pair (reify (codeF2 Pair))
                        (ap2 Pair (ap1 cor (var v1))
                                   (ap1 cor (var v2)))))))
                (ap1 cor (var v1)))))
      disp = thmTDispAxFst_param (ap1 cor (var v1)) (ap1 cor (var v2))

      -- Bridge: codeFTeq1Asym Fst (Pair v1 v2) reductions via cor.

      v1T : Term
      v1T = var v1

      v2T : Term
      v2T = var v2

      pairT : Term
      pairT = ap2 Pair v1T v2T

      -- (R1) cor (Pair v1 v2) -> mkAp2T pairCodeF2T (cor v1) (cor v2).
      -- This is the chain in BRA/Cor.agda's corOfReify body, lifted to
      -- variable inputs.  axRecNd O stepCor v1 v2 + stepCorRed.

      cor_red_Pair : Deriv (atomic (eqn
                       (ap1 cor pairT)
                       (ap2 Pair (reify tagAp2)
                         (ap2 Pair (reify (codeF2 Pair))
                           (ap2 Pair (ap1 cor v1T) (ap1 cor v2T))))))
      cor_red_Pair =
        let
          recs   = ap2 Pair (ap1 cor v1T) (ap1 cor v2T)

          axNd : Deriv (atomic (eqn (ap1 cor pairT)
                                     (ap2 stepCor pairT recs)))
          axNd = axRecNd O stepCor v1T v2T

          stRed : Deriv (atomic (eqn (ap2 stepCor pairT recs)
                                      (ap2 Pair (reify tagAp2)
                                        (ap2 Pair (reify (codeF2 Pair)) recs))))
          stRed = stepCorRed pairT recs

        in ruleTrans axNd stRed

      -- Bridge LHS subterm of codeFTeq1Asym = mkAp1T (codeF1 Fst) (cor (Pair v1 v2)).
      -- mkAp1T G T = ap2 Pair (reify tagAp1) (ap2 Pair G T).

      bridge_LHS_inner : Deriv (atomic (eqn
                          (ap2 Pair (reify (codeF1 Fst)) (ap1 cor pairT))
                          (ap2 Pair (reify (codeF1 Fst))
                            (ap2 Pair (reify tagAp2)
                              (ap2 Pair (reify (codeF2 Pair))
                                (ap2 Pair (ap1 cor v1T) (ap1 cor v2T)))))))
      bridge_LHS_inner = congR Pair (reify (codeF1 Fst)) cor_red_Pair

      bridge_LHS : Deriv (atomic (eqn
                    (mkAp1T (reify (codeF1 Fst)) (ap1 cor pairT))
                    (ap2 Pair (reify tagAp1)
                      (ap2 Pair (reify (codeF1 Fst))
                        (ap2 Pair (reify tagAp2)
                          (ap2 Pair (reify (codeF2 Pair))
                            (ap2 Pair (ap1 cor v1T) (ap1 cor v2T))))))))
      bridge_LHS = congR Pair (reify tagAp1) bridge_LHS_inner

      -- Bridge RHS subterm: cor (Fst (Pair v1 v2)) -> cor v1.
      -- axFst v1 v2          : ap1 Fst (Pair v1 v2) = v1
      -- cong1 cor             : cor (ap1 Fst (Pair v1 v2)) = cor v1.

      bridge_RHS : Deriv (atomic (eqn (ap1 cor (ap1 Fst pairT))
                                       (ap1 cor v1T)))
      bridge_RHS = cong1 cor (axFst v1T v2T)

      -- We want to bridge from disp's RHS:
      --   ap2 Pair (LHS_disp_subterm) (cor v1)
      -- to codeFTeq1Asym Fst (Pair v1 v2):
      --   ap2 Pair (mkAp1T (codeF1 Fst) (cor (Pair v1 v2)))
      --             (cor (Fst (Pair v1 v2)))
      --
      -- Going backward: bridge_LHS (sym) brings disp's LHS subterm
      -- back to mkAp1T-of-cor-of-Pair, and bridge_RHS (sym) brings
      -- cor v1 back to cor (Fst (Pair v1 v2)).

      step_LHS : Deriv (atomic (eqn
                  (ap2 Pair
                    (ap2 Pair (reify tagAp1)
                      (ap2 Pair (reify (codeF1 Fst))
                        (ap2 Pair (reify tagAp2)
                          (ap2 Pair (reify (codeF2 Pair))
                            (ap2 Pair (ap1 cor v1T) (ap1 cor v2T))))))
                    (ap1 cor v1T))
                  (ap2 Pair
                    (mkAp1T (reify (codeF1 Fst)) (ap1 cor pairT))
                    (ap1 cor v1T))))
      step_LHS = congL Pair (ap1 cor v1T) (ruleSym bridge_LHS)

      step_RHS : Deriv (atomic (eqn
                  (ap2 Pair
                    (mkAp1T (reify (codeF1 Fst)) (ap1 cor pairT))
                    (ap1 cor v1T))
                  (ap2 Pair
                    (mkAp1T (reify (codeF1 Fst)) (ap1 cor pairT))
                    (ap1 cor (ap1 Fst pairT)))))
      step_RHS = congR Pair
                   (mkAp1T (reify (codeF1 Fst)) (ap1 cor pairT))
                   (ruleSym bridge_RHS)

      bridge_total : Deriv (atomic (eqn
              (ap2 Pair
                (ap2 Pair (reify tagAp1)
                  (ap2 Pair (reify (codeF1 Fst))
                    (ap2 Pair (reify tagAp2)
                      (ap2 Pair (reify (codeF2 Pair))
                        (ap2 Pair (ap1 cor v1T) (ap1 cor v2T))))))
                (ap1 cor v1T))
              (codeFTeq1Asym Fst pairT)))
      bridge_total = ruleTrans step_LHS step_RHS

      pf_final : Deriv (atomic (eqn (ap1 thmT Df_term)
                                     (codeFTeq1Asym Fst pairT)))
      pf_final = ruleTrans disp bridge_total

    in mkSigma Df_term pf_final
