{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Th12FstLf -- Theorem 12 for Fst at the lf-input case.
--
-- Df_F1_Fst at input O (= lf): the simplest case.  axFstLf is closed
-- (no arguments), so no substitution is needed.  Df_F1_Fst_lf is just
-- a constant Fun1 returning the closed proof code  reify encAxFstLf .
--
-- The Pair-input case (x = ap2 Pair v1 v2) needs simultaneous double
-- substitution via subT2 (and currently requires the thmT-dispatch
-- extension with tagRuleInst2 — see project_sb2_done_thmt_blocks_fst.md).
-- This file delivers ONLY the lf-case as an unconditional concrete
-- result.
--
-- After fromBaseAndPair (lf-case + Pair-case → schematic Fst), the
-- schematic Df_F1_Fst would compose this lf-case with the Pair-case via
-- the case-split rule.
--
-- No postulates, no holes.

module BRA.Th12FstLf where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor          using (cor ; stepCor)
open import BRA.StepReduce   using (ktRed)
open import BRA.Thm.Parts.AxFstLf using (encAxFstLf ; outAxFstLf)
open import BRA.Thm.ThmT     using (thmT ; thmTDispAxFstLf)
open import BRA.Thm14CodeFTeqAsym using (codeFTeq1Asym ; mkAp1T ; mkEqT)

------------------------------------------------------------------------
-- Df_F1_Fst_lf : Fun1
--
-- A constant Fun1 returning  reify encAxFstLf  for any input.  At input
-- O specifically, this gives the proof code that thmT decodes to the
-- encoded "Fst(0) = 0" equation.

Df_F1_Fst_lf : Fun1
Df_F1_Fst_lf = KT (reify encAxFstLf)

------------------------------------------------------------------------
-- Th12_F1_Fst_at_lf : the lf case of Theorem 12 for Fst.
--
--   Deriv (atomic (eqn (ap1 thmT (ap1 Df_F1_Fst_lf O))
--                       (codeFTeq1Asym Fst O)))
--
-- Proof chain:
--   (1) ktRed: ap1 (KT (reify encAxFstLf)) O = reify encAxFstLf.
--   (2) thmTDispAxFstLf: thmT(reify encAxFstLf) = reify outAxFstLf.
--   (3) Cor-bridges: codeFTeq1Asym Fst O = reify outAxFstLf modulo
--       cor O = O (axRecLf O stepCor) and Fst O = O (axFstLf) reductions.

Th12_F1_Fst_at_lf :
  Deriv (atomic (eqn (ap1 thmT (ap1 Df_F1_Fst_lf O))
                     (codeFTeq1Asym Fst O)))
Th12_F1_Fst_at_lf =
  let
    -- The closed proof-code Term.
    pcT : Term
    pcT = reify encAxFstLf

    -- Step 1: unfold KT at input O.
    --   ktRed (encAxFstLf : Tree) O : ap1 (KT (reify encAxFstLf)) O = reify encAxFstLf
    s1 : Deriv (atomic (eqn (ap1 Df_F1_Fst_lf O) pcT))
    s1 = ktRed encAxFstLf O

    -- Step 2: lift to thmT-applied form via cong1.
    s2 : Deriv (atomic (eqn (ap1 thmT (ap1 Df_F1_Fst_lf O))
                             (ap1 thmT pcT)))
    s2 = cong1 thmT s1

    -- Step 3: thmT decodes the closed proof code.
    s3 : Deriv (atomic (eqn (ap1 thmT pcT) (reify outAxFstLf)))
    s3 = thmTDispAxFstLf

    -- Step 4: bridge  reify outAxFstLf  to  codeFTeq1Asym Fst O .
    --
    -- reify outAxFstLf
    --   = reify (codeFormula (atomic (eqn (ap1 Fst O) O)))
    --   = mkEqT (mkAp1T (reify (codeF1 Fst)) O) O   (after reify+code reductions)
    --
    -- codeFTeq1Asym Fst O
    --   = mkEqT (mkAp1T (reify (codeF1 Fst)) (ap1 cor O)) (ap1 cor (ap1 Fst O))
    --
    -- Differences:
    --   * LHS-inner slot:  O  vs  ap1 cor O   — bridged by  ruleSym (axRecLf O stepCor).
    --   * RHS slot:  O  vs  ap1 cor (ap1 Fst O)
    --     bridged by  ruleSym (ruleTrans (cong1 cor axFstLf) (axRecLf O stepCor)).

    bridgeInner : Deriv (atomic (eqn O (ap1 cor O)))
    bridgeInner = ruleSym (axRecLf stepCor)

    bridgeRHS : Deriv (atomic (eqn O (ap1 cor (ap1 Fst O))))
    bridgeRHS =
      ruleSym (ruleTrans (cong1 cor axFstLf) (axRecLf stepCor))

    -- Lift bridgeInner through  mkAp1T (reify (codeF1 Fst)) [_] :
    --   mkAp1T (reify (codeF1 Fst)) O  =  mkAp1T (reify (codeF1 Fst)) (ap1 cor O)
    bridgeLHS : Deriv (atomic (eqn (mkAp1T (reify (codeF1 Fst)) O)
                                    (mkAp1T (reify (codeF1 Fst)) (ap1 cor O))))
    bridgeLHS =
      congR Pair (reify tagAp1)
        (congR Pair (reify (codeF1 Fst)) bridgeInner)

    -- Combine into the full bridge from reify outAxFstLf to codeFTeq1Asym Fst O.
    bridgeFull : Deriv (atomic (eqn (mkEqT (mkAp1T (reify (codeF1 Fst)) O) O)
                                     (codeFTeq1Asym Fst O)))
    bridgeFull =
      ruleTrans (congL Pair O bridgeLHS)
                (congR Pair (mkAp1T (reify (codeF1 Fst)) (ap1 cor O)) bridgeRHS)

    s4 : Deriv (atomic (eqn (reify outAxFstLf) (codeFTeq1Asym Fst O)))
    s4 = bridgeFull

  in ruleTrans s2 (ruleTrans s3 s4)
