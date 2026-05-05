{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Th12IfLf -- schematic Theorem 12 for IfLf (Fun2 case).
--
-- IfLf has 4 defining axioms (axIfLfL, axIfLfN, axIfLfLL, axIfLfNL)
-- dispatching on the SHAPES of both inputs.  The substantive proof
-- is in BRA/Thm12/Parts/IfLf.agda (in the older parametric framework);
-- it constructs D_IfLf : Fun2 via Fan + projections and proves the
-- 4 cases plus a 2D ruleIndBT-style closure (D_correct2_IfLf_univ).
--
-- This file just re-exports under the Th12_F2_IfLf naming for
-- uniformity with Th12_F1_I, Th12_F2_Pair, etc.

module BRA.Th12IfLf where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Thm.ThmT using (thmT)
open import BRA.Thm12.Parts.IfLf
  using (D_IfLf ; codeFTeq2_IfLf ; D_correct2_IfLf_univ)

------------------------------------------------------------------------
-- Df_F2_IfLf : Fun2.

Df_F2_IfLf : Fun2
Df_F2_IfLf = D_IfLf

------------------------------------------------------------------------
-- Schematic Theorem 12 for IfLf : single Deriv P with var 0, var 1 free.
--
-- The internal codeFTeq2_IfLf is definitionally equal to the asymmetric
-- form codeFTeq2Asym IfLf, so this also serves as the schematic
-- statement for the latter.

P_Th12_IfLf : Formula
P_Th12_IfLf = atomic (eqn (ap1 thmT (ap2 Df_F2_IfLf (var zero) (var (suc zero))))
                           (codeFTeq2_IfLf (var zero) (var (suc zero))))

Th12_F2_IfLf : Deriv P_Th12_IfLf
Th12_F2_IfLf = D_correct2_IfLf_univ
