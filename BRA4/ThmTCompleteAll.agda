{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.ThmTCompleteAll -- the bundled per-constructor completeness API
-- re-exporting all 17 cases of the BRA3.Deriv constructor schema.
--
-- Each function has signature
--   thmT_complete_<rule> : <args + IH-equations + closed witnesses> ->
--                          Deriv (eqF (ap1 thmT (encode (<rule> args)))
--                                      (codeFormula <conclusion>))
--
-- Consumers (Diagonal , Goedel I , Goedel II) just  `open import
-- BRA4.ThmTCompleteAll`  and have all 17 per-rule lemmas in scope.
--
-- LAYERING (which file does each case live in) :
--
--   BRA4.ThmTComplete (easy layer , IH-consumable structurals) :
--     thmT_complete_ax_succ_nonzero
--     thmT_complete_mp
--     thmT_complete_ruleInst
--     thmT_complete_ruleIndNat
--     thmT_complete_axK
--
--   BRA4.ThmTCompleteAxClosedFree (single Term arg, no Closed) :
--     thmT_complete_ax_o
--     thmT_complete_ax_u
--
--   BRA4.ThmTCompleteAxClosed (multi Term args, Closed required) :
--     thmT_complete_ax_v
--     thmT_complete_ax_eqTrans
--     thmT_complete_ax_eqCong1
--     thmT_complete_ax_eqCongL
--     thmT_complete_ax_eqCongR
--
--   BRA4.ThmTCompleteAxFunctor (functor-bearing axioms) :
--     thmT_complete_ax_C
--     thmT_complete_ax_R_base
--     thmT_complete_ax_R_step          -- requires Closed x
--
--   BRA4.ThmTCompleteAxForm (formula-only axioms) :
--     thmT_complete_axS
--     thmT_complete_axNeg

module BRA4.ThmTCompleteAll where

open import BRA4.ThmTComplete           public
  using ( thmT_complete_ax_succ_nonzero
        ; thmT_complete_mp
        ; thmT_complete_ruleInst
        ; thmT_complete_ruleIndNat
        ; thmT_complete_axK
        ; sbtEq_codeTerm
        ; sbfEq_codeFormula )
open import BRA4.ThmTCompleteAxClosedFree public
  using ( thmT_complete_ax_o
        ; thmT_complete_ax_u )
open import BRA4.ThmTCompleteAxClosed public
  using ( thmT_complete_ax_v
        ; thmT_complete_ax_eqTrans
        ; thmT_complete_ax_eqCong1
        ; thmT_complete_ax_eqCongL
        ; thmT_complete_ax_eqCongR )
open import BRA4.ThmTCompleteAxFunctor public
  using ( thmT_complete_ax_C
        ; thmT_complete_ax_R_base
        ; thmT_complete_ax_R_step )
open import BRA4.ThmTCompleteAxForm public
  using ( thmT_complete_axS
        ; thmT_complete_axNeg )
