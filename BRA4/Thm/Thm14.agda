{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Thm.Thm14 -- Goedel's Second Incompleteness Theorem.
--
-- PER BRA4/Plan.md sections "Thm 14 + Goedel II" (lines 400-412) and
-- "Things to AVOID" (lines 512-528), Thm 14 in BRA4 must be the
-- CONCRETE 5-step Guard 1963 chain, NOT a parametric scaffold that
-- takes "internal Goedel I"  step5  as an undischarged contract.
--
-- An earlier draft of this file imitated BRA3.Thm14Abstract by taking
--    step5 : Deriv (imp PrG PrBot)
-- as a module parameter.  That is "Goedel II abstract" -- it reduces
-- Goedel II to its own hardest sub-step -- and BRA4 is explicitly
-- designed to NOT do this (see Plan.md line 519: "DO NOT design
-- dispatchers that assume well-formed inputs" and the surrounding
-- discipline).  The earlier draft is REMOVED.
--
-- THE CORRECT STRUCTURE (per Plan.md lines 400-412):
--
--   Step 1: From  Provable G iff G  (diagonal),  derive  Provable G -> G .
--   Step 2: D_thF1 x = Deriv handle giving
--               thmT (encode of D_thF1 x) = code "th(x_) = something" .
--   Step 3: Apply Thm 13 at  th_F1 -instances to get
--               th (g (x)) = "th (x_) = sub (i_, i_)"   under hypothesis P_x .
--           (Here  i_ = num i,  j_ = num j , per learnt.md line 25.)
--   Step 4: K_part (x) builds the ruleInst-encoded form;
--               th (K_part x) = "th (x_) != sub (i_, i_)"
--           (with num applied throughout).
--   Step 5: Combine 3 + 4 (contradiction) -> Provable G -> falseF ->
--           Goedel II:
--               godelII : Deriv ConSchema -> Deriv falseF
--           where
--               ConSchema = neg (eqF (ap1 thmT (var 0)) codeFalse) .
--
-- PREREQUISITES.  In dependency order, this file needs:
--   (a) codeEq / subT  (Phase 2, Plan.md).
--   (b) ax / sb / mp / ind handlers + thmT itself  (Phase 3).
--   (c) encode_correct  (Phase 4).
--   (d) D_thF1  + Thm 12 / Thm 13  (Phase 6).
--   (e) K_part  + the 5-step Guard chain  (this file, Phase 7).
--
-- The previous parametric draft is preserved in the git history
-- (commit-then-remove) as a reference; do not resurrect it.

module BRA4.Thm.Thm14 where

-- INTENTIONALLY EMPTY pending the prerequisites above.
