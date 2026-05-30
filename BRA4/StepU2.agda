{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.StepU2 -- Layer 1 of the two-layer CK-machine: the operational
-- semantics for Fun1 (no mu).
--
-- ARCHITECTURAL NOTE.  The Fun1 step-combinator `step` IS the universal
-- step combinator `stepU` from BRA4.EvalUStep.  Although `stepU`
-- structurally contains a mu branch (for tag_mu code heads), that branch
-- is DORMANT at Fun1/Fun2 code shapes: the head tag of `mcode1 f` and
-- `mcode2 g` is never tag_mu, so the EV cascade never dispatches into
-- the mu body.  Layer-1 completeness for Fun1 (BRA4.StepU2Correct) is
-- therefore unaffected by the presence of the mu branch in `step`.
--
-- The eleven transition lemmas exposed below cover exactly the Fun1 /
-- Fun2 fragment (no mu): EV-S, EV-O, EV-U, EV-V, EV-C, EV-R-base,
-- EV-R-step on the EV side, and RT-App2, RT-C1, RT-R1, RT-Empty on the
-- RT side.  Each lemma is stated at arbitrary Term-level inputs (no
-- natCode wrappers on the EV argument), so they directly drive a
-- Term-fuel Reaches relation in BRA4.StepU2Correct.
--
-- This is the architectural layer-1 view of the universal interpreter:
-- when restricted to Fun1/Fun2 codes, the universal stepU IS our
-- Fun1-operational-semantics step.

module BRA4.StepU2 where

------------------------------------------------------------------------
-- Re-export the configuration / kont / frame / code-coding from EvalU.

open import BRA4.EvalU public
  using ( cfgEV ; cfgRT ; cfgHALT
        ; kons ; konEmpty
        ; frmApp2 ; frmC1 ; frmR1
        ; tagEV ; tagRT ; tagHALT
        ; tagApp2 ; tagC1 ; tagR1
        ; mcode1 ; mcode2 )

------------------------------------------------------------------------
-- The layer-1 step combinator and its eleven Fun1/Fun2 transition
-- lemmas (no mu).

open import BRA4.EvalUStep public
  using ( stepU
        ; stepU_at_evS ; stepU_at_evO ; stepU_at_evU ; stepU_at_evV
        ; stepU_at_evC ; stepU_at_evRbase ; stepU_at_evRstep
        ; stepU_at_rtApp2 ; stepU_at_rtC1 ; stepU_at_rtR1
        ; stepU_at_rtEmpty )

-- The layer-1 step combinator: the universal interpreter's stepU,
-- viewed under the no-mu API exported above.
open import BRA4.Base using ( Fun1 )

step : Fun1
step = stepU
