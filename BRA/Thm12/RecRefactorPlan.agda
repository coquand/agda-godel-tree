{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm12.RecRefactorPlan
--
-- Phase 7c, Step 2 (proof-of-concept assessment).
--
-- Documents the new design for  Parts/Rec.Construction  using the
-- Rec primitive itself (rather than IfLf-dispatch + parametric NN_fun).
-- This sidesteps the Fun2-self-reference circularity discovered when
-- attempting TreeEq NN, by leveraging  axRecNd 's runtime evaluation
-- to supply cross-IH Term values via the  recs  argument.
--
-- This file is DESIGN ONLY; no executable construction.  Concrete
-- implementation deferred to next session per user's "stop and assess"
-- instruction.

module BRA.Thm12.RecRefactorPlan where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor
open import BRA.Thm.ThmT using (thmT)

------------------------------------------------------------------------
-- The new design: D_Rec_zs as Rec-primitive application.
--
-- Old design (Phase 6):
--   D_Rec_zs = Comp2 IfLf I (Comp2 Pair (KT (parEncAxRecLf zT sT)) D_Rec_NN_fun)
--   D_Rec_NN_fun is a Fun1 PARAMETER that handles the Pair-case.
--   To embed cross-IH (ap1 D_Rec_zs a) inside D_Rec_NN_fun's image,
--   D_Rec_NN_fun must structurally embed D_Rec_zs.  CIRCULARITY.
--
-- New design (Phase 7c):
--   D_Rec_zs = Rec (parEncAxRecLf zT sT) D_Rec_zs_step
--   D_Rec_zs_step : Fun2 (a CLOSED Fun2 expression in (orig, recs))
--   By axRecLf O step:  ap1 D_Rec_zs O = parEncAxRecLf zT sT.
--   By axRecNd:         ap1 D_Rec_zs (Pair a b)
--                         = ap2 D_Rec_zs_step (Pair a b)
--                                              (Pair (ap1 D_Rec_zs a)
--                                                    (ap1 D_Rec_zs b)).
--   The cross-IH Term values  (ap1 D_Rec_zs a)  and  (ap1 D_Rec_zs b)
--   are SUPPLIED BY axRecNd's evaluation at runtime as the recs slot.
--   D_Rec_zs_step extracts them via Snd / Fst on its second arg.
--   D_Rec_zs_step's Fun2 expression has NO structural reference to
--   D_Rec_zs -- it operates on (orig, recs) abstractly.

------------------------------------------------------------------------
-- Step Fun2 sketch.
--
-- D_Rec_zs_step takes (orig, recs) where:
--   orig = Pair a b   (the input pair to D_Rec_zs)
--   recs = Pair recA recB  with  recA = ap1 D_Rec_zs a , recB = ap1 D_Rec_zs b
--
-- Output: encoded chain Term whose thmT-image is codeFTeq1 (Rec z s) (Pair a b).
--
-- The chain (Term-level):
--   y1 = parEncAxRecNd-at-cor-folded-args
--          encoded "Rec(z,s)(Pair (cor a) (cor b))
--                     = s(Pair (cor a) (cor b),
--                         Pair (Rec(z,s)(cor a)) (Rec(z,s)(cor b)))"
--   y2 = parEncCongR (codeF2 s) (parEncCongR Pair (parEncCongL Pair recA xT_b) ... )
--          rewrite first "Rec(z,s)(cor a)" -> "cor(Rec(z,s) a)" using cross-IH
--   y3 = ... rewrite second using recB ...
--   y4 = D_correct2_s applied at cor-folded args
--          rewrite s(...) -> cor(s(...)) -> cor(Rec(z,s)(Pair a b))
--   bridge = ruleSym (cong1 cor (axRecNd z s a b))
--
-- D_Rec_zs_step's body builds this chain at the Term level using
-- combinators:  Fan, Lift, Comp, Comp2, KT, Pair  applied to (orig, recs).
-- Estimated ~150-200 LoC for the Fun2 expression.

------------------------------------------------------------------------
-- Construction interface change.
--
-- module Construction
--   (z : Term) (s : Fun2)
--   (z_corLemma : Deriv (ap1 cor z = reify (code z)))
--   where
--   D_Rec_zs : Fun1
--   D_Rec_zs = Rec (parEncAxRecLf zT sT) D_Rec_zs_step
--
--   D_Rec_zs_step : Fun2
--   D_Rec_zs_step = -- closed expression building chain
--
--   D_correct_Rec_zs_O : Deriv (...)
--   D_correct_Rec_zs_O = -- via axRecLf + parDispAxRecLf + bridgeO
--
--   D_correct_Rec_zs_Nd :
--     (a b : Term)
--     (cross_IH_a : Deriv (atomic (eqn (ap1 thmT (ap1 D_Rec_zs a))
--                                       (codeFTeq1_Rec_zs z s a))))
--     (cross_IH_b : Deriv (atomic (eqn (ap1 thmT (ap1 D_Rec_zs b))
--                                       (codeFTeq1_Rec_zs z s b))))
--     (cross_IH_s : (x v : Term) ->
--          Deriv (atomic (eqn (ap1 thmT (ap2 D2_s x v))
--                              (codeFTeq2 s x v))))
--     -> Deriv (atomic (eqn (ap1 thmT (ap1 D_Rec_zs (ap2 Pair a b)))
--                            (codeFTeq1_Rec_zs z s (ap2 Pair a b))))
--   D_correct_Rec_zs_Nd a b cIH_a cIH_b cIH_s = -- chain proof using parDispRuleTrans + cross-IH applications

------------------------------------------------------------------------
-- Phase 7 mutual recursion:  the Fun1-CASE D Rec
--
-- mutual
--   D_correct : (f : Fun1) (x : Term) -> Deriv (codeFTeq1 f x)
--   D_correct (Rec z s) (ap2 Pair a b) =
--     let module R = Construction z s (z_corLemma_for z)
--         cross_IH_a = D_correct (Rec z s) a
--         cross_IH_b = D_correct (Rec z s) b
--         cross_IH_s = D_correct2 s
--     in R.D_correct_Rec_zs_Nd a b cross_IH_a cross_IH_b cross_IH_s
--   D_correct (Rec z s) O = R.D_correct_Rec_zs_O
--   ...
--
-- Termination: D_correct (Rec z s) (ap2 Pair a b) -> D_correct (Rec z s) a
-- (recursion on the Term arg, structurally smaller).  Agda accepts.
--
-- For non-canonical x (var, ap1, ap2 with non-Pair g), use ruleInst on
-- a universal D_correct_Rec_zs_univ proof.  The universal can be built
-- via ruleIndBT inside Construction (where the inner ruleIndBT step
-- proof, at concrete Pair (var v1) (var v2), uses
--   D_correct_Rec_zs_Nd (var v1) (var v2) cross_IH_v1 cross_IH_v2 ...
-- with cross_IHs constructed at fresh-var arguments via standard
-- substitution machinery -- NO Hilbert deduction needed because the
-- IH-supply is at the Agda mutual-recursion level).

------------------------------------------------------------------------
-- WHY THIS DESIGN AVOIDS THE PHASE 7c OBSTRUCTION:
--
-- The previous obstruction:  D_TreeEq_NN_fun  must structurally embed
-- D_TreeEq  (universal, also containing D_TreeEq_NN_fun).  Infinite Fun2.
--
-- Resolution:  eliminate the NN_fun parameter.  The universal D
-- functor is BUILT VIA THE Rec / RecP / TreeEq PRIMITIVE itself,
-- which provides recursive evaluation via axRecNd / axRecPNd /
-- axTreeEqNN.  At runtime, recs / sub-pair Term values are passed
-- via the primitive's evaluation, NOT via Fun2 self-reference.
--
-- The structural circularity disappears because:
--   - D_X is a CLOSED Fun1/Fun2 expression (Rec base step).
--   - The step Fun2 has no reference to D_X (operates on (orig, recs)).
--   - Cross-IH Term values come via runtime  recs , NOT structural embedding.
--
-- The cross-IH AT THE DERIV LEVEL (proofs about thmT-images) flow via
-- Phase 7's Agda mutual recursion -- handled at the language layer,
-- not at the Hilbert proof layer.  No deduction theorem needed.

------------------------------------------------------------------------
-- ESTIMATED COST OF FULL IMPLEMENTATION:
--
-- Parts/Rec.agda refactor   ~250 LoC (chain construction in step Fun2 + chain proof)
-- Parts/RecP.agda refactor  ~250 LoC (analogous)
-- Parts/TreeEq.agda refactor ~400 LoC (TreeEq has 4 cases LL/LN/NL/NN;
--                                       NN is the largest chain)
-- Phase 7 mutual recursion   ~100 LoC (Thm12.agda updates)
-- TOTAL: ~1000 LoC across 3 Parts files + Thm12.agda.
--
-- NEXT-SESSION ENTRY POINT: implement Parts/Rec.agda new Construction
-- (smallest of the three; sets the pattern).  Then mirror for RecP, TreeEq.
