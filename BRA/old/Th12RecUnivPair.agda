{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Th12RecUnivPair
--
-- Proof of concept: instantiate Th12RecUniv.WithClosure with s = Pair,
-- discharging the ih_s_bra parameter via corOfPair (which is exactly the
-- BRA-Deriv form of ih_s_bra at s = Pair).
--
-- This delivers Theorem 12 for Rec O Pair UNCONDITIONALLY at the
-- universal-in-x case (var 0 free in the formula).
--
-- The pattern: for s = Pair, ih_s_bra := \ a b -> ruleSym (corOfPair a b),
-- which has the right type because cor (Pair a b) = mkAp2T (codeF2 Pair)
-- (cor a) (cor b) is exactly corOfPair's content.
--
-- For other Fun2 constructors of s, ih_s_bra requires a different
-- discharge (and for s = Const it is mathematically infeasible at the
-- specific Pair-rec inputs Th12RecUniv uses); a different chain Df
-- design would be needed for those cases.  See BRA/CorF.agda for the
-- corF1/corF2 mutual recursion that handles all cases at the
-- "simplified cor" level.
--
-- No postulates, no holes, --safe --without-K --exact-split.

module BRA.Th12RecUnivPair where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor               using (cor ; stepCor)
open import BRA.CorOfPair         using (corOfPair)
open import BRA.Thm14CodeFTeqAsym using (mkAp2T)
import BRA.Th12RecUniv

------------------------------------------------------------------------
-- z = O case: z_corLemma = axRecLf O stepCor.

-- Closure of O over substitution.
O_closed : (x : Nat) (r : Term) -> Eq (subst x r O) O
O_closed x r = refl

-- Closure of Pair (Fun2) over substitution.
Pair_closed : (x : Nat) (r : Term) -> Eq (substF2 x r Pair) Pair
Pair_closed x r = refl

-- z_corLemma at z = O: cor O = O = reify (code O) = reify lf.
-- (code O = lf, reify lf = O, all definitional.)
z_corLemma_O : Deriv (atomic (eqn (ap1 cor O) (reify (code O))))
z_corLemma_O = axRecLf O stepCor

------------------------------------------------------------------------
-- ih_s_bra for s = Pair.
--
-- Goal: (a b : Term) ->
--   Deriv (atomic (eqn (mkAp2T (reify (codeF2 Pair)) (ap1 cor a) (ap1 cor b))
--                       (ap1 cor (ap2 Pair a b))))
--
-- corOfPair gives the reverse direction:
--   ap1 cor (ap2 Pair a b) = mkAp2T (reify (codeF2 Pair)) (cor a) (cor b)
-- so we ruleSym.

ih_s_bra_Pair : (a b : Term) ->
  Deriv (atomic (eqn (mkAp2T (reify (codeF2 Pair)) (ap1 cor a) (ap1 cor b))
                     (ap1 cor (ap2 Pair a b))))
ih_s_bra_Pair a b = ruleSym (corOfPair a b)

------------------------------------------------------------------------
-- Instantiate Th12RecUnivCase at (z := O, s := Pair).

module RecOPair = BRA.Th12RecUniv.Th12RecUnivCase
                    O                -- z
                    Pair             -- s
                    z_corLemma_O     -- z_corLemma
                    O_closed         -- z_closed
                    Pair_closed      -- s_closed

-- Instantiate WithClosure with ih_s_bra_Pair.
module RecOPairWC = RecOPair.WithClosure ih_s_bra_Pair

------------------------------------------------------------------------
-- The headline export: Theorem 12 for Rec O Pair, universal in x.

Th12_F1_Rec_O_Pair : Deriv RecOPair.P_Th12_Rec_zs
Th12_F1_Rec_O_Pair = RecOPairWC.Th12_F1_Rec_zs_concrete

-- The Df chain Fun1 (universally usable in the diagonal construction).
Df_F1_Rec_O_Pair : Fun1
Df_F1_Rec_O_Pair = RecOPair.Df_F1_Rec_zs
