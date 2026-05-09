{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm14Numerals
--
-- Phase A of the Theorem 14 closure (NEXT-SESSION-THM14-CONSTR5.md):
-- closed encoded witnesses for Guard's transitivity tautology  t  and
-- ex-falso tautology  t' .
--
-- Guard p.16-17 uses:
--   t  =  (x_0 = x_2)  ⊃ . (x_1 = x_2)  ⊃ . (x_0 = x_1)            -- "transitivity"
--   t' =  (x_0 = x_1)  ⊃ . (~ (x_0 = x_1))  ⊃ . (0 = 1)            -- "ex-falso"
--
-- This file builds:
--
--   t_formula  : Formula
--   t_deriv    : Deriv t_formula
--   t_term     : Tree                                -- = fst (encode _ t_deriv)
--   t_witness  : Deriv (atomic (eqn (ap1 thmT (reify t_term))
--                                    (reify (codeFormula t_formula))))
--
--   t'_formula : Formula
--   t'_deriv   : Deriv t'_formula
--   t'_term    : Tree
--   t'_witness : Deriv (atomic (eqn (ap1 thmT (reify t'_term))
--                                    (reify (codeFormula t'_formula))))
--
-- These are CLOSED witnesses (no free meta-Pi).  Phases B-D will
-- (a) substitute Guard's f / g / h / K / constr5 numerals on the
-- relevant variable positions (Phase B: build the Fun1 functors), and
-- (b) lift everything under the antecedent  P = PrAtX x  (Phase C).
--
-- ASCII only.  No postulates, no holes, no with-abstraction, no dot
-- patterns.  No new Deriv constructors.

module BRA2.Thm14Numerals where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.DerivThreshold

open import BRA2.Thm.ThmT using (thmT)
open BRA2.Thm.ThmT.WithDispatch using (encode)

open import BRA2.Thm.EvalHelpers
  using ( liftAxiom ; B_combinator
        ; liftAxiomTwo ; B_combinatorTwo
        ; liftedAxEqTransTwo ; liftedRuleSymTwo ; liftedRuleTransTwo
        )

open import BRA2.GoedelII using (bot)

----------------------------------------------------------------------
-- Variable name conveniences (Guard's x_0, x_1, x_2).

x0 : Term
x0 = var zero

x1 : Term
x1 = var (suc zero)

x2 : Term
x2 = var (suc (suc zero))

----------------------------------------------------------------------
-- Equational atoms used by Guard's t and t' .

eq01 : Formula
eq01 = atomic (eqn x0 x1)

eq02 : Formula
eq02 = atomic (eqn x0 x2)

eq12 : Formula
eq12 = atomic (eqn x1 x2)

----------------------------------------------------------------------
-- t_formula : (x_0 = x_2)  ⊃ . (x_1 = x_2)  ⊃ . (x_0 = x_1) .
--
-- This is NOT directly  axEqTrans 's shape.  axEqTrans applied to
-- (a, b, c) yields  (a = b)  ⊃ . (a = c)  ⊃ . (b = c) , which differs
-- in the second antecedent's variable order from Guard's  t .  We
-- derive  t_deriv  via doubly-lifted  ruleSym  +  ruleTrans  beneath
-- the two antecedents.

t_formula : Formula
t_formula = eq02 imp (eq12 imp eq01)

----------------------------------------------------------------------
-- t_deriv .
--
-- Construction.  Set
--   P1 = eq02 = atomic (eqn x0 x2)
--   P2 = eq12 = atomic (eqn x1 x2)
--   R  = eq01 = atomic (eqn x0 x1)
--
-- Goal:  Deriv (P1 imp (P2 imp R)) .
--
-- Beneath the double-lifting:
--   d_P1  : P1 imp (P2 imp atomic (eqn x0 x2))   -- = axK P1 P2 (P1 itself).
--   d_P2  : P1 imp (P2 imp atomic (eqn x1 x2))   -- = liftAxiom P1 (axImpRefl P2).
--   d_Sym : P1 imp (P2 imp atomic (eqn x2 x1))   -- = liftedRuleSymTwo on d_P2.
--   d_T   : P1 imp (P2 imp atomic (eqn x0 x1))   -- = liftedRuleTransTwo on d_P1, d_Sym.

axImpRefl : (P : Formula) -> Deriv (P imp P)
axImpRefl P =
  mp (mp (axS P (P imp P) P)
         (axK P (P imp P)))
     (axK P P)

t_deriv : Deriv t_formula
t_deriv =
  let
      d_P1 : Deriv (eq02 imp (eq12 imp atomic (eqn x0 x2)))
      d_P1 = axK eq02 eq12

      d_P2 : Deriv (eq02 imp (eq12 imp atomic (eqn x1 x2)))
      d_P2 = liftAxiom eq02 (axImpRefl eq12)

      d_Sym : Deriv (eq02 imp (eq12 imp atomic (eqn x2 x1)))
      d_Sym = liftedRuleSymTwo eq02 eq12 x1 x2 d_P2

      d_T : Deriv (eq02 imp (eq12 imp atomic (eqn x0 x1)))
      d_T = liftedRuleTransTwo eq02 eq12 x0 x2 x1 d_P1 d_Sym
  in d_T

----------------------------------------------------------------------
-- Encoded form of t_deriv .

t_encoded :
  Sigma Term (\ y ->
    Sigma (IsValue y) (\ _ ->
      Deriv (atomic (eqn (ap1 thmT (reify y))
                         (reify (codeFormula t_formula))))))
t_encoded = encode t_formula t_deriv

t_term : Term
t_term = fst t_encoded

t_term_isValue : IsValue t_term
t_term_isValue = fst (snd t_encoded)

t_witness :
  Deriv (atomic (eqn (ap1 thmT (reify t_term))
                     (reify (codeFormula t_formula))))
t_witness = snd (snd t_encoded)

----------------------------------------------------------------------
-- t'_formula : (x_0 = x_1) ⊃ . ~(x_0 = x_1) ⊃ . (0 = 1) .
--
-- This is exactly  axExFalso eq01 bot  (after currying).

t'_formula : Formula
t'_formula = eq01 imp ((not eq01) imp bot)

t'_deriv : Deriv t'_formula
t'_deriv = axExFalso eq01 bot

----------------------------------------------------------------------
-- Encoded form of t'_deriv .

t'_encoded :
  Sigma Term (\ y ->
    Sigma (IsValue y) (\ _ ->
      Deriv (atomic (eqn (ap1 thmT (reify y))
                         (reify (codeFormula t'_formula))))))
t'_encoded = encode t'_formula t'_deriv

t'_term : Term
t'_term = fst t'_encoded

t'_term_isValue : IsValue t'_term
t'_term_isValue = fst (snd t'_encoded)

t'_witness :
  Deriv (atomic (eqn (ap1 thmT (reify t'_term))
                     (reify (codeFormula t'_formula))))
t'_witness = snd (snd t'_encoded)
