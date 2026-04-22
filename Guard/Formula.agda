{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.Formula -- propositional formulas above the equational layer.
--
-- Following Guard 1963 (BRA, lecture notes p.10), formulas are
-- atomic equations or propositional combinations using ~ and ⊃.
-- We use ASCII names matching our project conventions:
--   atomic eq    -- A = B  (an Equation)
--   not_ P       -- ~ P
--   _imp_ P Q    -- P ⊃ Q

module Guard.Formula where

open import Guard.Base
open import Guard.Term using (Equation ; Term ; substEq)

------------------------------------------------------------------------
-- Formula: propositional combination of atomic equations.
--
-- Following Guard's BRA (axioms 11, 12, 13 use only ~ and ⊃ as
-- propositional connectives; other connectives could be defined as
-- abbreviations later if needed).

data Formula : Set where
  atomic : Equation -> Formula
  not_   : Formula -> Formula
  _imp_  : Formula -> Formula -> Formula

infixr 5 not_
infixr 4 _imp_

------------------------------------------------------------------------
-- Substitution at the Formula level: replace variable x with term t.
--
-- Atomic equations use the existing substEq (Guard.Term).
-- Compound formulas recurse structurally.

substF : Nat -> Term -> Formula -> Formula
substF x t (atomic eq) = atomic (substEq x t eq)
substF x t (not P)     = not (substF x t P)
substF x t (P imp Q)   = (substF x t P) imp (substF x t Q)
