{-# OPTIONS --safe --without-K --exact-split #-}

module Rose.Equation where

open import Rose.Base using (Nat; zero)
open import Rose.Term using (Term)

------------------------------------------------------------------------
-- Equations between closed terms.
--
-- Rose's system has equation schemas with free numerical and function
-- variables.  We start with closed equations (Term 0 = Term 0) and
-- will generalise to open equations (Term n = Term n) when axiom
-- schemas are introduced.

record Equation : Set where
  constructor equation
  field
    lhs : Term zero
    rhs : Term zero
