{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm14CodeFTeq
--
-- Concrete definition of  codeFTeq : Term -> Term -> Term  in
-- SYMMETRIC form: just  reify  of  codeFormula  applied to the atomic
-- equation.  This matches what  encode  (BRA.Thm.ThmT) produces for
-- atomic equations, so:
--
--   * Thm 12 base cases reduce to one-line uses of  thmTDisp<Ax>  /
--     encode applied to  axRefl .
--
--   * Thm 13 reduces to a one-line use of  encode  on the
--     hypothesis derivation directly.
--
-- Earlier asymmetric reading (codeT recursive on LHS, cor on RHS) was
-- diagnosed in BRA/Thm12ExpAxI.agda as fundamentally incompatible with
-- ThmT.agda's symmetric  axRefl  dispatch -- BRA's Fun1 combinators
-- cannot introduce free variables ( ap1 cor (var n) ) in their output
-- from closed inputs.  Reverting to symmetric (option 4) is the
-- pragmatic choice.

module BRA.Thm14CodeFTeq where

open import BRA.Base
open import BRA.Term
open import BRA.Formula

------------------------------------------------------------------------
-- codeFTeq : Term -> Term -> Term .  Symmetric.

codeFTeq : Term -> Term -> Term
codeFTeq alpha beta = reify (codeFormula (atomic (eqn alpha beta)))

------------------------------------------------------------------------
-- Defining-equation alias for downstream readability.

codeFTeq_eqn : (alpha beta : Term) ->
               Eq (codeFTeq alpha beta)
                  (reify (codeFormula (atomic (eqn alpha beta))))
codeFTeq_eqn alpha beta = refl
