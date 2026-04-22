{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.Provable -- propositional layer above the equational Deriv.
--
-- Following Guard 1963 (BRA, axioms 11, 12, 13 + modus ponens +
-- substitution + induction).  This module gives the data-type and
-- the propositional axioms; substitution at the Formula level is
-- defined in Guard.Provable (step 2 of GUARD-BRA-TEMPLATE.md).
--
-- Single-hypothesis form  Provable hyp P  mirrors  Deriv hyp eq .
-- Multi-hypothesis reasoning emulated via P imp Q (cf. deduction
-- theorem in Guard.ProvableLemmas).
--
-- Equality at the Provable layer (Guard ax 4-7) is provided as
-- LEMMAS in Guard.ProvableEqLifts via fromDeriv + axK wrapping; not
-- as primitive constructors here.
--
-- No postulates, no holes.  Compiles under --safe --without-K
-- --exact-split.

module Guard.Provable where

open import Guard.Base
open import Guard.Term
open import Guard.Step using (Deriv)
open import Guard.Formula

------------------------------------------------------------------------
-- Provable hyp P : "from a single Formula hypothesis hyp, P is
-- derivable using BRA-style propositional rules".

data Provable (hyp : Formula) : Formula -> Set where

  ------------------------------------------------------------------
  -- Embedding from the Deriv layer.
  --
  -- Any Deriv-level fact polymorphic in its hypothesis (i.e., a
  -- THEOREM of the equational system) lifts to an atomic Provable
  -- at any Provable-level hyp.

  fromDeriv : {eq : Equation} ->
              ({h : Equation} -> Deriv h eq) ->
              Provable hyp (atomic eq)

  ------------------------------------------------------------------
  -- Hypothesis.

  ruleHypP : Provable hyp hyp

  ------------------------------------------------------------------
  -- Propositional axioms (Guard 1963 BRA, axioms 11, 12, 13).

  -- Axiom 11 (K):  P ⊃ . Q ⊃ P .
  axK : (P Q : Formula) ->
        Provable hyp (P imp (Q imp P))

  -- Axiom 12 (S):  P ⊃ (Q ⊃ R) ⊃ . P ⊃ Q ⊃ . P ⊃ R .
  axS : (P Q R : Formula) ->
        Provable hyp ((P imp (Q imp R))
                       imp ((P imp Q) imp (P imp R)))

  -- Axiom 13 (classical contraposition):  ~P ⊃ ~Q ⊃ . Q ⊃ P .
  axNeg : (P Q : Formula) ->
          Provable hyp ((not P) imp ((not Q) imp (Q imp P)))

  ------------------------------------------------------------------
  -- Modus ponens.

  mp : {P Q : Formula} ->
       Provable hyp (P imp Q) ->
       Provable hyp P ->
       Provable hyp Q

------------------------------------------------------------------------
-- Note on the substitution rule.
--
-- Guard 1963 lists "substitution of terms for numerical variables" as
-- an inference rule (page 10).  In our hypothesis-bearing form, a
-- substitution rule  Provable hyp P -> Provable hyp (substF x t P)
-- carries the standard side condition  "x not free in hyp"  (else
-- the deduction theorem case for substitution does not match the
-- expected type).
--
-- For simplicity, we OMIT a substitution rule from the Provable
-- constructor list.  Substitution is provided as a META-level Agda
-- function (substProv) acting on Provable derivation trees, defined
-- in Guard.ProvableSubst (TODO).  Each use site that requires
-- substitution invokes substProv directly, with the side condition
-- (when needed) discharged by the caller's choice of hyp.
