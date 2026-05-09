{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.WellFormedIndBT -- well-formedness side condition for indBTB
-- applications.
--
-- B.indBTB e v1 v2 base step  in  BRA2.DerivTBounded  does NOT enforce
-- that  v1 , v2  are fresh in  e  or that  v1 != v2 .  These are
-- conventions that the standard induction principle relies on.
-- Without them, an  indBTB  can still be inhabited via degenerate
-- step formulas (e.g., axK-style weakening: an ill-formed step's
-- conclusion may coincide with one of its premises and is then
-- derivable from that premise alone).
--
-- For the bounded-reduction programme we keep B.indBTB unchanged
-- (avoiding the alpha-renaming refactor that strengthening the
-- axiom would force), and instead carry well-formedness as a
-- side-condition record  WellFormedIndBT  on each indBTB instance
-- that we want to eliminate.  Three components:
--
--   FreshEq v e   : v is not a free variable in e (Geq v (maxVarEq e)).
--   NotEqNat v w  : v != w (encoded for use with subst_var_diff).
--   record        : both freshness witnesses + distinctness.
--
-- Once the find-and-extract / handler architecture is validated, we
-- can decide whether to bake well-formedness into B.indBTB itself.

module BRA2.WellFormedIndBT where

open import BRA2.Base
open import BRA2.Term
open import BRA2.MaxVar
open import BRA2.SubstCompose using (maxVarEq)

------------------------------------------------------------------------
-- FreshEq v e : v is not a free variable in e.
--
-- Encoded via Geq v (maxVarEq e), since maxVarEq returns one more
-- than the highest free-variable index in e.

FreshEq : Nat -> Equation -> Set
FreshEq v e = Geq v (maxVarEq e)

------------------------------------------------------------------------
-- NotEqNat v w : v != w, encoded for direct use with subst_var_diff.

NotEqNat : Nat -> Nat -> Set
NotEqNat v w = Eq (natEq v w) false

------------------------------------------------------------------------
-- WellFormedIndBT e v1 v2 : the three side conditions an
-- indBTB e v1 v2 _ _ application must satisfy for the standard
-- induction principle to be sound for it.
--
-- distinct's argument order  v2 v1  matches stepCombinerFromStep's
-- usage:  subst_var_diff v1 v2  takes  Eq (natEq v2 v1) false .

record WellFormedIndBT (e : Equation) (v1 v2 : Nat) : Set where
  constructor mkWellFormed
  field
    fresh1   : FreshEq v1 e
    fresh2   : FreshEq v2 e
    distinct : NotEqNat v2 v1
open WellFormedIndBT public
