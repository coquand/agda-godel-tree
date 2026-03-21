{-# OPTIONS --without-K --exact-split #-}

module ChwistekDiagonal where

open import ChwistekSyntax

------------------------------------------------------------------------
-- A. Schema syntax
------------------------------------------------------------------------

-- A schema is a formula with one hole, to be filled by a Code value.
-- Parallel to Formula but with shole in place of a leaf.

data Schema : Set where
  shole  : Schema
  sconst : Formula -> Schema
  simp   : Schema -> Schema -> Schema
  sall   : Schema -> Schema

------------------------------------------------------------------------
-- B. Instantiation by Code
------------------------------------------------------------------------

-- instantiate S c fills the hole in S with fcode c.
-- Structurally recursive on S.

instantiate : Schema -> Code -> Formula
instantiate shole c      = fcode c
instantiate (sconst A) c = A
instantiate (simp S T) c = fimp (instantiate S c) (instantiate T c)
instantiate (sall S) c   = fall (instantiate S c)

------------------------------------------------------------------------
-- C. Encoding schemas into Code
------------------------------------------------------------------------

-- Tag scheme for schemas (continues from ChwistekSyntax tags 0-7):
--   catom 10 = shole marker
--   catom 11 = sconst marker
--   catom 12 = simp marker
--   catom 13 = sall marker

encSchema : Schema -> Code
encSchema shole      = catom (suc (suc (suc (suc (suc
                        (suc (suc (suc (suc (suc zero))))))))))
encSchema (sconst A) =
  cnode (catom (suc (suc (suc (suc (suc
          (suc (suc (suc (suc (suc (suc zero))))))))))))
        (encFormula A)
encSchema (simp S T) =
  cnode (catom (suc (suc (suc (suc (suc
          (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))
        (cnode (encSchema S) (encSchema T))
encSchema (sall S)   =
  cnode (catom (suc (suc (suc (suc (suc
          (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))
        (encSchema S)

------------------------------------------------------------------------
-- D. Diagonalization
------------------------------------------------------------------------

-- diag S feeds schema S its own code.
-- This is finite, terminating, and requires no tricks.
-- It is the syntax-native analogue of Guard's Df / Goedel's diagonal lemma.

diag : Schema -> Formula
diag S = instantiate S (encSchema S)

------------------------------------------------------------------------
-- E. Basic correctness property
------------------------------------------------------------------------

-- The diagonal property holds definitionally.

diag-unfold :
  (S : Schema) ->
  Eq (diag S) (instantiate S (encSchema S))
diag-unfold S = refl

------------------------------------------------------------------------
-- F. Examples
------------------------------------------------------------------------

-- Example 1: "the code of this schema implies false"
-- Snot = hole -> bot

Snot : Schema
Snot = simp shole (sconst fbot)

-- Proto-Goedel sentence: diag Snot = fimp (fcode (encSchema Snot)) fbot
-- This says: "the code of Snot implies falsity"

G : Formula
G = diag Snot

-- Example 2: "for all x, the code of this schema implies false"
-- Sallnot = forall (hole -> bot)

Sallnot : Schema
Sallnot = sall (simp shole (sconst fbot))

-- diag Sallnot = fall (fimp (fcode (encSchema Sallnot)) fbot)

G2 : Formula
G2 = diag Sallnot

------------------------------------------------------------------------
-- G. Design notes
------------------------------------------------------------------------

-- Why Code is used instead of Formula self-embedding:
--
--   A definition like diag S = instantiate S (quoteF (diag S)) where
--   quoteF : Formula -> Formula would produce an infinite term:
--   the result formula would contain itself as a subformula.
--   Agda's termination checker correctly rejects this.
--
--   By using Code as the medium of self-reference, the formula
--   diag S = instantiate S (encSchema S) is finite: it contains
--   the *code* of the schema, not the formula itself. This is
--   exactly how real diagonalization works: a sentence refers to
--   its own Goedel number (code), not to itself directly.
--
-- Connection to Chwistek and Guard:
--
--   Guard's Df(x) = Sb(x, n(x)) applies a formula to its own number.
--   Our diag S = instantiate S (encSchema S) does the same thing
--   in tree-native syntax: apply a schema to its own code.
--
-- Next steps:
--
--   1. Define a provability predicate as a Formula (or Schema)
--   2. Connect fcode/encSchema with proof encoding
--   3. Build the Goedel sentence: a formula that says
--      "the code of this schema is not provable"
--   4. Derive unprovability from consistency assumptions
