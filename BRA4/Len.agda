{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Len -- meta-level length (node-count) of Terms.
--
-- Phase A of KRIVINE-BERRY-PLAN.md.  This is the meta-level SPEC of
-- "length"; the object functor  Len : Fun1  (to be built next via the
-- course-of-values pattern, like sbt/thmT) must compute  natCode
-- (lenMeta (code ...))  on codes.
--
-- lenMeta counts Term constructor nodes.  Functors (Fun1/Fun2) are NOT
-- Term substructure, so they are atomic at the raw-Term level; but the
-- coding functions (BRA4.Code) expand every functor into a Pair-tree of
-- natCode tags, so  lenMeta (codeFormula F)  fully accounts for F's
-- structure including its functors.
--
-- KEY FACT (the motivation for compressed numerals, BRA4.Bin):
--
--     lenMeta (natCode m) = suc m
--
-- i.e. a UNARY numeral has length linear in its value.  Hence a formula
-- that mentions a large number  m  via  natCode m  is long (>= m), which
-- would defeat the Berry self-reference  Len(B) < m0 .  Compressed
-- (binary) numerals (BRA4.Bin) give an  O(log m)  alternative.

module BRA4.Len where

open import BRA4.Base

------------------------------------------------------------------------
-- Local Nat addition (BRA3.Base provides none).

natAdd : Nat -> Nat -> Nat
natAdd zero    m = m
natAdd (suc n) m = suc (natAdd n m)

------------------------------------------------------------------------
-- Node-count of a Term.

lenMeta : Term -> Nat
lenMeta O           = suc zero
lenMeta (var k)     = suc zero
lenMeta (ap1 f t)   = suc (lenMeta t)
lenMeta (ap2 g a b) = suc (natAdd (lenMeta a) (lenMeta b))

------------------------------------------------------------------------
-- THE motivating fact:  unary numerals are length-linear.

lenMeta_natCode : (m : Nat) -> Eq (lenMeta (natCode m)) (suc m)
lenMeta_natCode zero    = refl
lenMeta_natCode (suc m) = eqCong suc (lenMeta_natCode m)

------------------------------------------------------------------------
-- A Pair node costs one plus the cost of its two children (definitional,
-- but recorded as the closure-shape the object  Len  functor will mirror).

lenMeta_Pair :
  (a b : Term) ->
  Eq (lenMeta (ap2 Pair a b)) (suc (natAdd (lenMeta a) (lenMeta b)))
lenMeta_Pair a b = refl
