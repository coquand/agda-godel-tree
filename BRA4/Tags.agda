{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Tags -- numeric tag constants used by codeTerm / codeFormula
-- / thmT.  All tags are >= 1, leaving 0 reserved for the leaf case
-- (the bare Term  O ).  Distinct tags are picked across the three
-- namespaces (Term constructors, Fun1/Fun2 constructors, Formula
-- constructors, rule slots) so that thmT's top-level Fst-dispatch
-- on a rule tag never collides with a Term tag at the same level
-- of nesting.

module BRA4.Tags where

open import BRA4.Base

------------------------------------------------------------------------
-- Term-level constructor tags.

tag_var  : Nat
tag_var  = 1

tag_ap1  : Nat
tag_ap1  = 2

tag_ap2  : Nat
tag_ap2  = 3

------------------------------------------------------------------------
-- Fun1 / Fun2 constructor tags.

tag_s    : Nat
tag_s    = 4

tag_o    : Nat
tag_o    = 5

tag_u    : Nat
tag_u    = 6

tag_C    : Nat
tag_C    = 7

tag_v    : Nat
tag_v    = 8

tag_R    : Nat
tag_R    = 9

------------------------------------------------------------------------
-- Formula tags.

tag_eq   : Nat
tag_eq   = 10

tag_neg  : Nat
tag_neg  = 11

tag_imp  : Nat
tag_imp  = 12

------------------------------------------------------------------------
-- Rule slot tags (used by thmT's top-level dispatch).  These live in
-- a SEPARATE namespace from the Term / Formula tags above; they are
-- inspected at the top of the proof code, not inside the formula
-- code.

tag_ax   : Nat
tag_ax   = 1

tag_sb   : Nat
tag_sb   = 2

tag_mp   : Nat
tag_mp   = 3

tag_ind  : Nat
tag_ind  = 4

tag_sb2  : Nat
tag_sb2  = 5

tag_sb3  : Nat
tag_sb3  = 6
