{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.EnumStep0Counter -- STEP 0 finding, MACHINE-CHECKED.
--
-- Demonstrates that the LITERAL  enum_cover  domain
--   { c : InAlph c  AND  Deriv (leq (lenR c) Lstar) }
-- is INFINITE, hence no finite-index enum can cover it.
--
-- The witness family  c_A := ap2 pi (ap1 s A) O  satisfies, for EVERY  A :
--   (1)  InAlph A  ->  InAlph c_A                         (so all c_A are in the domain)
--   (2)  Deriv (eqF (lenR c_A) (natCode 1))               (lenR is 1, INDEPENDENT of A)
-- Since there are infinitely many distinct InAlph terms A (O, s O, s (s O), ...),
-- there are infinitely many distinct c_A all with lenR = natCode 1 <= any Lstar >= 1.
-- A finite enum : {0..B} -> Term hits at most B+1 values, so cannot cover them.

module T4.EnumStep0Counter where

open import T4.Base
open import T4.LenR      using ( lenR ; lenR_at_O ; lenR_at_node )
open import T4.ProgParse using ( InAlph ; iaO ; iaS ; iaPi )

open import BRA3.Church using ( pi )

------------------------------------------------------------------------
-- The witness family.

cWit : Term -> Term
cWit A = ap2 pi (ap1 s A) O

-- (1) Every member of the family is InAlph (given A InAlph).

cWit_InAlph : (A : Term) -> InAlph A -> InAlph (cWit A)
cWit_InAlph A iaA = iaPi (ap1 s A) O (iaS A iaA) iaO

-- (2) lenR of every member is natCode 1, INDEPENDENT of A.
--     natCode 1 = ap1 s (natCode 0) = ap1 s O.

cWit_lenR : (A : Term) -> Deriv (eqF (ap1 lenR (cWit A)) (ap1 s O))
cWit_lenR A = ruleTrans (lenR_at_node A O) (cong1 s lenR_at_O)

-- Concrete inhabitants of the family with the SAME lenR = natCode 1 but
-- distinct underlying terms -- the mechanism of infiniteness, three samples.

_ : InAlph (cWit O)
_ = cWit_InAlph O iaO

_ : InAlph (cWit (ap1 s O))
_ = cWit_InAlph (ap1 s O) (iaS O iaO)

_ : InAlph (cWit (ap1 s (ap1 s O)))
_ = cWit_InAlph (ap1 s (ap1 s O)) (iaS (ap1 s O) (iaS O iaO))
