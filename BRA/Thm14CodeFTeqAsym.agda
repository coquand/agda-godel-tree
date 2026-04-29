{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm14CodeFTeqAsym
--
-- Asymmetric analog of Guard's encoded equation for Theorem 12.
-- For singulary f and Term x, encodes the formula
--
--    "f x_ = f_x_"  =  3J(3J("f", num x) + 1, num(f x))
--
-- as a Term (open in x):
--
--    codeFTeq1Asym f x  =  mkEqT (mkAp1T "f" (ap1 cor x))
--                                (ap1 cor (ap1 f x))
--
-- The "static GN" subterm (mkAp1T "f" ...) lives on the LHS with cor
-- at the variable position; the "evaluated numeral" subterm
-- (ap1 cor (ap1 f x)) lives on the RHS.
--
-- This is a sibling to BRA.Thm14CodeFTeq (the symmetric encoder) and
-- is intended for the asymmetric Theorem 12 development; see
-- BRA/THM12-ASYM-FEASIBILITY.md.
--
-- No postulates, no holes.

module BRA.Thm14CodeFTeqAsym where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Cor using (cor)

------------------------------------------------------------------------
-- Term-level GN constructors mirroring Term.mkAp1 / Term.mkAp2 (which
-- are Tree -> Tree), but accepting Term arguments so subterms can
-- contain ap1 cor x for x a free variable.

private
  tagAp1T : Term
  tagAp1T = reify tagAp1

  tagAp2T : Term
  tagAp2T = reify tagAp2

mkAp1T : Term -> Term -> Term
mkAp1T fCodeT tCodeT = ap2 Pair tagAp1T (ap2 Pair fCodeT tCodeT)

mkAp2T : Term -> Term -> Term -> Term
mkAp2T gCodeT aCodeT bCodeT =
  ap2 Pair tagAp2T (ap2 Pair gCodeT (ap2 Pair aCodeT bCodeT))

-- Equation packer: codeEqn (eqn l r) = nd (code l) (code r),
-- reified is ap2 Pair.
mkEqT : Term -> Term -> Term
mkEqT lhsT rhsT = ap2 Pair lhsT rhsT

------------------------------------------------------------------------
-- Asymmetric codeFTeq for Fun1 and Fun2.
--
-- For canonical x = reify v, both subterms reduce (in Deriv) to closed
-- Trees that together form the GN of the closed formula
--   f(reify v) = reify (f-meta v)
-- which is a theorem of BRA at every v by f's defining axioms.

codeFTeq1Asym : Fun1 -> Term -> Term
codeFTeq1Asym f x =
  mkEqT (mkAp1T (reify (codeF1 f)) (ap1 cor x))
        (ap1 cor (ap1 f x))

codeFTeq2Asym : Fun2 -> Term -> Term -> Term
codeFTeq2Asym g x v =
  mkEqT (mkAp2T (reify (codeF2 g)) (ap1 cor x) (ap1 cor v))
        (ap1 cor (ap2 g x v))

------------------------------------------------------------------------
-- Defining-equation aliases for downstream readability.

codeFTeq1Asym_eqn : (f : Fun1) (x : Term) ->
  Eq (codeFTeq1Asym f x)
     (mkEqT (mkAp1T (reify (codeF1 f)) (ap1 cor x))
            (ap1 cor (ap1 f x)))
codeFTeq1Asym_eqn f x = refl

codeFTeq2Asym_eqn : (g : Fun2) (x v : Term) ->
  Eq (codeFTeq2Asym g x v)
     (mkEqT (mkAp2T (reify (codeF2 g)) (ap1 cor x) (ap1 cor v))
            (ap1 cor (ap2 g x v)))
codeFTeq2Asym_eqn g x v = refl
