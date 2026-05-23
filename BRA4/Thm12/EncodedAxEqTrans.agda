{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Thm12.EncodedAxEqTrans -- encoded  ax_eqTrans  instance via THREE
-- NESTED single-variable sb-wraps on axN4  (no sbt3/sbf3).
--
-- Goal (universal in tA tB tC : Term ; tB tC inert) :
--
--   Df_axEqTrans : Term -> Term -> Term -> Term
--   encodedAxEqTrans :
--     (tA tB tC : Term) (inertB : InertU tB) (inertC : InertU tC) ->
--     Deriv (eqF (ap1 thmT (Df_axEqTrans tA tB tC))
--                 (encodedAxEqTrans_Term tA tB tC))
--
-- where  encodedAxEqTrans_Term tA tB tC  encodes
--   "(tA = tB) > ((tA = tC) > (tB = tC))" .
--
-- axN4 has no functor argument, so the inner "extra" slot is a dummy  O .
-- Nesting: var 0 := tA outermost, var 1 := tB, var 2 := tC innermost,
-- with skeleton
--   FormT x0 x1 x2 = imp (eq x0 x1) (imp (eq x0 x2) (eq x1 x2)) .

module BRA4.Thm12.EncodedAxEqTrans where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code              using ( codeFormula )
open import BRA4.SbT               using ( sbt )
open import BRA4.SbtAtVar          using ( sbt_at_var_match ; sbt_at_var_nomatch )
open import BRA4.SbF               using ( sbf )
open import BRA4.SbStep
open import BRA4.ThmT              using ( thmT )
open import BRA4.ThmTAtSb          using ( thmT_at_sb )
open import BRA4.ThmTAtAx4         using ( thmT_at_axN4 )

------------------------------------------------------------------------
-- Constants and helpers.

private
  N4 : Nat
  N4 = suc (suc (suc (suc zero)))

  cV0 : Term
  cV0 = ap2 Pair (natCode tag_var) (natCode zero)

  cV1 : Term
  cV1 = ap2 Pair (natCode tag_var) (natCode (suc zero))

  cV2 : Term
  cV2 = ap2 Pair (natCode tag_var) (natCode (suc (suc zero)))

  eqc : Term -> Term -> Term
  eqc p q = ap2 Pair (natCode tag_eq) (ap2 Pair p q)

  impc : Term -> Term -> Term
  impc a b = ap2 Pair (natCode tag_imp) (ap2 Pair a b)

  -- The encoded skeleton  "(x0 = x1) > ((x0 = x2) > (x1 = x2))" .
  FormT : Term -> Term -> Term -> Term
  FormT x0 x1 x2 = impc (eqc x0 x1) (impc (eqc x0 x2) (eqc x1 x2))

  packAx4 : Term
  packAx4 =
    ap2 Pair (natCode tag_ax)
      (ap2 Pair (natCode N4) O)

  spec0_at : Term -> Term
  spec0_at A = ap2 Pair (natCode zero) A

  spec1_at : Term -> Term
  spec1_at B = ap2 Pair (natCode (suc zero)) B

  spec2_at : Term -> Term
  spec2_at cc = ap2 Pair (natCode (suc (suc zero))) cc

------------------------------------------------------------------------
-- Df_axEqTrans  (nested sb-wrap).

Df_axEqTrans : Term -> Term -> Term -> Term
Df_axEqTrans tA tB tC =
  ap2 Pair (natCode tag_sb)
    (ap2 Pair (spec0_at tA)
      (ap2 Pair (natCode tag_sb)
        (ap2 Pair (spec1_at tB)
          (ap2 Pair (natCode tag_sb)
            (ap2 Pair (spec2_at tC) packAx4)))))

------------------------------------------------------------------------
-- Target encoded formula.

encodedAxEqTrans_Term : Term -> Term -> Term -> Term
encodedAxEqTrans_Term tA tB tC = FormT tA tB tC

------------------------------------------------------------------------
-- One pass of  sbf  over the FormT skeleton.

private
  onePassT :
    (k : Nat) (S : Term) (x0 x1 x2 x0' x1' x2' : Term) ->
    Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S) x0) x0') ->
    Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S) x1) x1') ->
    Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S) x2) x2') ->
    Deriv (eqF (ap2 sbf (ap2 Pair (natCode k) S) (FormT x0 x1 x2))
                (FormT x0' x1' x2'))
  onePassT k S x0 x1 x2 x0' x1' x2' e0 e1 e2 =
    sbf_step_imp k S
      (eqc x0 x1) (impc (eqc x0 x2) (eqc x1 x2))
      (eqc x0' x1') (impc (eqc x0' x2') (eqc x1' x2'))
      (sbf_step_atomic k S x0 x1 x0' x1' e0 e1)
      (sbf_step_imp k S
        (eqc x0 x2) (eqc x1 x2) (eqc x0' x2') (eqc x1' x2')
        (sbf_step_atomic k S x0 x2 x0' x2' e0 e2)
        (sbf_step_atomic k S x1 x2 x1' x2' e1 e2))

------------------------------------------------------------------------
-- Main theorem.

encodedAxEqTrans :
  (tA tB tC : Term) (inertB : InertU tB) (inertC : InertU tC) ->
  Deriv (eqF (ap1 thmT (Df_axEqTrans tA tB tC))
              (encodedAxEqTrans_Term tA tB tC))
encodedAxEqTrans tA tB tC inertB inertC =
  let spec0 : Term
      spec0 = spec0_at tA
      spec1 : Term
      spec1 = spec1_at tB
      spec2 : Term
      spec2 = spec2_at tC

      inner2 : Term
      inner2 = ap2 Pair (natCode tag_sb) (ap2 Pair spec2 packAx4)

      inner1 : Term
      inner1 = ap2 Pair (natCode tag_sb) (ap2 Pair spec1 inner2)

      e_axN4 : Deriv (eqF (ap1 thmT packAx4) (FormT cV0 cV1 cV2))
      e_axN4 = thmT_at_axN4 O

      innerPass :
        Deriv (eqF (ap2 sbf spec2 (FormT cV0 cV1 cV2)) (FormT cV0 cV1 tC))
      innerPass =
        onePassT (suc (suc zero)) tC cV0 cV1 cV2 cV0 cV1 tC
          (sbt_at_var_nomatch (suc (suc zero)) zero tC refl)
          (sbt_at_var_nomatch (suc (suc zero)) (suc zero) tC refl)
          (sbt_at_var_match (suc (suc zero)) tC)

      middlePass :
        Deriv (eqF (ap2 sbf spec1 (FormT cV0 cV1 tC)) (FormT cV0 tB tC))
      middlePass =
        onePassT (suc zero) tB cV0 cV1 tC cV0 tB tC
          (sbt_at_var_nomatch (suc zero) zero tB refl)
          (sbt_at_var_match (suc zero) tB)
          (inertC (suc zero) tB)

      outerPass :
        Deriv (eqF (ap2 sbf spec0 (FormT cV0 tB tC)) (FormT tA tB tC))
      outerPass =
        onePassT zero tA cV0 tB tC tA tB tC
          (sbt_at_var_match zero tA)
          (inertB zero tA)
          (inertC zero tA)

  in ruleTrans (thmT_at_sb spec0 inner1)
       (ruleTrans (congR sbf spec0 (thmT_at_sb spec1 inner2))
         (ruleTrans (congR sbf spec0 (congR sbf spec1 (thmT_at_sb spec2 packAx4)))
           (ruleTrans (congR sbf spec0 (congR sbf spec1 (congR sbf spec2 e_axN4)))
             (ruleTrans (congR sbf spec0 (congR sbf spec1 innerPass))
               (ruleTrans (congR sbf spec0 middlePass)
                          outerPass)))))
