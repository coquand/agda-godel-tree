{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Thm12.EncodedAxEqCongR -- encoded  ax_eqCongR  instance via THREE
-- NESTED single-variable sb-wraps on axN7  (no sbt3/sbf3).
--
-- Goal (universal in g : Fun2, tA tB tC : Term ; tB tC inert) :
--
--   Df_axEqCongR : Fun2 -> Term -> Term -> Term -> Term
--   encodedAxEqCongR :
--     (g : Fun2) (tA tB tC : Term) (inertB : InertU tB) (inertC : InertU tC) ->
--     Deriv (eqF (ap1 thmT (Df_axEqCongR g tA tB tC))
--                 (encodedAxEqCongR_Term g tA tB tC))
--
-- where  encodedAxEqCongR_Term g tA tB tC  encodes
--   "(tA = tB) > (g(tC, tA) = g(tC, tB))" .
--
-- Same nesting discipline as EncodedAxEqCongL (var 0 := tA outermost,
-- var 1 := tB, var 2 := tC innermost), with skeleton
--   FormR g x0 x1 x2 = imp (eq x0 x1) (eq (g x2 x0) (g x2 x1)) .

module BRA4.Thm12.EncodedAxEqCongR where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code              using ( codeFun2 )
open import BRA4.SbT               using ( sbt )
open import BRA4.SbtAtVar          using ( sbt_at_var_match ; sbt_at_var_nomatch )
open import BRA4.SbF               using ( sbf )
open import BRA4.SbStep
open import BRA4.ThmT              using ( thmT )
open import BRA4.ThmTAtSb          using ( thmT_at_sb )
open import BRA4.ThmTAtAx7         using ( thmT_at_axN7 )

------------------------------------------------------------------------
-- Constants and helpers.

private
  N7 : Nat
  N7 = suc (suc (suc (suc (suc (suc (suc zero))))))

  cV0 : Term
  cV0 = ap2 Pair (natCode tag_var) (natCode zero)

  cV1 : Term
  cV1 = ap2 Pair (natCode tag_var) (natCode (suc zero))

  cV2 : Term
  cV2 = ap2 Pair (natCode tag_var) (natCode (suc (suc zero)))

  cAp2g : Fun2 -> Term -> Term -> Term
  cAp2g g a b = ap2 Pair (natCode tag_ap2) (ap2 Pair (codeFun2 g) (ap2 Pair a b))

  -- The encoded skeleton  "(x0 = x1) > (g(x2,x0) = g(x2,x1))" .
  FormR : Fun2 -> Term -> Term -> Term -> Term
  FormR g x0 x1 x2 =
    ap2 Pair (natCode tag_imp)
      (ap2 Pair (ap2 Pair (natCode tag_eq) (ap2 Pair x0 x1))
                (ap2 Pair (natCode tag_eq)
                  (ap2 Pair (cAp2g g x2 x0) (cAp2g g x2 x1))))

  packAx7_codeF2 : Fun2 -> Term
  packAx7_codeF2 g =
    ap2 Pair (natCode tag_ax)
      (ap2 Pair (natCode N7) (codeFun2 g))

  spec0_at : Term -> Term
  spec0_at A = ap2 Pair (natCode zero) A

  spec1_at : Term -> Term
  spec1_at B = ap2 Pair (natCode (suc zero)) B

  spec2_at : Term -> Term
  spec2_at cc = ap2 Pair (natCode (suc (suc zero))) cc

------------------------------------------------------------------------
-- Df_axEqCongR  (nested sb-wrap).

Df_axEqCongR : Fun2 -> Term -> Term -> Term -> Term
Df_axEqCongR g tA tB tC =
  ap2 Pair (natCode tag_sb)
    (ap2 Pair (spec0_at tA)
      (ap2 Pair (natCode tag_sb)
        (ap2 Pair (spec1_at tB)
          (ap2 Pair (natCode tag_sb)
            (ap2 Pair (spec2_at tC) (packAx7_codeF2 g))))))

------------------------------------------------------------------------
-- Target encoded formula.

encodedAxEqCongR_Term : Fun2 -> Term -> Term -> Term -> Term
encodedAxEqCongR_Term g tA tB tC = FormR g tA tB tC

------------------------------------------------------------------------
-- One pass of  sbf  over the FormR skeleton.

private
  onePassR :
    (g : Fun2) (k : Nat) (S : Term) (x0 x1 x2 x0' x1' x2' : Term) ->
    Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S) x0) x0') ->
    Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S) x1) x1') ->
    Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S) x2) x2') ->
    Deriv (eqF (ap2 sbf (ap2 Pair (natCode k) S) (FormR g x0 x1 x2))
                (FormR g x0' x1' x2'))
  onePassR g k S x0 x1 x2 x0' x1' x2' e0 e1 e2 =
    sbf_step_imp k S
      (ap2 Pair (natCode tag_eq) (ap2 Pair x0 x1))
      (ap2 Pair (natCode tag_eq) (ap2 Pair (cAp2g g x2 x0) (cAp2g g x2 x1)))
      (ap2 Pair (natCode tag_eq) (ap2 Pair x0' x1'))
      (ap2 Pair (natCode tag_eq) (ap2 Pair (cAp2g g x2' x0') (cAp2g g x2' x1')))
      (sbf_step_atomic k S x0 x1 x0' x1' e0 e1)
      (sbf_step_atomic k S
        (cAp2g g x2 x0) (cAp2g g x2 x1) (cAp2g g x2' x0') (cAp2g g x2' x1')
        (sbt_step_ap2 k S g x2 x0 x2' x0' e2 e0)
        (sbt_step_ap2 k S g x2 x1 x2' x1' e2 e1))

------------------------------------------------------------------------
-- Main theorem.

encodedAxEqCongR :
  (g : Fun2) (tA tB tC : Term) (inertB : InertU tB) (inertC : InertU tC) ->
  Deriv (eqF (ap1 thmT (Df_axEqCongR g tA tB tC))
              (encodedAxEqCongR_Term g tA tB tC))
encodedAxEqCongR g tA tB tC inertB inertC =
  let spec0 : Term
      spec0 = spec0_at tA
      spec1 : Term
      spec1 = spec1_at tB
      spec2 : Term
      spec2 = spec2_at tC

      pa : Term
      pa = packAx7_codeF2 g

      inner2 : Term
      inner2 = ap2 Pair (natCode tag_sb) (ap2 Pair spec2 pa)

      inner1 : Term
      inner1 = ap2 Pair (natCode tag_sb) (ap2 Pair spec1 inner2)

      e_axN7 : Deriv (eqF (ap1 thmT pa) (FormR g cV0 cV1 cV2))
      e_axN7 = thmT_at_axN7 (codeFun2 g)

      innerPass :
        Deriv (eqF (ap2 sbf spec2 (FormR g cV0 cV1 cV2))
                    (FormR g cV0 cV1 tC))
      innerPass =
        onePassR g (suc (suc zero)) tC cV0 cV1 cV2 cV0 cV1 tC
          (sbt_at_var_nomatch (suc (suc zero)) zero tC refl)
          (sbt_at_var_nomatch (suc (suc zero)) (suc zero) tC refl)
          (sbt_at_var_match (suc (suc zero)) tC)

      middlePass :
        Deriv (eqF (ap2 sbf spec1 (FormR g cV0 cV1 tC))
                    (FormR g cV0 tB tC))
      middlePass =
        onePassR g (suc zero) tB cV0 cV1 tC cV0 tB tC
          (sbt_at_var_nomatch (suc zero) zero tB refl)
          (sbt_at_var_match (suc zero) tB)
          (inertC (suc zero) tB)

      outerPass :
        Deriv (eqF (ap2 sbf spec0 (FormR g cV0 tB tC))
                    (FormR g tA tB tC))
      outerPass =
        onePassR g zero tA cV0 tB tC tA tB tC
          (sbt_at_var_match zero tA)
          (inertB zero tA)
          (inertC zero tA)

  in ruleTrans (thmT_at_sb spec0 inner1)
       (ruleTrans (congR sbf spec0 (thmT_at_sb spec1 inner2))
         (ruleTrans (congR sbf spec0 (congR sbf spec1 (thmT_at_sb spec2 pa)))
           (ruleTrans (congR sbf spec0 (congR sbf spec1 (congR sbf spec2 e_axN7)))
             (ruleTrans (congR sbf spec0 (congR sbf spec1 innerPass))
               (ruleTrans (congR sbf spec0 middlePass)
                          outerPass)))))
