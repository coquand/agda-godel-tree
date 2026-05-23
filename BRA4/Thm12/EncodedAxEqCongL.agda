{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Thm12.EncodedAxEqCongL -- encoded  ax_eqCongL  instance via THREE
-- NESTED single-variable sb-wraps on axN6  (no sbt3/sbf3).
--
-- Goal (universal in g : Fun2, tA tB tC : Term ; tB tC inert) :
--
--   Df_axEqCongL : Fun2 -> Term -> Term -> Term -> Term
--   encodedAxEqCongL :
--     (g : Fun2) (tA tB tC : Term) (inertB : InertU tB) (inertC : InertU tC) ->
--     Deriv (eqF (ap1 thmT (Df_axEqCongL g tA tB tC))
--                 (encodedAxEqCongL_Term g tA tB tC))
--
-- where  encodedAxEqCongL_Term g tA tB tC  encodes
--   "(tA = tB) > (g(tA, tC) = g(tB, tC))" .
--
-- Construction (var 0 := tA outermost, var 1 := tB, var 2 := tC innermost):
--
--   Df_axEqCongL g tA tB tC =
--     Pair tag_sb (Pair (Pair (natCode 0) tA)
--       (Pair tag_sb (Pair (Pair (natCode 1) tB)
--         (Pair tag_sb (Pair (Pair (natCode 2) tC) (packAx 6 (codeFun2 g)))))))
--
-- thmT walks the wrap with  thmT_at_sb  three times :
--   thmT (Df) = sbf spec0 (sbf spec1 (sbf spec2 (FormL g cV0 cV1 cV2)))
--             = sbf spec0 (sbf spec1 (FormL g cV0 cV1 tC))   [inner  pass, var 2]
--             = sbf spec0 (FormL g cV0 tB tC)                [middle pass, var 1]
--             = FormL g tA tB tC                             [outer  pass, var 0]
-- where  FormL g x0 x1 x2 = imp (eq x0 x1) (eq (g x0 x2) (g x1 x2)) .
--
-- Inner plants tC; middle plants tB and re-scans tC (inertC); outer
-- plants tA and re-scans tB, tC (inertB, inertC).

module BRA4.Thm12.EncodedAxEqCongL where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code              using ( codeFun2 )
open import BRA4.SbT               using ( sbt )
open import BRA4.SbtAtVar          using ( sbt_at_var_match ; sbt_at_var_nomatch )
open import BRA4.SbF               using ( sbf )
open import BRA4.SbStep
open import BRA4.ThmT              using ( thmT )
open import BRA4.ThmTAtSb          using ( thmT_at_sb )
open import BRA4.ThmTAtAx6         using ( thmT_at_axN6 )

------------------------------------------------------------------------
-- Constants and helpers.

private
  N6 : Nat
  N6 = suc (suc (suc (suc (suc (suc zero)))))

  cV0 : Term
  cV0 = ap2 Pair (natCode tag_var) (natCode zero)

  cV1 : Term
  cV1 = ap2 Pair (natCode tag_var) (natCode (suc zero))

  cV2 : Term
  cV2 = ap2 Pair (natCode tag_var) (natCode (suc (suc zero)))

  -- code(ap2 g a b).
  cAp2g : Fun2 -> Term -> Term -> Term
  cAp2g g a b = ap2 Pair (natCode tag_ap2) (ap2 Pair (codeFun2 g) (ap2 Pair a b))

  -- The encoded skeleton  "(x0 = x1) > (g(x0,x2) = g(x1,x2))" .
  FormL : Fun2 -> Term -> Term -> Term -> Term
  FormL g x0 x1 x2 =
    ap2 Pair (natCode tag_imp)
      (ap2 Pair (ap2 Pair (natCode tag_eq) (ap2 Pair x0 x1))
                (ap2 Pair (natCode tag_eq)
                  (ap2 Pair (cAp2g g x0 x2) (cAp2g g x1 x2))))

  packAx6_codeF2 : Fun2 -> Term
  packAx6_codeF2 g =
    ap2 Pair (natCode tag_ax)
      (ap2 Pair (natCode N6) (codeFun2 g))

  spec0_at : Term -> Term
  spec0_at A = ap2 Pair (natCode zero) A

  spec1_at : Term -> Term
  spec1_at B = ap2 Pair (natCode (suc zero)) B

  spec2_at : Term -> Term
  spec2_at cc = ap2 Pair (natCode (suc (suc zero))) cc

------------------------------------------------------------------------
-- Df_axEqCongL  (nested sb-wrap).

Df_axEqCongL : Fun2 -> Term -> Term -> Term -> Term
Df_axEqCongL g tA tB tC =
  ap2 Pair (natCode tag_sb)
    (ap2 Pair (spec0_at tA)
      (ap2 Pair (natCode tag_sb)
        (ap2 Pair (spec1_at tB)
          (ap2 Pair (natCode tag_sb)
            (ap2 Pair (spec2_at tC) (packAx6_codeF2 g))))))

------------------------------------------------------------------------
-- Target encoded formula.

encodedAxEqCongL_Term : Fun2 -> Term -> Term -> Term -> Term
encodedAxEqCongL_Term g tA tB tC = FormL g tA tB tC

------------------------------------------------------------------------
-- One pass of  sbf  over the FormL skeleton.

private
  onePassL :
    (g : Fun2) (k : Nat) (S : Term) (x0 x1 x2 x0' x1' x2' : Term) ->
    Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S) x0) x0') ->
    Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S) x1) x1') ->
    Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S) x2) x2') ->
    Deriv (eqF (ap2 sbf (ap2 Pair (natCode k) S) (FormL g x0 x1 x2))
                (FormL g x0' x1' x2'))
  onePassL g k S x0 x1 x2 x0' x1' x2' e0 e1 e2 =
    sbf_step_imp k S
      (ap2 Pair (natCode tag_eq) (ap2 Pair x0 x1))
      (ap2 Pair (natCode tag_eq) (ap2 Pair (cAp2g g x0 x2) (cAp2g g x1 x2)))
      (ap2 Pair (natCode tag_eq) (ap2 Pair x0' x1'))
      (ap2 Pair (natCode tag_eq) (ap2 Pair (cAp2g g x0' x2') (cAp2g g x1' x2')))
      (sbf_step_atomic k S x0 x1 x0' x1' e0 e1)
      (sbf_step_atomic k S
        (cAp2g g x0 x2) (cAp2g g x1 x2) (cAp2g g x0' x2') (cAp2g g x1' x2')
        (sbt_step_ap2 k S g x0 x2 x0' x2' e0 e2)
        (sbt_step_ap2 k S g x1 x2 x1' x2' e1 e2))

------------------------------------------------------------------------
-- Main theorem.

encodedAxEqCongL :
  (g : Fun2) (tA tB tC : Term) (inertB : InertU tB) (inertC : InertU tC) ->
  Deriv (eqF (ap1 thmT (Df_axEqCongL g tA tB tC))
              (encodedAxEqCongL_Term g tA tB tC))
encodedAxEqCongL g tA tB tC inertB inertC =
  let spec0 : Term
      spec0 = spec0_at tA
      spec1 : Term
      spec1 = spec1_at tB
      spec2 : Term
      spec2 = spec2_at tC

      pa : Term
      pa = packAx6_codeF2 g

      inner2 : Term
      inner2 = ap2 Pair (natCode tag_sb) (ap2 Pair spec2 pa)

      inner1 : Term
      inner1 = ap2 Pair (natCode tag_sb) (ap2 Pair spec1 inner2)

      e_axN6 : Deriv (eqF (ap1 thmT pa) (FormL g cV0 cV1 cV2))
      e_axN6 = thmT_at_axN6 (codeFun2 g)

      -- inner pass (var 2 := tC).
      innerPass :
        Deriv (eqF (ap2 sbf spec2 (FormL g cV0 cV1 cV2))
                    (FormL g cV0 cV1 tC))
      innerPass =
        onePassL g (suc (suc zero)) tC cV0 cV1 cV2 cV0 cV1 tC
          (sbt_at_var_nomatch (suc (suc zero)) zero tC refl)
          (sbt_at_var_nomatch (suc (suc zero)) (suc zero) tC refl)
          (sbt_at_var_match (suc (suc zero)) tC)

      -- middle pass (var 1 := tB).
      middlePass :
        Deriv (eqF (ap2 sbf spec1 (FormL g cV0 cV1 tC))
                    (FormL g cV0 tB tC))
      middlePass =
        onePassL g (suc zero) tB cV0 cV1 tC cV0 tB tC
          (sbt_at_var_nomatch (suc zero) zero tB refl)
          (sbt_at_var_match (suc zero) tB)
          (inertC (suc zero) tB)

      -- outer pass (var 0 := tA).
      outerPass :
        Deriv (eqF (ap2 sbf spec0 (FormL g cV0 tB tC))
                    (FormL g tA tB tC))
      outerPass =
        onePassL g zero tA cV0 tB tC tA tB tC
          (sbt_at_var_match zero tA)
          (inertB zero tA)
          (inertC zero tA)

  in ruleTrans (thmT_at_sb spec0 inner1)
       (ruleTrans (congR sbf spec0 (thmT_at_sb spec1 inner2))
         (ruleTrans (congR sbf spec0 (congR sbf spec1 (thmT_at_sb spec2 pa)))
           (ruleTrans (congR sbf spec0 (congR sbf spec1 (congR sbf spec2 e_axN6)))
             (ruleTrans (congR sbf spec0 (congR sbf spec1 innerPass))
               (ruleTrans (congR sbf spec0 middlePass)
                          outerPass)))))
