{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Thm12.PartV -- Theorem 12, case  g = v  (second-projection Fun2).
--
-- Goal :
--   thm12_v : (X Y : Term) ->
--     Deriv (eqF (ap1 thmT (Df_v X Y)) (codeFTeq2 v X Y))
--
-- Construction (NESTED single-variable sb-wrap of  packAx 3 O ; no
-- sbt2/sbf2).  Substituents  num X (var 0) , num Y (var 1) :
--
--   Df_v X Y =
--     Pair tag_sb (Pair (Pair (natCode 0) (num X))
--       (Pair tag_sb (Pair (Pair (natCode 1) (num Y)) (packAx 3 O))))
--
-- Then thmT walks the wrap with  thmT_at_sb  twice :
--   thmT (Df_v X Y)  =  sbf spec0 (sbf spec1 (thmT (packAx 3 O)))
--                    =  sbf spec0 (sbf spec1 (FormV cV0 cV1))
--                    =  sbf spec0 (FormV cV0 (num Y))     [inner pass, var 1 := num Y]
--                    =  FormV (num X) (num Y)             [outer pass, var 0 := num X]
-- where  FormV x0 x1 = Pair tag_eq (Pair (encV x0 x1) x1)  and
--  encV A B = Pair tag_ap2 (Pair (codeFun2 v) (Pair A B)) .
--
-- The inner pass plants  num Y ; the outer pass re-scans it, discharged
-- by  sbt_num_inert  (numeral-inertness).  Bridge RHS slot  num Y ->
--  num (v X Y)  via  cong1 num (ruleSym (ax_v X Y)) .

module BRA4.Thm12.PartV where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code              using ( codeFun2 ; codeFormula )
open import BRA4.Num               using ( num )
open import BRA4.SbT               using ( sbt )
open import BRA4.SbtAtVar          using ( sbt_at_var_match ; sbt_at_var_nomatch )
open import BRA4.SbF               using ( sbf )
open import BRA4.SbStep
open import BRA4.NumInert          using ( sbt_num_inert )
open import BRA4.ThmT              using ( thmT )
open import BRA4.ThmTAtSb          using ( thmT_at_sb )
open import BRA4.ThmTAtAx3         using ( thmT_at_axN3 )
open import BRA4.Thm12.CodeFTeq    using ( codeFTeq2 )

------------------------------------------------------------------------
-- Constants and helpers.

private
  N3 : Nat
  N3 = suc (suc (suc zero))

  cV0 : Term
  cV0 = ap2 Pair (natCode tag_var) (natCode zero)

  cV1 : Term
  cV1 = ap2 Pair (natCode tag_var) (natCode (suc zero))

  packAx3_O : Term
  packAx3_O =
    ap2 Pair (natCode tag_ax)
      (ap2 Pair (natCode N3) O)

  spec0_at : Term -> Term
  spec0_at A = ap2 Pair (natCode zero) A

  spec1_at : Term -> Term
  spec1_at B = ap2 Pair (natCode (suc zero)) B

  -- encV A B = code(ap2 v A B).
  encV : Term -> Term -> Term
  encV A B =
    ap2 Pair (natCode tag_ap2) (ap2 Pair (codeFun2 v) (ap2 Pair A B))

  -- The encoded skeleton  "(v x0 x1) = x1" .
  FormV : Term -> Term -> Term
  FormV x0 x1 =
    ap2 Pair (natCode tag_eq) (ap2 Pair (encV x0 x1) x1)

------------------------------------------------------------------------
-- Df_v : Term -> Term -> Term  (nested sb-wrap).

Df_v : Term -> Term -> Term
Df_v X Y =
  ap2 Pair (natCode tag_sb)
    (ap2 Pair (spec0_at (ap1 num X))
      (ap2 Pair (natCode tag_sb)
        (ap2 Pair (spec1_at (ap1 num Y)) packAx3_O)))

------------------------------------------------------------------------
-- One pass of  sbf  over the FormV skeleton.

private
  onePassV :
    (k : Nat) (S : Term) (x0 x1 x0' x1' : Term) ->
    Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S) x0) x0') ->
    Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S) x1) x1') ->
    Deriv (eqF (ap2 sbf (ap2 Pair (natCode k) S) (FormV x0 x1))
                (FormV x0' x1'))
  onePassV k S x0 x1 x0' x1' e0 e1 =
    sbf_step_atomic k S
      (encV x0 x1) x1
      (encV x0' x1') x1'
      (sbt_step_ap2 k S v x0 x1 x0' x1' e0 e1)
      e1

------------------------------------------------------------------------
-- The main theorem.

thm12_v :
  (X Y : Term) ->
  Deriv (eqF (ap1 thmT (Df_v X Y)) (codeFTeq2 v X Y))
thm12_v X Y =
  let
    spec0 : Term
    spec0 = spec0_at (ap1 num X)

    spec1 : Term
    spec1 = spec1_at (ap1 num Y)

    innerCode : Term
    innerCode = ap2 Pair (natCode tag_sb) (ap2 Pair spec1 packAx3_O)

    -- (a)  thmT (Df_v X Y) = sbf spec0 (thmT innerCode)   [thmT_at_sb].
    e1 : Deriv (eqF (ap1 thmT (Df_v X Y))
                     (ap2 sbf spec0 (ap1 thmT innerCode)))
    e1 = thmT_at_sb spec0 innerCode

    -- (b)  thmT innerCode = sbf spec1 (thmT packAx3_O)    [thmT_at_sb].
    e2 : Deriv (eqF (ap1 thmT innerCode)
                     (ap2 sbf spec1 (ap1 thmT packAx3_O)))
    e2 = thmT_at_sb spec1 packAx3_O

    -- (c)  thmT packAx3_O = FormV cV0 cV1                 [thmT_at_axN3].
    e3 : Deriv (eqF (ap1 thmT packAx3_O) (FormV cV0 cV1))
    e3 = thmT_at_axN3 O

    -- (d)  inner pass (var 1 := num Y) :  FormV cV0 cV1 -> FormV cV0 (num Y).
    innerPass :
      Deriv (eqF (ap2 sbf spec1 (FormV cV0 cV1)) (FormV cV0 (ap1 num Y)))
    innerPass =
      onePassV (suc zero) (ap1 num Y) cV0 cV1 cV0 (ap1 num Y)
        (sbt_at_var_nomatch (suc zero) zero (ap1 num Y) refl)
        (sbt_at_var_match (suc zero) (ap1 num Y))

    -- (e)  outer pass (var 0 := num X) :  FormV cV0 (num Y) -> FormV (num X) (num Y).
    outerPass :
      Deriv (eqF (ap2 sbf spec0 (FormV cV0 (ap1 num Y)))
                  (FormV (ap1 num X) (ap1 num Y)))
    outerPass =
      onePassV zero (ap1 num X) cV0 (ap1 num Y) (ap1 num X) (ap1 num Y)
        (sbt_at_var_match zero (ap1 num X))
        (sbt_num_inert zero (ap1 num X) Y)

    e_cascade :
      Deriv (eqF (ap1 thmT (Df_v X Y)) (FormV (ap1 num X) (ap1 num Y)))
    e_cascade =
      ruleTrans e1
        (ruleTrans (congR sbf spec0 e2)
          (ruleTrans (congR sbf spec0 (congR sbf spec1 e3))
            (ruleTrans (congR sbf spec0 innerPass)
                       outerPass)))

    -- (f)  Bridge RHS slot  num Y -> num (v X Y)  via cong1 num (ruleSym (ax_v X Y)).
    axV_eq : Deriv (eqF (ap2 v X Y) Y)
    axV_eq = ax_v X Y

    rhs_bridge :
      Deriv (eqF (ap1 num Y) (ap1 num (ap2 v X Y)))
    rhs_bridge = cong1 num (ruleSym axV_eq)

    e_inner_pair :
      Deriv (eqF
        (ap2 Pair (encV (ap1 num X) (ap1 num Y)) (ap1 num Y))
        (ap2 Pair (encV (ap1 num X) (ap1 num Y)) (ap1 num (ap2 v X Y))))
    e_inner_pair = congR Pair (encV (ap1 num X) (ap1 num Y)) rhs_bridge

    e_outer_pair :
      Deriv (eqF
        (FormV (ap1 num X) (ap1 num Y))
        (ap2 Pair (natCode tag_eq)
          (ap2 Pair (encV (ap1 num X) (ap1 num Y)) (ap1 num (ap2 v X Y)))))
    e_outer_pair = congR Pair (natCode tag_eq) e_inner_pair

    -- The RHS of e_outer_pair is definitionally  codeFTeq2 v X Y .

  in ruleTrans e_cascade e_outer_pair
