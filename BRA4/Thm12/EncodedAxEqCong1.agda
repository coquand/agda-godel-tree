{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Thm12.EncodedAxEqCong1 -- encoded  ax_eqCong1  instance via a
-- NESTED single-variable sb-wrap on axN5  (no sbt2/sbf2).
--
-- Goal (universal in f : Fun1, A B : Term ; B inert) :
--
--   Df_axEqCong1 : Fun1 -> Term -> Term -> Term
--   encodedAxEqCong1 :
--     (f : Fun1) (A B : Term) (inertB : InertU B) ->
--     Deriv (eqF (ap1 thmT (Df_axEqCong1 f A B))
--                 (encodedAxEqCong1_Term f A B))
--
-- where  encodedAxEqCong1_Term f A B  is the encoded form of
--   "(A = B) > (f A = f B)" .
--
-- Construction (replaces the old  tag_sb2  wrap with two nested  tag_sb
-- wraps -- var 0 := A outermost, var 1 := B innermost) :
--
--   Df_axEqCong1 f A B =
--     Pair tag_sb (Pair (Pair (natCode 0) A)
--       (Pair tag_sb (Pair (Pair (natCode 1) B) (packAx 5 (codeFun1 f)))))
--
-- thmT walks the nested wrap with  thmT_at_sb  twice :
--   thmT (Df_axEqCong1 f A B)
--     = sbf spec0 (sbf spec1 (thmT (packAx 5 (codeFun1 f))))   [thmT_at_sb x2]
--     = sbf spec0 (sbf spec1 (FormCong1 f cV0 cV1))            [thmT_at_axN5]
--     = sbf spec0 (FormCong1 f cV0 B)                          [inner pass]
--     = FormCong1 f A B = encodedAxEqCong1_Term f A B          [outer pass]
--
-- The inner pass plants B at the var-1 leaf; the outer pass re-scans it,
-- discharged by  inertB  (B is num-based at every call site).

module BRA4.Thm12.EncodedAxEqCong1 where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code              using ( codeFun1 )
open import BRA4.SbT               using ( sbt )
open import BRA4.SbtAtVar          using ( sbt_at_var_match ; sbt_at_var_nomatch )
open import BRA4.SbF               using ( sbf )
open import BRA4.SbStep
open import BRA4.ThmT              using ( thmT )
open import BRA4.ThmTAtSb          using ( thmT_at_sb )
open import BRA4.ThmTAtAx5         using ( thmT_at_axN5 )

------------------------------------------------------------------------
-- Constants and helpers.

private
  N5 : Nat
  N5 = suc (suc (suc (suc (suc zero))))

  cV0 : Term
  cV0 = ap2 Pair (natCode tag_var) (natCode zero)

  cV1 : Term
  cV1 = ap2 Pair (natCode tag_var) (natCode (suc zero))

  -- code(ap1 f t) = Pair tag_ap1 (Pair (codeFun1 f) t).
  cAp1f : Fun1 -> Term -> Term
  cAp1f f t = ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 f) t)

  -- The encoded skeleton  "(x0 = x1) > (f x0 = f x1)" .
  FormCong1 : Fun1 -> Term -> Term -> Term
  FormCong1 f x0 x1 =
    ap2 Pair (natCode tag_imp)
      (ap2 Pair (ap2 Pair (natCode tag_eq) (ap2 Pair x0 x1))
                (ap2 Pair (natCode tag_eq)
                  (ap2 Pair (cAp1f f x0) (cAp1f f x1))))

  -- The packed axiom Term  packAx 5 (codeFun1 f) .
  packAx5_codeF1 : Fun1 -> Term
  packAx5_codeF1 f =
    ap2 Pair (natCode tag_ax)
      (ap2 Pair (natCode N5) (codeFun1 f))

  -- Single-variable substitution spec codes.
  spec0_at : Term -> Term
  spec0_at A = ap2 Pair (natCode zero) A

  spec1_at : Term -> Term
  spec1_at B = ap2 Pair (natCode (suc zero)) B

------------------------------------------------------------------------
-- Df_axEqCong1 : Fun1 -> Term -> Term -> Term  (nested sb-wrap).

Df_axEqCong1 : Fun1 -> Term -> Term -> Term
Df_axEqCong1 f A B =
  ap2 Pair (natCode tag_sb)
    (ap2 Pair (spec0_at A)
      (ap2 Pair (natCode tag_sb)
        (ap2 Pair (spec1_at B) (packAx5_codeF1 f))))

------------------------------------------------------------------------
-- The target encoded formula.

encodedAxEqCong1_Term : Fun1 -> Term -> Term -> Term
encodedAxEqCong1_Term f A B = FormCong1 f A B

------------------------------------------------------------------------
-- One pass of  sbf  over the FormCong1 skeleton (given the per-leaf sbt
-- results  x0 -> x0' , x1 -> x1' ).

private
  onePass1 :
    (f : Fun1) (k : Nat) (S : Term) (x0 x1 x0' x1' : Term) ->
    Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S) x0) x0') ->
    Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S) x1) x1') ->
    Deriv (eqF (ap2 sbf (ap2 Pair (natCode k) S) (FormCong1 f x0 x1))
                (FormCong1 f x0' x1'))
  onePass1 f k S x0 x1 x0' x1' e0 e1 =
    sbf_step_imp k S
      (ap2 Pair (natCode tag_eq) (ap2 Pair x0 x1))
      (ap2 Pair (natCode tag_eq) (ap2 Pair (cAp1f f x0) (cAp1f f x1)))
      (ap2 Pair (natCode tag_eq) (ap2 Pair x0' x1'))
      (ap2 Pair (natCode tag_eq) (ap2 Pair (cAp1f f x0') (cAp1f f x1')))
      (sbf_step_atomic k S x0 x1 x0' x1' e0 e1)
      (sbf_step_atomic k S
        (cAp1f f x0) (cAp1f f x1) (cAp1f f x0') (cAp1f f x1')
        (sbt_step_ap1 k S f x0 x0' e0)
        (sbt_step_ap1 k S f x1 x1' e1))

------------------------------------------------------------------------
-- Main theorem.

encodedAxEqCong1 :
  (f : Fun1) (A B : Term) (inertB : InertU B) ->
  Deriv (eqF (ap1 thmT (Df_axEqCong1 f A B))
              (encodedAxEqCong1_Term f A B))
encodedAxEqCong1 f A B inertB =
  let spec0 : Term
      spec0 = spec0_at A

      spec1 : Term
      spec1 = spec1_at B

      pa : Term
      pa = packAx5_codeF1 f

      innerCode : Term
      innerCode = ap2 Pair (natCode tag_sb) (ap2 Pair spec1 pa)

      -- thmT (Df) = sbf spec0 (thmT innerCode)   [thmT_at_sb].
      e1 : Deriv (eqF (ap1 thmT (Df_axEqCong1 f A B))
                       (ap2 sbf spec0 (ap1 thmT innerCode)))
      e1 = thmT_at_sb spec0 innerCode

      -- thmT innerCode = sbf spec1 (thmT pa)      [thmT_at_sb].
      e2 : Deriv (eqF (ap1 thmT innerCode) (ap2 sbf spec1 (ap1 thmT pa)))
      e2 = thmT_at_sb spec1 pa

      -- thmT pa = FormCong1 f cV0 cV1             [thmT_at_axN5].
      e3 : Deriv (eqF (ap1 thmT pa) (FormCong1 f cV0 cV1))
      e3 = thmT_at_axN5 (codeFun1 f)

      -- inner pass (var 1 := B) :  sbf spec1 (FormCong1 f cV0 cV1) = FormCong1 f cV0 B.
      innerPass :
        Deriv (eqF (ap2 sbf spec1 (FormCong1 f cV0 cV1)) (FormCong1 f cV0 B))
      innerPass =
        onePass1 f (suc zero) B cV0 cV1 cV0 B
          (sbt_at_var_nomatch (suc zero) zero B refl)
          (sbt_at_var_match (suc zero) B)

      -- outer pass (var 0 := A) :  sbf spec0 (FormCong1 f cV0 B) = FormCong1 f A B.
      outerPass :
        Deriv (eqF (ap2 sbf spec0 (FormCong1 f cV0 B)) (FormCong1 f A B))
      outerPass =
        onePass1 f zero A cV0 B A B
          (sbt_at_var_match zero A)
          (inertB zero A)

  in ruleTrans e1
       (ruleTrans (congR sbf spec0 e2)
         (ruleTrans (congR sbf spec0 (congR sbf spec1 e3))
           (ruleTrans (congR sbf spec0 innerPass)
                      outerPass)))
