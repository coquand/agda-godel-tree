{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Thm12.EncodedRefl -- universal encoded-reflexivity for arbitrary
-- Term Y , in the ASYMMETRIC form.
--
--   Df_refl_meta : Term -> Term
--   Df_refl_meta Y = encode_sb 0 Y z_axRefl_v0
--
--   encoded_refl :
--     (Y : Term) ->
--     Deriv (eqF (ap1 thmT (Df_refl_meta Y))
--                 (ap2 Pair (natCode tag_eq) (ap2 Pair Y Y)))
--
-- The trick : z_axRefl_v0 is a FIXED Term with
--   thmT z_axRefl_v0 =Deriv= codeFormula (atomic (eqn (var 0) (var 0)))
-- (proved in BRA4.Thm12.EncodedReflVar0 using the fresh-c sb-cascade).
-- Wrapping it with one  encode_sb 0 Y  layer substitutes  Y  for the
-- two  var 0  positions via  sbt_at_var_match  -- a SINGLE sb-wrap, so
-- no sbt-on-arbitrary-Y blocker.

module BRA4.Thm12.EncodedRefl where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code
open import BRA4.SbContract
open import BRA4.SbT               using ( sbt )
open import BRA4.SbF               using ( sbf )
open import BRA4.SbfAtClosures     using ( sbContract )
open import BRA4.ThmT              using ( thmT )
open import BRA4.ThmTAtSb          using ( thmT_at_sb )
open import BRA4.Thm12.EncodedReflVar0
  using ( z_axRefl_v0 ; thmT_eq_z_axRefl_v0 )

open import BRA3.Church            using ( pi )

open SbContract sbContract

------------------------------------------------------------------------
-- Df_refl_meta : Term -> Term.

Df_refl_meta : Term -> Term
Df_refl_meta Y =
  ap2 pi (natCode tag_sb)
    (ap2 pi (ap2 pi (natCode zero) Y) z_axRefl_v0)

------------------------------------------------------------------------
-- Target shape :  Pair tag_eq (Pair Y Y) .

codedReflTerm : Term -> Term
codedReflTerm Y = ap2 Pair (natCode tag_eq) (ap2 Pair Y Y)

------------------------------------------------------------------------
-- The main theorem.

encoded_refl :
  (Y : Term) ->
  Deriv (eqF (ap1 thmT (Df_refl_meta Y)) (codedReflTerm Y))
encoded_refl Y =
  let
    spec : Term
    spec = ap2 Pair (natCode zero) Y

    -- (1) thmT (Df_refl_meta Y) =Deriv= sbf spec (thmT z_axRefl_v0)  via thmT_at_sb.
    e_sb :
      Deriv (eqF (ap1 thmT (Df_refl_meta Y))
                  (ap2 sbf spec (ap1 thmT z_axRefl_v0)))
    e_sb = thmT_at_sb spec z_axRefl_v0

    -- (2) thmT z_axRefl_v0 =Deriv= codeFormula (atomic (eqn (var 0) (var 0))) .
    -- This is  Pair tag_eq (Pair codeV0 codeV0)  with codeV0 = Pair tag_var (natCode 0) .
    e_inner : Deriv (eqF (ap1 thmT z_axRefl_v0)
                          (codeFormula (atomic (eqn (var zero) (var zero)))))
    e_inner = thmT_eq_z_axRefl_v0

    e_lift :
      Deriv (eqF (ap2 sbf spec (ap1 thmT z_axRefl_v0))
                  (ap2 sbf spec (codeFormula (atomic (eqn (var zero) (var zero))))))
    e_lift = congR sbf spec e_inner

    -- (3) sbf spec (codeFormula (eqn v0 v0))
    --        =sbf_at_atomic=  Pair tag_eq (Pair (sbt spec codeV0) (sbt spec codeV0))
    --        =sbt_at_var_match (twice)=  Pair tag_eq (Pair Y Y) .
    codeV0 : Term
    codeV0 = ap2 Pair (natCode tag_var) (natCode zero)

    e_atomic :
      Deriv (eqF (ap2 sbf spec (codeFormula (atomic (eqn (var zero) (var zero)))))
                  (ap2 Pair (natCode tag_eq)
                    (ap2 Pair (ap2 sbt spec codeV0) (ap2 sbt spec codeV0))))
    e_atomic = sbf_at_atomic zero Y codeV0 codeV0

    e_sbt_var : Deriv (eqF (ap2 sbt spec codeV0) Y)
    e_sbt_var = sbt_at_var_match zero Y

    e_reduce_inner :
      Deriv (eqF (ap2 Pair (ap2 sbt spec codeV0) (ap2 sbt spec codeV0))
                  (ap2 Pair Y Y))
    e_reduce_inner =
      ruleTrans (congL Pair (ap2 sbt spec codeV0) e_sbt_var)
                (congR Pair Y e_sbt_var)

    e_reduce :
      Deriv (eqF (ap2 sbf spec (codeFormula (atomic (eqn (var zero) (var zero)))))
                  (codedReflTerm Y))
    e_reduce = ruleTrans e_atomic
                 (congR Pair (natCode tag_eq) e_reduce_inner)

  in ruleTrans e_sb (ruleTrans e_lift e_reduce)
