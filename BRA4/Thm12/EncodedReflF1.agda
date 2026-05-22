{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Thm12.EncodedReflF1 -- Df_refl as a proper Fun1.
--
--   Df_refl : Fun1
--   Df_refl Y = encode_sb 0 Y z_axRefl_v0
--
-- Built via :
--   Df_refl = C Pair (constN tag_sb)
--               (C Pair (C Pair (constN 0) u)
--                       (constTermFun1 z_axRefl_v0))
--
-- The  constTermFun1 z_axRefl_v0  piece is the Fun1 that always returns
-- z_axRefl_v0  (since it's var-free, witnessed by NoVar_z_axRefl_v0).
--
--   encoded_refl_F1 :
--     (Y : Term) ->
--     Deriv (eqF (ap1 thmT (ap1 Df_refl Y)) (codedReflTerm Y))

module BRA4.Thm12.EncodedReflF1 where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.ThmT              using ( thmT )
open import BRA4.Thm12.EncodedReflVar0
  using ( z_axRefl_v0 )
open import BRA4.Thm12.EncodedRefl
  using ( Df_refl_meta ; encoded_refl ; codedReflTerm )
open import BRA4.Thm12.ConstTermFun1
  using ( constTermFun1 ; constTermFun1_eq )
open import BRA4.Thm12.NoVarZ
  using ( NoVar_z_axRefl_v0 )

------------------------------------------------------------------------
-- Df_refl as a Fun1.

Df_refl : Fun1
Df_refl =
  C Pair (constN tag_sb)
    (C Pair (C Pair (constN zero) u) (constTermFun1 z_axRefl_v0))

------------------------------------------------------------------------
-- ap1 Df_refl Y =Deriv= Df_refl_meta Y.

Df_refl_unfold :
  (Y : Term) -> Deriv (eqF (ap1 Df_refl Y) (Df_refl_meta Y))
Df_refl_unfold Y =
  let
    -- inner1 := C Pair (constN zero) u.  ap1 inner1 Y = Pair (natCode 0) Y.
    inner1 : Fun1
    inner1 = C Pair (constN zero) u

    -- inner1's value.
    e_inner1 :
      Deriv (eqF (ap1 inner1 Y) (ap2 Pair (natCode zero) Y))
    e_inner1 =
      let e1 :
            Deriv (eqF (ap1 inner1 Y)
                        (ap2 Pair (ap1 (constN zero) Y) (ap1 u Y)))
          e1 = ax_C Pair (constN zero) u Y
      in ruleTrans e1
           (ruleTrans (congL Pair (ap1 u Y) (constN_eq zero Y))
                      (congR Pair (natCode zero) (ax_u Y)))

    -- constTermFun1 z_axRefl_v0 returns z_axRefl_v0.
    e_constZ :
      Deriv (eqF (ap1 (constTermFun1 z_axRefl_v0) Y) z_axRefl_v0)
    e_constZ = constTermFun1_eq z_axRefl_v0 NoVar_z_axRefl_v0 Y

    -- inner2 := C Pair inner1 (constTermFun1 z_axRefl_v0).
    -- ap1 inner2 Y = Pair (Pair (natCode 0) Y) z_axRefl_v0.
    inner2 : Fun1
    inner2 = C Pair inner1 (constTermFun1 z_axRefl_v0)

    e_inner2 :
      Deriv (eqF (ap1 inner2 Y)
                  (ap2 Pair (ap2 Pair (natCode zero) Y) z_axRefl_v0))
    e_inner2 =
      let e1 :
            Deriv (eqF (ap1 inner2 Y)
                        (ap2 Pair (ap1 inner1 Y)
                                    (ap1 (constTermFun1 z_axRefl_v0) Y)))
          e1 = ax_C Pair inner1 (constTermFun1 z_axRefl_v0) Y
      in ruleTrans e1
           (ruleTrans (congL Pair (ap1 (constTermFun1 z_axRefl_v0) Y) e_inner1)
                      (congR Pair (ap2 Pair (natCode zero) Y) e_constZ))

    -- Df_refl = C Pair (constN tag_sb) inner2.
    e_outer :
      Deriv (eqF (ap1 Df_refl Y)
                  (ap2 Pair (ap1 (constN tag_sb) Y) (ap1 inner2 Y)))
    e_outer = ax_C Pair (constN tag_sb) inner2 Y

  in ruleTrans e_outer
       (ruleTrans (congL Pair (ap1 inner2 Y) (constN_eq tag_sb Y))
                  (congR Pair (natCode tag_sb) e_inner2))

------------------------------------------------------------------------
-- encoded_refl_F1.

encoded_refl_F1 :
  (Y : Term) ->
  Deriv (eqF (ap1 thmT (ap1 Df_refl Y)) (codedReflTerm Y))
encoded_refl_F1 Y =
  let e1 : Deriv (eqF (ap1 thmT (ap1 Df_refl Y)) (ap1 thmT (Df_refl_meta Y)))
      e1 = cong1 thmT (Df_refl_unfold Y)
  in ruleTrans e1 (encoded_refl Y)
