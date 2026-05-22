{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Thm12.PartSF1 -- Theorem 12 successor case with Df_s : Fun1.
--
--   Df_s : Fun1
--   Df_s = compose1U Df_refl (compose1U num s)
--
--   thm12_s_F1 : (X : Term) ->
--                Deriv (eqF (ap1 thmT (ap1 Df_s X)) (codeFTeq1 s X))

module BRA4.Thm12.PartSF1 where

open import BRA4.Base
open import BRA4.Num               using ( num )
open import BRA4.ThmT              using ( thmT )
open import BRA4.Thm12.CodeFTeq    using ( codeFTeq1 )
open import BRA4.Thm12.EncodedRefl using ( Df_refl_meta )
open import BRA4.Thm12.EncodedReflF1
  using ( Df_refl ; Df_refl_unfold )
open import BRA4.Thm12.PartS       using ( Df_s_meta ; thm12_s )

------------------------------------------------------------------------
-- Df_s : Fun1.

Df_s : Fun1
Df_s = compose1U Df_refl (compose1U num s)

------------------------------------------------------------------------
-- ap1 Df_s X =Deriv= Df_s_meta X.

Df_s_unfold :
  (X : Term) -> Deriv (eqF (ap1 Df_s X) (Df_s_meta X))
Df_s_unfold X =
  let
    -- ap1 (compose1U num s) X =Deriv= ap1 num (ap1 s X).
    e_inner : Deriv (eqF (ap1 (compose1U num s) X) (ap1 num (ap1 s X)))
    e_inner = axComp num s X

    -- ap1 Df_s X = ap1 Df_refl (ap1 (compose1U num s) X)  via axComp.
    e_outer :
      Deriv (eqF (ap1 Df_s X) (ap1 Df_refl (ap1 (compose1U num s) X)))
    e_outer = axComp Df_refl (compose1U num s) X

    -- Rewrite inner to (num (s X)).
    e_step :
      Deriv (eqF (ap1 Df_refl (ap1 (compose1U num s) X))
                  (ap1 Df_refl (ap1 num (ap1 s X))))
    e_step = cong1 Df_refl e_inner

    -- Unfold Df_refl applied to (num (s X)) :  Df_refl_unfold.
    e_unfold :
      Deriv (eqF (ap1 Df_refl (ap1 num (ap1 s X)))
                  (Df_refl_meta (ap1 num (ap1 s X))))
    e_unfold = Df_refl_unfold (ap1 num (ap1 s X))

    -- Df_refl_meta (num (s X)) is definitionally Df_s_meta X.
  in ruleTrans e_outer (ruleTrans e_step e_unfold)

------------------------------------------------------------------------
-- thm12_s in Fun1 form.

thm12_s_F1 :
  (X : Term) ->
  Deriv (eqF (ap1 thmT (ap1 Df_s X)) (codeFTeq1 s X))
thm12_s_F1 X =
  let e_thmT_unfold :
        Deriv (eqF (ap1 thmT (ap1 Df_s X)) (ap1 thmT (Df_s_meta X)))
      e_thmT_unfold = cong1 thmT (Df_s_unfold X)
  in ruleTrans e_thmT_unfold (thm12_s X)
