{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Thm12 -- hub for Theorem 12 singulary cases.
--
-- Re-exports :
--
--   codeFTeq1 : Fun1 -> Term -> Term     (BRA4.Thm12.CodeFTeq)
--
--   Df_u   : Fun1
--   thm12_u : (X : Term) ->
--             Deriv (eqF (ap1 thmT (ap1 Df_u X)) (codeFTeq1 u X))
--
--   Df_o   : Fun1
--   thm12_o : (X : Term) ->
--             Deriv (eqF (ap1 thmT (ap1 Df_o X)) (codeFTeq1 o X))
--
--   Df_s_meta : Term -> Term
--   thm12_s : (X : Term) ->
--             Deriv (eqF (ap1 thmT (Df_s_meta X)) (codeFTeq1 s X))
--
--   encoded_refl : (Y : Term) ->
--                  Deriv (eqF (ap1 thmT (Df_refl_meta Y)) (codedReflTerm Y))
--
-- Note : Df_s_meta is a meta-Agda Term -> Term function (not a Fun1).
-- The asymmetric codeFTeq1 design requires Y as a Pair-leaf, which
-- requires baking in z_axRefl_v0 as a constant.  A Fun1 version of Df_s
-- is buildable via a constTermFun1 helper (recursion on z_axRefl_v0's
-- structure) but adds ~200 LoC of mechanical Pair-tree construction
-- and is deferred until downstream code requires it.

module BRA4.Thm12 where

open import BRA4.Thm12.CodeFTeq    public using ( codeFTeq1 )
open import BRA4.Thm12.PartU       public using ( Df_u ; thm12_u )
open import BRA4.Thm12.PartO       public using ( Df_o ; thm12_o )
open import BRA4.Thm12.PartS       public using ( Df_s_meta ; thm12_s )
open import BRA4.Thm12.PartSF1     public using ( Df_s ; thm12_s_F1 )
open import BRA4.Thm12.EncodedRefl public using
  ( Df_refl_meta ; codedReflTerm ; encoded_refl )
open import BRA4.Thm12.EncodedReflF1 public using
  ( Df_refl ; encoded_refl_F1 )
