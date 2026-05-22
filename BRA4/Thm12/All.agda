{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Thm12.All -- Theorem 12, mutual assembly.
--
-- The recursion structure mirrors  Fun1 / Fun2 :
--
--   thm12      : (f : Fun1) -> Thm12_F1 f
--   thm12_Fun2 : (g : Fun2) -> Thm12_F2 g
--
-- where
--
--   Thm12_F1 f = Sigma Fun1 (\ Df ->
--     (X : Term) -> Deriv (eqF (ap1 thmT (ap1 Df X)) (codeFTeq1 f X)))
--
--   Thm12_F2 g = Sigma Fun2 (\ Df ->
--     (A B : Term) -> Deriv (eqF (ap1 thmT (ap2 Df A B)) (codeFTeq2 g A B)))
--
-- Each clause invokes the per-case shipped lemma (PartSF1.thm12_s_F1,
-- PartO.thm12_o, PartU.thm12_u, PartCF1.thm12_C_F1, PartVF2.thm12_v_F2,
-- PartRStep.thm12_R) ; the recursion just threads the per-case Df / IH
-- pairs through the inductive structure.

module BRA4.Thm12.All where

open import BRA4.Base
open import BRA4.ThmT              using ( thmT )
open import BRA4.Thm12.CodeFTeq    using ( codeFTeq1 ; codeFTeq2 )
open import BRA4.Thm12.PartO       using ( Df_o ; thm12_o )
open import BRA4.Thm12.PartU       using ( Df_u ; thm12_u )
open import BRA4.Thm12.PartSF1     using ( Df_s ; thm12_s_F1 )
open import BRA4.Thm12.PartCF1     using ( Df_C_F1 ; thm12_C_F1 )
open import BRA4.Thm12.PartVF2     using ( Df_v_F2 ; thm12_v_F2 )
open import BRA4.Thm12.PartRStep   using ( Dg ; thm12_R )

------------------------------------------------------------------------
-- Local Sigma (BRA3 / BRA4 do not export a global Sigma).

record Sigma (A : Set) (B : A -> Set) : Set where
  constructor mkSigma
  field
    fst : A
    snd : B fst
open Sigma public

------------------------------------------------------------------------
-- Result types.

Thm12_F1 : Fun1 -> Set
Thm12_F1 f =
  Sigma Fun1 (\ Df ->
    (X : Term) -> Deriv (eqF (ap1 thmT (ap1 Df X)) (codeFTeq1 f X)))

Thm12_F2 : Fun2 -> Set
Thm12_F2 g =
  Sigma Fun2 (\ Df ->
    (A B : Term) -> Deriv (eqF (ap1 thmT (ap2 Df A B)) (codeFTeq2 g A B)))

------------------------------------------------------------------------
-- The mutual recursion.

mutual
  thm12 : (f : Fun1) -> Thm12_F1 f
  thm12 s = mkSigma Df_s thm12_s_F1
  thm12 o = mkSigma Df_o thm12_o
  thm12 u = mkSigma Df_u thm12_u
  thm12 (C g h1 h2) =
    let p_g  = thm12_Fun2 g
        p_h1 = thm12 h1
        p_h2 = thm12 h2

        Df_g_F2  : Fun2
        Df_g_F2  = fst p_g

        Df_h1_F1 : Fun1
        Df_h1_F1 = fst p_h1

        Df_h2_F1 : Fun1
        Df_h2_F1 = fst p_h2

        ih_g  = snd p_g
        ih_h1 = snd p_h1
        ih_h2 = snd p_h2
    in mkSigma (Df_C_F1 g h1 h2 Df_g_F2 Df_h1_F1 Df_h2_F1)
               (\ X -> thm12_C_F1 g h1 h2 Df_g_F2 Df_h1_F1 Df_h2_F1
                                   ih_g ih_h1 ih_h2 X)

  thm12_Fun2 : (g : Fun2) -> Thm12_F2 g
  thm12_Fun2 v = mkSigma Df_v_F2 thm12_v_F2
  thm12_Fun2 (R g h1 h2) =
    let p_g  = thm12 g
        p_h1 = thm12_Fun2 h1
        p_h2 = thm12_Fun2 h2

        Df_g_F1  : Fun1
        Df_g_F1  = fst p_g

        Df_h1_F2 : Fun2
        Df_h1_F2 = fst p_h1

        Df_h2_F2 : Fun2
        Df_h2_F2 = fst p_h2

        ih_g  = snd p_g
        ih_h1 = snd p_h1
        ih_h2 = snd p_h2
    in mkSigma (Dg g h1 h2 Df_g_F1 Df_h1_F2 Df_h2_F2)
               (\ X Y -> thm12_R g h1 h2 Df_g_F1 Df_h1_F2 Df_h2_F2
                                  ih_g ih_h1 ih_h2 X Y)
