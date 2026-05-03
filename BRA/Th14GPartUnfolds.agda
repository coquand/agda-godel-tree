{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Th14GPartUnfolds
--
-- Pair-of-Comp2 unfold lemmas for the g_part tower in
-- BRA.Thm14Constr5Final .  Mirrors  Th14HUnfolds  for the g_part chain.
--
-- These deliver, parametric in x : Term :
--
--   g_part_inner_unfold :
--     ap1 g_part_inner x
--       = ap2 Pair tagCode_mp
--           (ap2 Pair (ap1 f_part x) (ap1 D_thmT x))
--
--   g_part_unfold :
--     ap1 g_part x
--       = ap2 Pair tagCode_mp
--           (ap2 Pair (ap1 g_part_inner x) (ap1 D_sub_at_ii x))
--
-- ASCII only.  No postulates, no holes.

module BRA.Th14GPartUnfolds where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Sub      using (sub)
open import BRA.StepReduce using (ktRed)
open import BRA.Thm.Tag  using (tagMp)

open import BRA.Thm.ThmT using (thmT)
open import BRA.Thm.TagCodes using (tagCode_mp)

open import BRA.Thm12 using (Thm12_F1_Result ; Thm12_F2_Result)

open import BRA.Thm14Constr5Final using (module Th14Constr5Final)

----------------------------------------------------------------------
-- The Th14GPartUnfolds module proper.

module Th14GPartUnfolds
  (r12_th  : Thm12_F1_Result thmT)
  (r12_sub : Thm12_F2_Result sub)
  where

  open Th14Constr5Final r12_th r12_sub
    using ( f_part ; g_part_inner ; g_part
          ; D_thmT ; D_sub_at_ii )

  --------------------------------------------------------------------
  -- g_part_inner_unfold .

  g_part_inner_unfold : (x : Term) ->
    Deriv (atomic (eqn (ap1 g_part_inner x)
                       (ap2 Pair tagCode_mp
                          (ap2 Pair (ap1 f_part x) (ap1 D_thmT x)))))
  g_part_inner_unfold x =
    let
        mid : Fun1
        mid = Comp2 Pair f_part D_thmT

        mid_step : Deriv (atomic (eqn (ap1 mid x)
                                       (ap2 Pair (ap1 f_part x)
                                                 (ap1 D_thmT x))))
        mid_step = axComp2 Pair f_part D_thmT x

        outer_step : Deriv (atomic (eqn (ap1 g_part_inner x)
                                         (ap2 Pair (ap1 (KT tagCode_mp) x)
                                                   (ap1 mid x))))
        outer_step = axComp2 Pair (KT tagCode_mp) mid x

        kt_tag : Deriv (atomic (eqn (ap1 (KT tagCode_mp) x) tagCode_mp))
        kt_tag = ktRed (natCode tagMp) x

        outer_simp1 : Deriv (atomic (eqn (ap1 g_part_inner x)
                                          (ap2 Pair tagCode_mp (ap1 mid x))))
        outer_simp1 = ruleTrans outer_step (congL Pair (ap1 mid x) kt_tag)
    in
        ruleTrans outer_simp1 (congR Pair tagCode_mp mid_step)

  --------------------------------------------------------------------
  -- g_part_unfold .

  g_part_unfold : (x : Term) ->
    Deriv (atomic (eqn (ap1 g_part x)
                       (ap2 Pair tagCode_mp
                          (ap2 Pair (ap1 g_part_inner x) (ap1 D_sub_at_ii x)))))
  g_part_unfold x =
    let
        mid : Fun1
        mid = Comp2 Pair g_part_inner D_sub_at_ii

        mid_step : Deriv (atomic (eqn (ap1 mid x)
                                       (ap2 Pair (ap1 g_part_inner x)
                                                 (ap1 D_sub_at_ii x))))
        mid_step = axComp2 Pair g_part_inner D_sub_at_ii x

        outer_step : Deriv (atomic (eqn (ap1 g_part x)
                                         (ap2 Pair (ap1 (KT tagCode_mp) x)
                                                   (ap1 mid x))))
        outer_step = axComp2 Pair (KT tagCode_mp) mid x

        kt_tag : Deriv (atomic (eqn (ap1 (KT tagCode_mp) x) tagCode_mp))
        kt_tag = ktRed (natCode tagMp) x

        outer_simp1 : Deriv (atomic (eqn (ap1 g_part x)
                                          (ap2 Pair tagCode_mp (ap1 mid x))))
        outer_simp1 = ruleTrans outer_step (congL Pair (ap1 mid x) kt_tag)
    in
        ruleTrans outer_simp1 (congR Pair tagCode_mp mid_step)
