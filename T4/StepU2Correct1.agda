{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.StepU2Correct1 -- completeness for operational semantics for
-- Fun1, EXCEPT the R case of Fun2.  Parametric in a  complete2_R
-- handler (provided by T4.StepU2Correct2).
--
-- For each Fun1 f, complete1 f x K produces a  Reaches  record whose
-- fuel is a Term-level expression in  x  (built by meta-recursion on
-- f's tree) and whose runs is a Deriv at SPECIFIC x, K.

module T4.StepU2Correct1 where

open import T4.Base
open import T4.StepU2
open import T4.StepU2Reach

open import BRA3.Church          using ( pi )
open import BRA3.ChurchT117      using ( Fst )
open import BRA3.ChurchT116      using ( Snd )

------------------------------------------------------------------------
-- Halt-style readjustment helper.

cfgRT_val_rw : (val val' K : Term) ->
               Deriv (eqF val val') ->
               Deriv (eqF (cfgRT val K) (cfgRT val' K))
cfgRT_val_rw val val' K e = congR pi (natCode tagRT) (congL pi K e)

------------------------------------------------------------------------
-- Inner module parametric in the Fun2-R completeness handler.

module Inner
  (complete2_R :
     (gFun : Fun1) (h1 h2 : Fun2) (x y K : Term) ->
     Reaches (cfgEV (mcode2 (R gFun h1 h2)) (ap2 pi x y) K)
             (cfgRT (ap2 (R gFun h1 h2) x y) K))
  where

  ------------------------------------------------------------------------
  -- Mutual completeness theorems for Fun1 / Fun2 .

  complete1 : (f : Fun1) (x K : Term) ->
              Reaches (cfgEV (mcode1 f) x K) (cfgRT (ap1 f x) K)
  complete2 : (g : Fun2) (x y K : Term) ->
              Reaches (cfgEV (mcode2 g) (ap2 pi x y) K)
                      (cfgRT (ap2 g x y) K)

  ----------------------------------------------------------------------
  -- Fun1 leaves.

  complete1 s x K =
    reach_step1 (cfgEV (mcode1 s) x K) (cfgRT (ap1 s x) K) (stepU_at_evS x K)

  complete1 o x K =
    let r1 : Reaches (cfgEV (mcode1 o) x K) (cfgRT O K)
        r1 = reach_step1 (cfgEV (mcode1 o) x K) (cfgRT O K) (stepU_at_evO x K)

        rwOx : Deriv (eqF (cfgRT O K) (cfgRT (ap1 o x) K))
        rwOx = cfgRT_val_rw O (ap1 o x) K (ruleSym (ax_o x))
    in reach_eq_target r1 rwOx

  complete1 u x K =
    let r1 : Reaches (cfgEV (mcode1 u) x K) (cfgRT x K)
        r1 = reach_step1 (cfgEV (mcode1 u) x K) (cfgRT x K) (stepU_at_evU x K)

        rwUx : Deriv (eqF (cfgRT x K) (cfgRT (ap1 u x) K))
        rwUx = cfgRT_val_rw x (ap1 u x) K (ruleSym (ax_u x))
    in reach_eq_target r1 rwUx

  ----------------------------------------------------------------------
  -- Fun1 composition  C(g, h1, h2)(x) = g(h1(x), h2(x)) .

  complete1 (C g h1 h2) x K =
    let K1 : Term
        K1 = kons (frmC1 (mcode2 g) (mcode1 h2) x) K

        K2 : Term
        K2 = kons (frmApp2 (mcode2 g) (ap1 h1 x)) K

        step1 : Reaches (cfgEV (mcode1 (C g h1 h2)) x K)
                        (cfgEV (mcode1 h1) x K1)
        step1 = reach_step1 (cfgEV (mcode1 (C g h1 h2)) x K)
                            (cfgEV (mcode1 h1) x K1)
                            (stepU_at_evC g h1 h2 x K)

        rec_h1 : Reaches (cfgEV (mcode1 h1) x K1) (cfgRT (ap1 h1 x) K1)
        rec_h1 = complete1 h1 x K1

        step2 : Reaches (cfgRT (ap1 h1 x) K1) (cfgEV (mcode1 h2) x K2)
        step2 = reach_step1 (cfgRT (ap1 h1 x) K1)
                            (cfgEV (mcode1 h2) x K2)
                            (stepU_at_rtC1 (ap1 h1 x) (mcode2 g) (mcode1 h2) x K)

        rec_h2 : Reaches (cfgEV (mcode1 h2) x K2) (cfgRT (ap1 h2 x) K2)
        rec_h2 = complete1 h2 x K2

        step3 : Reaches (cfgRT (ap1 h2 x) K2)
                        (cfgEV (mcode2 g) (ap2 pi (ap1 h1 x) (ap1 h2 x)) K)
        step3 = reach_step1 (cfgRT (ap1 h2 x) K2)
                            (cfgEV (mcode2 g) (ap2 pi (ap1 h1 x) (ap1 h2 x)) K)
                            (stepU_at_rtApp2 (ap1 h2 x) (mcode2 g) (ap1 h1 x) K)

        rec_g : Reaches (cfgEV (mcode2 g) (ap2 pi (ap1 h1 x) (ap1 h2 x)) K)
                        (cfgRT (ap2 g (ap1 h1 x) (ap1 h2 x)) K)
        rec_g = complete2 g (ap1 h1 x) (ap1 h2 x) K

        chain : Reaches (cfgEV (mcode1 (C g h1 h2)) x K)
                        (cfgRT (ap2 g (ap1 h1 x) (ap1 h2 x)) K)
        chain = reach_trans step1 (reach_trans rec_h1 (reach_trans step2
                (reach_trans rec_h2 (reach_trans step3 rec_g))))

        rwCx : Deriv (eqF (cfgRT (ap2 g (ap1 h1 x) (ap1 h2 x)) K)
                          (cfgRT (ap1 (C g h1 h2) x) K))
        rwCx = cfgRT_val_rw (ap2 g (ap1 h1 x) (ap1 h2 x))
                            (ap1 (C g h1 h2) x) K
                            (ruleSym (ax_C g h1 h2 x))
    in reach_eq_target chain rwCx

  ----------------------------------------------------------------------
  -- Fun2 leaf v.

  complete2 v x y K =
    let r1 : Reaches (cfgEV (mcode2 v) (ap2 pi x y) K)
                     (cfgRT (ap1 Snd (ap2 pi x y)) K)
        r1 = reach_step1 (cfgEV (mcode2 v) (ap2 pi x y) K)
                         (cfgRT (ap1 Snd (ap2 pi x y)) K)
                         (stepU_at_evV (ap2 pi x y) K)

        eSnd : Deriv (eqF (ap1 Snd (ap2 pi x y)) y)
        eSnd = axSnd x y

        eVxy : Deriv (eqF y (ap2 v x y))
        eVxy = ruleSym (ax_v x y)

        rwVal : Deriv (eqF (cfgRT (ap1 Snd (ap2 pi x y)) K) (cfgRT (ap2 v x y) K))
        rwVal = cfgRT_val_rw (ap1 Snd (ap2 pi x y)) (ap2 v x y) K
                             (ruleTrans eSnd eVxy)
    in reach_eq_target r1 rwVal

  ----------------------------------------------------------------------
  -- Fun2 R: delegated to the module parameter.

  complete2 (R gFun h1 h2) x y K = complete2_R gFun h1 h2 x y K
