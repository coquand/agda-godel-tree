{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.StepU2Correct1New -- completeness for operational semantics for
-- Fun1 (Correct1/Correct2 BUNDLES API), EXCEPT the R case of Fun2.
--
-- Each bundle exposes the meta-level Fun1/Fun2 fuel function, so the
-- R-case (BRA4.StepU2CorrectR) can use it directly when constructing
-- paired_R : Fun2.

module BRA4.StepU2Correct1New where

open import BRA4.Base
open import BRA4.StepU2
open import BRA4.StepU2CorrectAPI

open import BRA3.Church          using ( pi ; sigma )
open import BRA3.ChurchT117      using ( Fst )
open import BRA3.ChurchT116      using ( Snd )
open import BRA3.CourseOfValues  using ( iter )
open import BRA3.RecBRA3AtPairUniv using ( iter_base_univ ; iter_step_univ )
open import BRA3.Fan             using ( Lift1 ; Lift1_eq )
open import BRA4.StepU2Reach     using ( sigma_zero ; sigma_succ ; iter_add_T )

------------------------------------------------------------------------
-- Helpers.

-- Building a one-step Deriv whose fuel is  ap1 (constN 1) x .
oneStep_constN1 :
  (c c' x : Term) ->
  Deriv (eqF (ap1 step c) c') ->
  Deriv (eqF (ap2 (iter step) c (ap1 (constN 1) x)) c')
oneStep_constN1 c c' x eStep =
  let fuelEq : Deriv (eqF (ap1 (constN 1) x) (ap1 s O))
      fuelEq = constN_eq 1 x
      e1 = congR (iter step) c fuelEq
      e2 = iter_step_univ step c O
      e3 = cong1 step (iter_base_univ step c)
  in ruleTrans e1 (ruleTrans e2 (ruleTrans e3 eStep))

-- Sum-of-two Fun1: (sumOf2 a b)(x) = sigma(a(x), b(x)) .
sumOf2 : Fun1 -> Fun1 -> Fun1
sumOf2 a b = C sigma a b

sumOf2_eq : (a b : Fun1) (x : Term) ->
            Deriv (eqF (ap1 (sumOf2 a b) x) (ap2 sigma (ap1 a x) (ap1 b x)))
sumOf2_eq a b x = ax_C sigma a b x

-- Result-rewrite helper (cfgRT value position).
cfgRT_val_rw : (val val' K : Term) ->
               Deriv (eqF val val') ->
               Deriv (eqF (cfgRT val K) (cfgRT val' K))
cfgRT_val_rw val val' K e = congR pi (natCode tagRT) (congL pi K e)

-- Iter composition: iter step c (sigma n m) = iter step (iter step c n) m
-- We re-export the universal iter_add_T from StepU2Reach.

------------------------------------------------------------------------
-- Inner module parametric in the Fun2-R completeness bundle.

module Inner
  (correct2_R :
     (gFun : Fun1) (h1 h2 : Fun2) ->
     Correct1 gFun -> Correct2 h1 -> Correct2 h2 ->
     Correct2 (R gFun h1 h2))
  where

  ------------------------------------------------------------------------
  -- Mutual definitions.

  correct1 : (f : Fun1) -> Correct1 f
  correct2 : (g : Fun2) -> Correct2 g

  ----------------------------------------------------------------------
  -- Fun1 leaves.

  correct1 s = mkC1 (constN 1)
    (\ x K -> oneStep_constN1 (cfgEV (mcode1 s) x K) (cfgRT (ap1 s x) K) x
                              (stepU_at_evS x K))

  correct1 o = mkC1 (constN 1)
    (\ x K ->
      let core : Deriv (eqF (ap2 (iter step) (cfgEV (mcode1 o) x K) (ap1 (constN 1) x))
                            (cfgRT O K))
          core = oneStep_constN1 (cfgEV (mcode1 o) x K) (cfgRT O K) x
                                  (stepU_at_evO x K)
          rwOx = cfgRT_val_rw O (ap1 o x) K (ruleSym (ax_o x))
      in ruleTrans core rwOx)

  correct1 u = mkC1 (constN 1)
    (\ x K ->
      let core : Deriv (eqF (ap2 (iter step) (cfgEV (mcode1 u) x K) (ap1 (constN 1) x))
                            (cfgRT x K))
          core = oneStep_constN1 (cfgEV (mcode1 u) x K) (cfgRT x K) x
                                  (stepU_at_evU x K)
          rwUx = cfgRT_val_rw x (ap1 u x) K (ruleSym (ax_u x))
      in ruleTrans core rwUx)

  ----------------------------------------------------------------------
  -- Fun1 composition  C(g, h1, h2).  (Continuation of the correct1
  -- definition; placed BEFORE the correct2 clauses to keep all
  -- correct1 clauses contiguous.)

  correct1 (C g h1 h2) =
    let bH1 : Correct1 h1
        bH1 = correct1 h1
        bH2 : Correct1 h2
        bH2 = correct1 h2
        bG  : Correct2 g
        bG  = correct2 g

        fH1 = fuelF bH1
        fH2 = fuelF bH2
        fG  = fuelG bG

        fuelC : Fun1
        fuelC = sumOf2 (sumOf2 (sumOf2 (sumOf2 (sumOf2 (constN 1) fH1) (constN 1))
                                       fH2) (constN 1))
                       (C fG h1 h2)

        body : (x K : Term) ->
               Deriv (eqF (ap2 (iter step) (cfgEV (mcode1 (C g h1 h2)) x K)
                                            (ap1 fuelC x))
                          (cfgRT (ap1 (C g h1 h2) x) K))
        body x K =
          let
              cInit : Term
              cInit = cfgEV (mcode1 (C g h1 h2)) x K
              K1 : Term
              K1 = kons (frmC1 (mcode2 g) (mcode1 h2) x) K
              cAfterEvC : Term
              cAfterEvC = cfgEV (mcode1 h1) x K1
              cAfterH1 : Term
              cAfterH1 = cfgRT (ap1 h1 x) K1
              K2 : Term
              K2 = kons (frmApp2 (mcode2 g) (ap1 h1 x)) K
              cAfterRtC1 : Term
              cAfterRtC1 = cfgEV (mcode1 h2) x K2
              cAfterH2 : Term
              cAfterH2 = cfgRT (ap1 h2 x) K2
              cAfterRtApp2 : Term
              cAfterRtApp2 = cfgEV (mcode2 g) (ap2 pi (ap1 h1 x) (ap1 h2 x)) K
              cFinal : Term
              cFinal = cfgRT (ap2 g (ap1 h1 x) (ap1 h2 x)) K

              one : Term
              one = ap1 (constN 1) x
              h1Fuel : Term
              h1Fuel = ap1 fH1 x
              h2Fuel : Term
              h2Fuel = ap1 fH2 x
              gFuel : Term
              gFuel = ap2 fG (ap1 h1 x) (ap1 h2 x)

              run1 : Deriv (eqF (ap2 (iter step) cInit one) cAfterEvC)
              run1 = oneStep_constN1 cInit cAfterEvC x (stepU_at_evC g h1 h2 x K)

              run_h1 : Deriv (eqF (ap2 (iter step) cAfterEvC h1Fuel) cAfterH1)
              run_h1 = runs1 bH1 x K1

              run2 : Deriv (eqF (ap2 (iter step) cAfterH1 one) cAfterRtC1)
              run2 = oneStep_constN1 cAfterH1 cAfterRtC1 x
                                     (stepU_at_rtC1 (ap1 h1 x) (mcode2 g) (mcode1 h2) x K)

              run_h2 : Deriv (eqF (ap2 (iter step) cAfterRtC1 h2Fuel) cAfterH2)
              run_h2 = runs1 bH2 x K2

              run3 : Deriv (eqF (ap2 (iter step) cAfterH2 one) cAfterRtApp2)
              run3 = oneStep_constN1 cAfterH2 cAfterRtApp2 x
                                     (stepU_at_rtApp2 (ap1 h2 x) (mcode2 g) (ap1 h1 x) K)

              run_g : Deriv (eqF (ap2 (iter step) cAfterRtApp2 gFuel) cFinal)
              run_g = runs2 bG (ap1 h1 x) (ap1 h2 x) K

              fuel01 : Term
              fuel01 = ap2 sigma one h1Fuel
              run01 : Deriv (eqF (ap2 (iter step) cInit fuel01) cAfterH1)
              run01 =
                ruleTrans (iter_add_T cInit one h1Fuel)
                  (ruleTrans (congL (iter step) h1Fuel run1) run_h1)

              fuel012 : Term
              fuel012 = ap2 sigma fuel01 one
              run012 : Deriv (eqF (ap2 (iter step) cInit fuel012) cAfterRtC1)
              run012 =
                ruleTrans (iter_add_T cInit fuel01 one)
                  (ruleTrans (congL (iter step) one run01) run2)

              fuel0123 : Term
              fuel0123 = ap2 sigma fuel012 h2Fuel
              run0123 : Deriv (eqF (ap2 (iter step) cInit fuel0123) cAfterH2)
              run0123 =
                ruleTrans (iter_add_T cInit fuel012 h2Fuel)
                  (ruleTrans (congL (iter step) h2Fuel run012) run_h2)

              fuel01234 : Term
              fuel01234 = ap2 sigma fuel0123 one
              run01234 : Deriv (eqF (ap2 (iter step) cInit fuel01234) cAfterRtApp2)
              run01234 =
                ruleTrans (iter_add_T cInit fuel0123 one)
                  (ruleTrans (congL (iter step) one run0123) run3)

              fuelFull : Term
              fuelFull = ap2 sigma fuel01234 gFuel
              runFull : Deriv (eqF (ap2 (iter step) cInit fuelFull) cFinal)
              runFull =
                ruleTrans (iter_add_T cInit fuel01234 gFuel)
                  (ruleTrans (congL (iter step) gFuel run01234) run_g)

              f4 : Fun1
              f4 = sumOf2 (sumOf2 (sumOf2 (sumOf2 (constN 1) fH1) (constN 1)) fH2) (constN 1)

              f3 : Fun1
              f3 = sumOf2 (sumOf2 (sumOf2 (constN 1) fH1) (constN 1)) fH2

              f2 : Fun1
              f2 = sumOf2 (sumOf2 (constN 1) fH1) (constN 1)

              f1 : Fun1
              f1 = sumOf2 (constN 1) fH1

              eq_f1 : Deriv (eqF (ap1 f1 x) fuel01)
              eq_f1 = sumOf2_eq (constN 1) fH1 x

              eq_f2 : Deriv (eqF (ap1 f2 x) fuel012)
              eq_f2 =
                ruleTrans (sumOf2_eq (sumOf2 (constN 1) fH1) (constN 1) x)
                          (congL sigma one eq_f1)

              eq_f3 : Deriv (eqF (ap1 f3 x) fuel0123)
              eq_f3 =
                ruleTrans (sumOf2_eq (sumOf2 (sumOf2 (constN 1) fH1) (constN 1)) fH2 x)
                          (congL sigma h2Fuel eq_f2)

              eq_f4 : Deriv (eqF (ap1 f4 x) fuel01234)
              eq_f4 =
                ruleTrans (sumOf2_eq f3 (constN 1) x)
                          (congL sigma one eq_f3)

              eq_Cfg : Deriv (eqF (ap1 (C fG h1 h2) x) gFuel)
              eq_Cfg = ax_C fG h1 h2 x

              eq_fuelC : Deriv (eqF (ap1 fuelC x) fuelFull)
              eq_fuelC =
                ruleTrans (sumOf2_eq f4 (C fG h1 h2) x)
                  (ruleTrans (congL sigma (ap1 (C fG h1 h2) x) eq_f4)
                             (congR sigma fuel01234 eq_Cfg))

              chain_fuel : Deriv (eqF (ap2 (iter step) cInit (ap1 fuelC x))
                                       (ap2 (iter step) cInit fuelFull))
              chain_fuel = congR (iter step) cInit eq_fuelC

              rwCx : Deriv (eqF cFinal (cfgRT (ap1 (C g h1 h2) x) K))
              rwCx = cfgRT_val_rw (ap2 g (ap1 h1 x) (ap1 h2 x))
                                  (ap1 (C g h1 h2) x) K
                                  (ruleSym (ax_C g h1 h2 x))

          in ruleTrans chain_fuel (ruleTrans runFull rwCx)
    in mkC1 fuelC body

  ----------------------------------------------------------------------
  -- Fun2 leaf v.   fuelG v = Lift1 (constN 1) ; ap2 (Lift1 (constN 1)) x y
  -- = ap1 (constN 1) x = natCode 1 = ap1 s O .

  correct2 v = mkC2 (Lift1 (constN 1))
    (\ x y K ->
      let fuelEq1 : Deriv (eqF (ap2 (Lift1 (constN 1)) x y) (ap1 (constN 1) x))
          fuelEq1 = Lift1_eq (constN 1) x y
          fuelEq2 : Deriv (eqF (ap1 (constN 1) x) (ap1 s O))
          fuelEq2 = constN_eq 1 x
          fuelEq  : Deriv (eqF (ap2 (Lift1 (constN 1)) x y) (ap1 s O))
          fuelEq  = ruleTrans fuelEq1 fuelEq2

          c : Term
          c = cfgEV (mcode2 v) (ap2 pi x y) K

          rewriteFuel : Deriv (eqF (ap2 (iter step) c (ap2 (Lift1 (constN 1)) x y))
                                    (ap2 (iter step) c (ap1 s O)))
          rewriteFuel = congR (iter step) c fuelEq

          e2 = iter_step_univ step c O
          e3 = cong1 step (iter_base_univ step c)

          stepEq : Deriv (eqF (ap1 step c) (cfgRT (ap1 Snd (ap2 pi x y)) K))
          stepEq = stepU_at_evV (ap2 pi x y) K

          chain : Deriv (eqF (ap2 (iter step) c (ap2 (Lift1 (constN 1)) x y))
                              (cfgRT (ap1 Snd (ap2 pi x y)) K))
          chain = ruleTrans rewriteFuel (ruleTrans e2 (ruleTrans e3 stepEq))

          eSnd = axSnd x y
          eVxy = ruleSym (ax_v x y)
          rwVal = cfgRT_val_rw (ap1 Snd (ap2 pi x y)) (ap2 v x y) K
                               (ruleTrans eSnd eVxy)
      in ruleTrans chain rwVal)

  ----------------------------------------------------------------------
  -- Fun2 R: delegated to module parameter, threading the sub-bundles.

  correct2 (R gFun h1 h2) =
    correct2_R gFun h1 h2 (correct1 gFun) (correct2 h1) (correct2 h2)

------------------------------------------------------------------------
-- Section -- Close Inner with the PeterRec-based R-case bundle from
-- BRA4.StepU2CorrectRPeter.  This yields the FULL Layer-1 Correct1/
-- Correct2 closed forms for every Fun1/Fun2 (no remaining open
-- parameters).

open import BRA4.StepU2CorrectRPeter using ( module Construct )

correct2_R-closed :
  (gFun : Fun1) (h1 h2 : Fun2) ->
  Correct1 gFun -> Correct2 h1 -> Correct2 h2 ->
  Correct2 (R gFun h1 h2)
correct2_R-closed gFun h1 h2 bG bH1 bH2 =
  Construct.correct2_R gFun h1 h2 bG bH1 bH2

open Inner correct2_R-closed public
  using ( correct1 ; correct2 )
