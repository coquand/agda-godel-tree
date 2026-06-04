{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.RunMono -- monotonicity of run (the internal-Deriv core), OBJECT-FUEL
-- formulation.  Block 3 of NEXT-SESSION-SURPRISE-GII-PLAN, corrected.
--
-- "Running longer cannot un-halt a halted machine."  The universal machine's
-- HALT configuration is a  stepU -fixpoint ( T4.EvalUStep.stepU_at_halt ), so
-- once the configuration at fuel  L  is  cfgHALT val , the configuration at
-- fuel  s L  is again  cfgHALT val .
--
-- CRUCIAL CORRECTION (vs an earlier  natCode -indexed draft):  the halting step
-- is NOT assumed to be a meta-Nat.  The fuel  L  is an arbitrary OBJECT term --
-- a free variable, an  ap2 maxFun x0 x1 , whatever -- and the single step uses
--  BRA3.RecBRA3AtPairUniv.iter_step_univ  (the no- Closed , universal  iter
-- unfold).  Definability is the OBJECT predicate "the config reaches  cfgHALT x
-- at some object fuel", monotone in the fuel by  runHaltStep ; no meta-Nat
-- halting time, and no  readout -inversion / symbolic-mode reflection is needed
-- (the hypothesis is the config-level  cfgHALT  witness directly).

module T4.RunMono where

open import T4.Base
open import T4.EvalU      using ( cfgHALT )
open import T4.EvalUStep  using ( stepU ; stepU_at_halt )
open import T4.EvalUEval  using ( initF ; readout ; readout_halt ; evalU ; evalU_unfold )
open import T4.Kdef       using ( runProg ; runProg_eq )
open import T4.ProgParse  using ( parse )

open import BRA3.CourseOfValues     using ( iter )
open import BRA3.RecBRA3AtPairUniv  using ( iter_step_univ )
open import T4.Thm12.ImpHelpers   using ( impLift ; impCong1 ; impEqTrans )

------------------------------------------------------------------------
-- SECTION 1.  One more step of (object) fuel preserves the HALT config.
--   No  Closed , no  natCode :  L  is an arbitrary object term.

runHaltStep :
  (c val L : Term) ->
  Deriv (eqF (ap2 (iter stepU) c L) (cfgHALT val)) ->
  Deriv (eqF (ap2 (iter stepU) c (ap1 s L)) (cfgHALT val))
runHaltStep c val L h =
  ruleTrans (iter_step_univ stepU c L)
            (ruleTrans (cong1 stepU h) (stepU_at_halt val))

------------------------------------------------------------------------
-- SECTION 2.  At a HALT config (any object fuel) the read-off is  s val .

runOutputAt :
  (c val L : Term) ->
  Deriv (eqF (ap2 (iter stepU) c L) (cfgHALT val)) ->
  Deriv (eqF (ap1 readout (ap2 (iter stepU) c L)) (ap1 s val))
runOutputAt c val L h =
  ruleTrans (cong1 readout h) (readout_halt val)

------------------------------------------------------------------------
-- SECTION 3.  Monotonicity at the  runProg  level (Kdef's  definable  matrix):
-- from a config-level halt witness at object fuel  L , the program name  p
-- outputs  s val  at fuel  L  (and, by  runHaltStep , at  s L ).

runProgAt :
  (p val L : Term) ->
  Deriv (eqF (ap2 (iter stepU) (ap1 initF (ap1 parse p)) L) (cfgHALT val)) ->
  Deriv (eqF (ap2 runProg p L) (ap1 s val))
runProgAt p val L h =
  let e_rp : Deriv (eqF (ap2 runProg p L) (ap2 evalU (ap1 parse p) L))
      e_rp = runProg_eq p L

      e_ev : Deriv (eqF (ap2 evalU (ap1 parse p) L)
                        (ap1 readout (ap2 (iter stepU) (ap1 initF (ap1 parse p)) L)))
      e_ev = evalU_unfold (ap1 parse p) L

      e_out : Deriv (eqF (ap1 readout (ap2 (iter stepU) (ap1 initF (ap1 parse p)) L))
                         (ap1 s val))
      e_out = runOutputAt (ap1 initF (ap1 parse p)) val L h
  in ruleTrans e_rp (ruleTrans e_ev e_out)

-- The monotone step at the  runProg  level :  output persists at fuel  s L .
runProgStep :
  (p val L : Term) ->
  Deriv (eqF (ap2 (iter stepU) (ap1 initF (ap1 parse p)) L) (cfgHALT val)) ->
  Deriv (eqF (ap2 runProg p (ap1 s L)) (ap1 s val))
runProgStep p val L h =
  runProgAt p val (ap1 s L)
    (runHaltStep (ap1 initF (ap1 parse p)) val L h)

------------------------------------------------------------------------
-- SECTION 4.  Carneiro witness-imp-lifting : the same monotonicity threaded
-- under an ARBITRARY antecedent formula  P  (the halt witness arrives as
--  imp P (... = cfgHALT val) ).  Each  ruleTrans/cong1  becomes
--  impEqTrans/impCong1 , each axiom  impLift .

imp_runHaltStep :
  (P : Formula) (c val L : Term) ->
  Deriv (imp P (eqF (ap2 (iter stepU) c L) (cfgHALT val))) ->
  Deriv (imp P (eqF (ap2 (iter stepU) c (ap1 s L)) (cfgHALT val)))
imp_runHaltStep P c val L h =
  let A : Term
      A = ap2 (iter stepU) c (ap1 s L)

      sC : Term
      sC = ap1 stepU (ap2 (iter stepU) c L)

      e1 : Deriv (imp P (eqF A sC))
      e1 = impLift {P} (iter_step_univ stepU c L)

      e2 : Deriv (imp P (eqF sC (ap1 stepU (cfgHALT val))))
      e2 = impCong1 {P} stepU (ap2 (iter stepU) c L) (cfgHALT val) h

      e3 : Deriv (imp P (eqF (ap1 stepU (cfgHALT val)) (cfgHALT val)))
      e3 = impLift {P} (stepU_at_halt val)
  in impEqTrans {P} A sC (cfgHALT val)
       e1 (impEqTrans {P} sC (ap1 stepU (cfgHALT val)) (cfgHALT val) e2 e3)

imp_runProgAt :
  (P : Formula) (p val L : Term) ->
  Deriv (imp P (eqF (ap2 (iter stepU) (ap1 initF (ap1 parse p)) L) (cfgHALT val))) ->
  Deriv (imp P (eqF (ap2 runProg p L) (ap1 s val)))
imp_runProgAt P p val L h =
  let RP : Term
      RP = ap2 runProg p L

      EV : Term
      EV = ap2 evalU (ap1 parse p) L

      RO : Term
      RO = ap1 readout (ap2 (iter stepU) (ap1 initF (ap1 parse p)) L)

      SV : Term
      SV = ap1 s val

      e_rp : Deriv (imp P (eqF RP EV))
      e_rp = impLift {P} (runProg_eq p L)

      e_ev : Deriv (imp P (eqF EV RO))
      e_ev = impLift {P} (evalU_unfold (ap1 parse p) L)

      e_out : Deriv (imp P (eqF RO SV))
      e_out = impEqTrans {P} RO (ap1 readout (cfgHALT val)) SV
                (impCong1 {P} readout (ap2 (iter stepU) (ap1 initF (ap1 parse p)) L)
                          (cfgHALT val) h)
                (impLift {P} (readout_halt val))
  in impEqTrans {P} RP EV SV e_rp (impEqTrans {P} EV RO SV e_ev e_out)
