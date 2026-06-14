{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.DevEval -- STAGE I3 of attempt3 §11, layer 4: the complete-development
-- CK machine ASSEMBLED into an object two-place evaluator
--
--     devEval : Fun2 ,   ap2 devEval e n = Snd (devStepU^n (initDevF e)) ,
--
-- the EvalUEval.evalU analog for  dev .  The initialiser  initDevF  starts
-- the machine developing  e  with the empty continuation
-- ( ap1 initDevF e = cfgEV e konEmpty ); the read-off is just  Snd  (a HALT
-- config  cfgHALT val = Pair (natCode mHALT) val  exposes its developed
-- value directly at  Snd ).  Threading the run-to-HALT of  T4.DevRun
-- ( devReaches ) through this assembly gives the correctness
--
--     devEval_correct : (t : Tm) -> DevEvalsTo (code t) (code (dev t)) ,
--
-- i.e. there is a fuel  N  with  ap2 devEval (code t) (natCode N) = code (dev t) :
-- the OBJECT machine computes the complete development as a genuine BRA  Deriv .
-- (Fuel is carried existentially, exactly as EvalUCorrect.EvalsTo; no object
-- fuel-bound function is needed.)  Modelled on T4.EvalUEval + the EvalsTo tail
-- of T4.EvalUCorrect; no holes, no postulates.

module T4.DevEval where

open import T4.Base
open import T4.DevMachine using ( cfgEV ; cfgHALT ; konEmpty ; body_cfgHALT ; mEV )
open import T4.DevStep    using ( devStepU )
open import T4.DevRun     using ( Reaches ; steps ; runsP ; devReaches )
open import T4.ParReflPres using ( Tm ; code )
open import T4.ParTri      using ( dev )

open import BRA3.CourseOfValues using ( iter )
open import BRA3.PairAlgebra    using ( Post ; axPost )
open import BRA3.Fan            using ( Lift1 ; Lift1_eq )

------------------------------------------------------------------------
-- initDevF : Fun1 -- ap1 initDevF e = cfgEV e konEmpty
--   = Pair (natCode mEV) (Pair e (Pair O O)).

initDevF : Fun1
initDevF = C Pair (constN mEV) (C Pair u (C Pair o o))

initDevF_eq : (e : Term) -> Deriv (eqF (ap1 initDevF e) (cfgEV e konEmpty))
initDevF_eq e =
  let eInner : Deriv (eqF (ap1 (C Pair o o) e) (ap2 Pair O O))
      eInner = ruleTrans (ax_C Pair o o e)
                 (ruleTrans (congL Pair (ap1 o e) (ax_o e)) (congR Pair O (ax_o e)))
      eMid : Deriv (eqF (ap1 (C Pair u (C Pair o o)) e) (ap2 Pair e (ap2 Pair O O)))
      eMid = ruleTrans (ax_C Pair u (C Pair o o) e)
               (ruleTrans (congL Pair (ap1 (C Pair o o) e) (ax_u e)) (congR Pair e eInner))
      e1 = ax_C Pair (constN mEV) (C Pair u (C Pair o o)) e
  in ruleTrans e1
       (ruleTrans (congL Pair (ap1 (C Pair u (C Pair o o)) e) (constN_eq mEV e))
                  (congR Pair (natCode mEV) eMid))

------------------------------------------------------------------------
-- devEval : Fun2 .  Read-off is  Snd  (the HALT value).

devEval : Fun2
devEval = Post Snd (Fan (Lift1 initDevF) v (iter devStepU))

devEval_unfold : (e n : Term) ->
  Deriv (eqF (ap2 devEval e n) (ap1 Snd (ap2 (iter devStepU) (ap1 initDevF e) n)))
devEval_unfold e n =
  let G : Fun2
      G = Fan (Lift1 initDevF) v (iter devStepU)
      e1 : Deriv (eqF (ap2 devEval e n) (ap1 Snd (ap2 G e n)))
      e1 = axPost Snd G e n
      e2 : Deriv (eqF (ap2 G e n)
                      (ap2 (iter devStepU) (ap2 (Lift1 initDevF) e n) (ap2 v e n)))
      e2 = axFan (Lift1 initDevF) v (iter devStepU) e n
      e5 : Deriv (eqF (ap2 (iter devStepU) (ap2 (Lift1 initDevF) e n) (ap2 v e n))
                      (ap2 (iter devStepU) (ap1 initDevF e) n))
      e5 = ruleTrans (congL (iter devStepU) (ap2 v e n) (Lift1_eq initDevF e n))
                     (congR (iter devStepU) (ap1 initDevF e) (ax_v e n))
  in ruleTrans e1 (cong1 Snd (ruleTrans e2 e5))

------------------------------------------------------------------------
-- Correctness: there is a fuel  N  with  devEval (code t) (natCode N) = code (dev t) .

record DevEvalsTo (e out : Term) : Set where
  constructor mkDevEvalsTo
  field
    fuel : Nat
    ev   : Deriv (eqF (ap2 devEval e (natCode fuel)) out)

open DevEvalsTo public

devEval_correct : (t : Tm) -> DevEvalsTo (code t) (code (dev t))
devEval_correct t =
  let r : Reaches (cfgEV (code t) konEmpty) (cfgHALT (code (dev t)))
      r = devReaches t
      N : Nat
      N = steps r
      run : Deriv (eqF (ap2 (iter devStepU) (cfgEV (code t) konEmpty) (natCode N))
                       (cfgHALT (code (dev t))))
      run = runsP r
      u1 : Deriv (eqF (ap2 devEval (code t) (natCode N))
                      (ap1 Snd (ap2 (iter devStepU) (ap1 initDevF (code t)) (natCode N))))
      u1 = devEval_unfold (code t) (natCode N)
      iterEq : Deriv (eqF (ap2 (iter devStepU) (ap1 initDevF (code t)) (natCode N))
                          (ap2 (iter devStepU) (cfgEV (code t) konEmpty) (natCode N)))
      iterEq = congL (iter devStepU) (natCode N) (initDevF_eq (code t))
      chain : Deriv (eqF (ap2 (iter devStepU) (ap1 initDevF (code t)) (natCode N))
                         (cfgHALT (code (dev t))))
      chain = ruleTrans iterEq run
      final : Deriv (eqF (ap2 devEval (code t) (natCode N)) (code (dev t)))
      final = ruleTrans u1 (ruleTrans (cong1 Snd chain) (body_cfgHALT (code (dev t))))
  in mkDevEvalsTo N final
