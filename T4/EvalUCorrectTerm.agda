{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.EvalUCorrectTerm -- Term-input lift of evalU_correct (Piece 2A
-- of Goal 2 from T4/PETERREC-NEXT-SESSION-HANDOFF.md).
--
-- The existing  T4.EvalUCorrect.evalU_correct  hard-codes the input
-- as  O  (via  initF e = cfgEV e O konEmpty ).  Here we extend the
-- result to arbitrary Term  x  (Fun1 case) and  x , y  (Fun2 case) by
-- composing the SHIPPED bundles
--
--     T4.StepU2Correct1New.{correct1, correct2}
--
-- with the rtEmpty halt transition and the universal readout lemma.
-- Per-program fuel is Fun1/Fun2-derived (majorising fuel via
-- fuelF/fuelG), not meta-Nat.
--
-- Output theorems (Section 2):
--
--     evalU_correct_at_run1 :
--       (f : Fun1) (x : Term) ->
--       Sigma Term (\ N -> Deriv (eqF
--         (ap1 readout (ap2 (iter step) (cfgEV (mcode1 f) x konEmpty) N))
--         (ap1 s (ap1 f x))))
--
--     evalU_correct_at_run2 :
--       (g : Fun2) (x y : Term) ->
--       Sigma Term (\ N -> Deriv (eqF
--         (ap1 readout (ap2 (iter step)
--                            (cfgEV (mcode2 g) (ap2 pi x y) konEmpty) N))
--         (ap1 s (ap2 g x y))))
--
-- The fuel  N  is a closed-form Term derived from the program: for Fun1,
--   N = ap1 (sumOf2 (fuelF (correct1 f)) (constN 1)) x ,
-- i.e., a Fun1 expression applied to  x  -- this is exactly the
-- majorising-fuel-as-a-Fun1 architecture from T4.StepU2CorrectAPI.
--
-- Section 3 derives the wrapper  evalU_correct_at_via_evalU  routed
-- through the existing  evalU : Fun2 , for downstream uses that prefer
-- the  evalU  interface at  x = O .

module T4.EvalUCorrectTerm where

open import T4.Base
open import T4.StepU2
open import T4.StepU2CorrectAPI
open import T4.StepU2Correct1New
  using ( correct1 ; correct2 ; sumOf2 ; sumOf2_eq ; oneStep_constN1 )
open import T4.StepU2Reach
  using ( iter_add_T )
open import T4.EvalUStep
  using ( stepU_at_rtEmpty )
open import T4.EvalUEval
  using ( readout ; readout_halt ; initF ; initF_eq ; evalU ; evalU_unfold )

open import BRA3.Church          using ( pi ; sigma )
open import BRA3.CourseOfValues  using ( iter )
open import BRA3.Dispatch        using ( constN )

------------------------------------------------------------------------
-- Local Sigma (BRA3 / T4 do not export a global one).

record Sigma (A : Set) (B : A -> Set) : Set where
  constructor mkSigma
  field
    fst : A
    snd : B fst
open Sigma public

------------------------------------------------------------------------
-- Section 1.  Term-input runs to  cfgHALT  (Fun1 and Fun2 inputs).
--
--   runHalt1 f x : the operational chain from  cfgEV (mcode1 f) x konEmpty
--                  to  cfgHALT (ap1 f x) , Term-fuelled by
--                  ap1 (sumOf2 fH (constN 1)) x  where  fH = fuelF (correct1 f) .
--
--   runHalt2 g x y : same shape for Fun2,  with input  (ap2 pi x y) .

runHalt1 : (f : Fun1) (x : Term) ->
  Deriv (eqF (ap2 (iter step) (cfgEV (mcode1 f) x konEmpty)
                  (ap1 (sumOf2 (fuelF (correct1 f)) (constN 1)) x))
             (cfgHALT (ap1 f x)))
runHalt1 f x =
  let bC1 = correct1 f
      fH  = fuelF bC1

      c    : Term
      c    = cfgEV (mcode1 f) x konEmpty
      cRT  : Term
      cRT  = cfgRT (ap1 f x) konEmpty
      cH   : Term
      cH   = cfgHALT (ap1 f x)

      fuelA : Term
      fuelA = ap1 fH x
      fuelB : Term
      fuelB = ap1 (constN 1) x

      run1 : Deriv (eqF (ap2 (iter step) c fuelA) cRT)
      run1 = runs1 bC1 x konEmpty

      run2 : Deriv (eqF (ap2 (iter step) cRT fuelB) cH)
      run2 = oneStep_constN1 cRT cH x (stepU_at_rtEmpty (ap1 f x))

      addFuel : Deriv (eqF (ap2 (iter step) c (ap2 sigma fuelA fuelB))
                            (ap2 (iter step) (ap2 (iter step) c fuelA) fuelB))
      addFuel = iter_add_T c fuelA fuelB

      stepRwrite : Deriv (eqF (ap2 (iter step) (ap2 (iter step) c fuelA) fuelB)
                               (ap2 (iter step) cRT fuelB))
      stepRwrite = congL (iter step) fuelB run1

      chainSigma : Deriv (eqF (ap2 (iter step) c (ap2 sigma fuelA fuelB)) cH)
      chainSigma = ruleTrans addFuel (ruleTrans stepRwrite run2)

      fuelEq : Deriv (eqF (ap1 (sumOf2 fH (constN 1)) x) (ap2 sigma fuelA fuelB))
      fuelEq = sumOf2_eq fH (constN 1) x

      rewriteFuel : Deriv (eqF (ap2 (iter step) c (ap1 (sumOf2 fH (constN 1)) x))
                                (ap2 (iter step) c (ap2 sigma fuelA fuelB)))
      rewriteFuel = congR (iter step) c fuelEq
  in ruleTrans rewriteFuel chainSigma

runHalt2 : (g : Fun2) (x y : Term) ->
  Deriv (eqF (ap2 (iter step) (cfgEV (mcode2 g) (ap2 pi x y) konEmpty)
                  (ap2 sigma (ap2 (fuelG (correct2 g)) x y)
                             (ap1 (constN 1) (ap2 pi x y))))
             (cfgHALT (ap2 g x y)))
runHalt2 g x y =
  let bC2 = correct2 g
      fG  = fuelG bC2

      arg : Term
      arg = ap2 pi x y

      c    : Term
      c    = cfgEV (mcode2 g) arg konEmpty
      cRT  : Term
      cRT  = cfgRT (ap2 g x y) konEmpty
      cH   : Term
      cH   = cfgHALT (ap2 g x y)

      fuelA : Term
      fuelA = ap2 fG x y
      fuelB : Term
      fuelB = ap1 (constN 1) arg

      run1 : Deriv (eqF (ap2 (iter step) c fuelA) cRT)
      run1 = runs2 bC2 x y konEmpty

      run2 : Deriv (eqF (ap2 (iter step) cRT fuelB) cH)
      run2 = oneStep_constN1 cRT cH arg (stepU_at_rtEmpty (ap2 g x y))

      addFuel : Deriv (eqF (ap2 (iter step) c (ap2 sigma fuelA fuelB))
                            (ap2 (iter step) (ap2 (iter step) c fuelA) fuelB))
      addFuel = iter_add_T c fuelA fuelB

      stepRwrite : Deriv (eqF (ap2 (iter step) (ap2 (iter step) c fuelA) fuelB)
                               (ap2 (iter step) cRT fuelB))
      stepRwrite = congL (iter step) fuelB run1
  in ruleTrans addFuel (ruleTrans stepRwrite run2)

------------------------------------------------------------------------
-- Section 2.  Term-input universal-interpreter correctness (the
-- "evalU correct at  x " theorem).
--
-- Composes  runHalt1/2  with  readout_halt .

evalU_correct_at_run1 :
  (f : Fun1) (x : Term) ->
  Sigma Term (\ N ->
    Deriv (eqF (ap1 readout
                 (ap2 (iter step) (cfgEV (mcode1 f) x konEmpty) N))
               (ap1 s (ap1 f x))))
evalU_correct_at_run1 f x =
  let fH = fuelF (correct1 f)
      N : Term
      N = ap1 (sumOf2 fH (constN 1)) x

      runEq : Deriv (eqF (ap2 (iter step) (cfgEV (mcode1 f) x konEmpty) N)
                          (cfgHALT (ap1 f x)))
      runEq = runHalt1 f x

      readoutEq : Deriv (eqF (ap1 readout (ap2 (iter step)
                                                (cfgEV (mcode1 f) x konEmpty) N))
                              (ap1 readout (cfgHALT (ap1 f x))))
      readoutEq = cong1 readout runEq

      haltEq : Deriv (eqF (ap1 readout (cfgHALT (ap1 f x))) (ap1 s (ap1 f x)))
      haltEq = readout_halt (ap1 f x)
  in mkSigma N (ruleTrans readoutEq haltEq)

evalU_correct_at_run2 :
  (g : Fun2) (x y : Term) ->
  Sigma Term (\ N ->
    Deriv (eqF (ap1 readout
                 (ap2 (iter step) (cfgEV (mcode2 g) (ap2 pi x y) konEmpty) N))
               (ap1 s (ap2 g x y))))
evalU_correct_at_run2 g x y =
  let fG = fuelG (correct2 g)
      N : Term
      N = ap2 sigma (ap2 fG x y) (ap1 (constN 1) (ap2 pi x y))

      runEq : Deriv (eqF (ap2 (iter step) (cfgEV (mcode2 g) (ap2 pi x y) konEmpty) N)
                          (cfgHALT (ap2 g x y)))
      runEq = runHalt2 g x y

      readoutEq : Deriv (eqF (ap1 readout (ap2 (iter step)
                                                (cfgEV (mcode2 g) (ap2 pi x y) konEmpty) N))
                              (ap1 readout (cfgHALT (ap2 g x y))))
      readoutEq = cong1 readout runEq

      haltEq : Deriv (eqF (ap1 readout (cfgHALT (ap2 g x y))) (ap1 s (ap2 g x y)))
      haltEq = readout_halt (ap2 g x y)
  in mkSigma N (ruleTrans readoutEq haltEq)

------------------------------------------------------------------------
-- Section 3.  Compatibility wrapper via the existing  evalU : Fun2 .
--
-- The shipped  evalU_unfold  uses  initF  (input hard-coded to  O ),
-- so  ap2 evalU e n = readout (iter stepU (cfgEV e O konEmpty) n) .
-- At  x = O  the Term-input theorem above specialises to a witness
-- of  EvalsTo_term (mcode1 f) (ap1 s (ap1 f O))  routed through  evalU .

record EvalsTo_term (e out : Term) : Set where
  constructor mkEvalsTo_term
  field
    fuel_T : Term
    ev_T   : Deriv (eqF (ap2 evalU e fuel_T) out)

open EvalsTo_term public

evalU_correct_at_via_evalU :
  (f : Fun1) -> EvalsTo_term (mcode1 f) (ap1 s (ap1 f O))
evalU_correct_at_via_evalU f =
  let -- Specialise the Term-input theorem at  x := O .
      sig = evalU_correct_at_run1 f O
      N : Term
      N = fst sig
      runReadout : Deriv (eqF (ap1 readout
                                 (ap2 (iter step) (cfgEV (mcode1 f) O konEmpty) N))
                               (ap1 s (ap1 f O)))
      runReadout = snd sig

      -- Bridge to  evalU  via  initF_eq  and  evalU_unfold .
      u1 : Deriv (eqF (ap2 evalU (mcode1 f) N)
                       (ap1 readout (ap2 (iter step) (ap1 initF (mcode1 f)) N)))
      u1 = evalU_unfold (mcode1 f) N

      iEq : Deriv (eqF (ap1 initF (mcode1 f)) (cfgEV (mcode1 f) O konEmpty))
      iEq = initF_eq (mcode1 f)

      iterEq : Deriv (eqF (ap2 (iter step) (ap1 initF (mcode1 f)) N)
                           (ap2 (iter step) (cfgEV (mcode1 f) O konEmpty) N))
      iterEq = congL (iter step) N iEq

      readoutChain : Deriv (eqF (ap1 readout (ap2 (iter step)
                                                   (ap1 initF (mcode1 f)) N))
                                 (ap1 readout (ap2 (iter step)
                                                    (cfgEV (mcode1 f) O konEmpty) N)))
      readoutChain = cong1 readout iterEq

      final : Deriv (eqF (ap2 evalU (mcode1 f) N) (ap1 s (ap1 f O)))
      final = ruleTrans u1 (ruleTrans readoutChain runReadout)
  in mkEvalsTo_term N final
