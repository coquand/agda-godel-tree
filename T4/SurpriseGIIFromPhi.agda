{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SurpriseGIIFromPhi -- the surprise-Goedel-II headline reduced to the
-- SHARPEST residual : the per-day Sigma_1 lift  phiLift  ( = clos Steps 2-4,
-- "encode the  K_rest => KdefBigConjF  proof, substitute  x0 |-> num x0  in
-- its code, and  mp  against the  picks  run-data" ).   EVERYTHING else is built :
--
--   surpriseGIIFromPhi checkFires phiLift con : Deriv (eqF O (ap1 s O))      -- 0 = 1
--
-- Critical-path pieces ( all BUILT + verified ) :
--   * monoShift            ( clos "by monotonicity of run" :  P(x0)=>Q(x0) |- P(x0)=>Q(x1) ) ;
--   * phiLift  ( RESIDUAL ) ( clos Steps 2-4 :  encode + x0|->num x0 + mp picks-Sigma_1 ) ;
--   * c1FromPhiProv        ( clos Step 5, "by enum correctness" : internalised  coverBridge ) ;
--   * reflectFalse         ( clos Step 6 :  Chaitin closer  cgFalseImpDedAlph  +  ConOpenInt ) ;
--   * surpriseGII          ( the shipped external induction StageInd/StageStepF/DayClash ).
--
-- So the ONLY remaining mathematics is  phiLift  ( the per-day Sigma_1 provability of
-- K_rest , built on the honest  picks  run-data ).

open import T4.Base
open import BRA3.ChurchLeq      using ( leq )
open import T4.KGodel1BridgeDef using ( Lstar )

module T4.SurpriseGIIFromPhi
  (Lstar_meta : Nat)
  (lstarLe    : Deriv (leq (natCode Lstar_meta) Lstar))
  where

open import BRA3.RuleInst2          using ( NatLe )
open import T4.Code               using ( falseF )

open import T4.SurpriseG2.ConOpenIntDef    using ( ConOpenInt )
open import T4.SurpriseG2.BigConjFormula   using ( BigConjFormula )
open import T4.SurpriseG2.KdefBigConj      using ( KdefBigConj )
open import T4.SurpriseG2.StagePredFormula using ( Picks ; PicksBound )
open import T4.KdefBigConjFuelBridge       using ( KdefBigConjF )

open import T4.MonoShift                   using ( monoShift )
open import T4.FrontToKdefAlph Lstar_meta lstarLe using ( consts )
open import T4.KdefClashAssembly Lstar_meta lstarLe using ( C1 ; CheckFires ; N ; M ; enum )
open import T4.BuildC1 Lstar_meta lstarLe  using ( PhiProv ; c1FromPhiProv )
open import T4.KdefClashReflect Lstar_meta lstarLe using ( reflectFalse )
open import T4.SurpriseGII Lstar_meta lstarLe using ( surpriseGII )

------------------------------------------------------------------------
-- The residual :  encode + Sigma_1-lift of one day's  K_rest => KdefBigConjF .

PhiLift : Set
PhiLift =
  (r : Nat) (picks : Picks) ->
  Deriv (imp (BigConjFormula consts (suc r) picks)
             (KdefBigConjF enum (var (suc zero)) M (natCode r))) ->
  PhiProv r picks

------------------------------------------------------------------------
-- The assembled  kdefClash  ( monoShift on the critical path ).

kdefClash :
  CheckFires -> PhiLift ->
  ConOpenInt ->
  (r : Nat) -> NatLe r N ->
  (picks : Picks) -> PicksBound consts picks ->
  Deriv (imp (BigConjFormula consts (suc r) picks) (KdefBigConj M enum (natCode r))) ->
  Deriv (imp (BigConjFormula consts (suc r) picks) falseF)
kdefClash checkFires phiLift con r rleN picks bound dComp =
  let dPhi : Deriv (imp (BigConjFormula consts (suc r) picks)
                        (KdefBigConjF enum (var (suc zero)) M (natCode r)))
      dPhi = monoShift consts r picks dComp
      pp : PhiProv r picks
      pp = phiLift r picks dPhi
      c1 : C1 r picks
      c1 = c1FromPhiProv r picks pp
  in reflectFalse checkFires r picks
       (C1.W c1) (C1.cl0 c1) (C1.cl1 c1) (C1.clsim c1) (C1.hit c1) con

------------------------------------------------------------------------
-- The headline.

surpriseGIIFromPhi :
  CheckFires -> PhiLift -> ConOpenInt -> Deriv (eqF O (ap1 s O))
surpriseGIIFromPhi checkFires phiLift =
  surpriseGII (kdefClash checkFires phiLift)
