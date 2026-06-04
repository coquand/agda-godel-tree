{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SurpriseGIICKConcrete -- the CK-faithful surprise-GII at the CONCRETE
-- CKMargin constants, with  dCB (coverBridge) , ltMN , and the consts/enum
-- plumbing ALL DISCHARGED.   What remains as inputs is EXACTLY :
--   * Kr        : the antecedent characteristic ;
--   * bridgeBwd : imp (Kr x0=O) K_rest   -- the CK identity  <=  direction ;
--   * bridgeFwd : imp K_rest (Kr x0=O)   -- the CK identity  =>  direction ;
--   * checkFires ( pre-existing L*-large-enough fact ) ,  con (= ConOpenInt) .
--
-- So the SOLE remaining mathematics is the CK identity
--   K(x0,p(r+1),..,pN)  <->  (Kr x0 = O) .

open import T4.Base
open import BRA3.ChurchLeq      using ( leq )
open import T4.KGodel1BridgeDef using ( Lstar )

module T4.SurpriseGIICKConcrete
  (Lstar_meta : Nat)
  (lstarLe    : Deriv (leq (natCode Lstar_meta) Lstar))
  where

open import T4.SurpriseG2.ConstantsConj using ( SurpriseConstsConj )
open import T4.SurpriseG2.StagePredFormula using ( Picks )
open import T4.SurpriseG2.ConOpenIntDef using ( ConOpenInt )
open import T4.CheckAlphN using ( checkAlphN )
open import T4.ProgEnc    using ( enc )
open import T4.KdefDiagAlph Lstar_meta    using ( gLcodeDefAlph )
open import T4.CoverBridgeAlph Lstar_meta using ( coverBridgeKdefAlph )

open import T4.CKMargin Lstar_meta lstarLe using ( N ; M ; enum ; ltMN ; Bnat ; Bpos ; predEq )

import T4.StageStepCK
import T4.SurpriseGIICK

consts : SurpriseConstsConj
consts = record { N = N ; M = M ; enum = enum }

------------------------------------------------------------------------
-- Fix the antecedent characteristic  Kr , then discharge everything shipped.

module _ (Kr : Nat -> (Nat -> Nat) -> Fun1) where

  open T4.StageStepCK Lstar_meta consts Kr using ( charAtom ; Krest ; KBCf ; KA )
  open T4.SurpriseGIICK Lstar_meta consts Kr using ( surpriseGIICK )

  -- coverBridge ( "by enum correctness" ), at the concrete enum.
  dCB : (r : Nat) (picks : Picks) -> Deriv (imp (KBCf r) (KA r))
  dCB r picks = coverBridgeKdefAlph M r (predEq Bnat Bpos)

  -- ONLY the CK identity ( both directions ) + checkFires + con remain.
  surpriseGIICKConcrete :
    Deriv (eqF (ap1 (checkAlphN Lstar_meta) (enc gLcodeDefAlph)) (ap1 s O)) ->
    ConOpenInt ->
    (bridgeBwd : (r : Nat) (picks : Picks) -> Deriv (imp (charAtom r picks) (Krest r picks))) ->
    (bridgeFwd : (r : Nat) (picks : Picks) -> Deriv (imp (Krest r picks) (charAtom r picks))) ->
    Deriv (eqF O (ap1 s O))
  surpriseGIICKConcrete checkFires con bridgeBwd bridgeFwd =
    surpriseGIICK ltMN checkFires con bridgeBwd bridgeFwd dCB
