{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SurpriseGIIDone -- the ONE concrete surprise-Goedel-II headline.
--
--   surpriseGIIDone checkFires dKrestProv con : Deriv (eqF O (ap1 s O))   -- 0 = 1
--
-- Everything generic is built in  T4.BuildC1Gen  ( abstract  consts , <20s ).
-- This file is the SOLE place the concrete  CKMargin  enumerator is normalized
-- under  encode / thmT  ( via  buildC1 ), so it is EXPECTED to be slow ( >20s ) ;
-- compile it in the BACKGROUND.   It carries, as honest STOP-rule hypotheses :
--   * checkFires   = "the diagonal program is a valid code of depth <= Lstar_meta" ;
--   * dKrestProv   = the per-day  picks  Sigma_1 run-data ( T4.BuildC1Gen.KrestProv ) ;
--   * ConOpenInt   = the open-interval consistency antecedent.
--
-- The chain ( clos Steps 1-6, all built ) :
--   dComp --monoShift--> Step2 --imp_encoded_mp(dKrestProv)--> PhiProv
--         --c1FromPhiProv(coverBridge)--> C1 --reflectFalse(checkFires,con)--> imp K_rest falseF
--   and then  surpriseGII  ( the shipped external induction ).

open import T4.Base
open import BRA3.ChurchLeq      using ( leq )
open import T4.KGodel1BridgeDef using ( Lstar )

module T4.SurpriseGIIDone
  (Lstar_meta : Nat)
  (lstarLe    : Deriv (leq (natCode Lstar_meta) Lstar))
  where

open import BRA3.RuleInst2 using ( NatLe )
open import T4.Code        using ( falseF )
open import T4.CheckAlphN  using ( checkAlphN )
open import T4.ProgEnc     using ( enc )

open import T4.SurpriseG2.ConstantsConj    using ( SurpriseConstsConj )
open import T4.SurpriseG2.ConOpenIntDef     using ( ConOpenInt )
open import T4.SurpriseG2.BigConjFormula   using ( BigConjFormula )
open import T4.SurpriseG2.KdefBigConj      using ( KdefBigConj )
open import T4.SurpriseG2.StagePredFormula using ( Picks ; PicksBound )

open import T4.CKMargin Lstar_meta lstarLe using ( M ; Bnat ; Bpos ; predEq )
open import T4.KdefDiagAlph Lstar_meta     using ( gLcodeDefAlph )
open import T4.CoverBridgeAlph Lstar_meta  using ( coverBridgeKdefAlph )

open import T4.SurpriseGII Lstar_meta lstarLe using ( surpriseGII ; KdefClash ; consts )
open import T4.KdefClashReflect Lstar_meta lstarLe using ( reflectFalse )
open import T4.BuildC1Gen Lstar_meta consts using ( C1 ; KrestProv ; buildC1 ; Sg )

------------------------------------------------------------------------
-- The carried residuals.

CheckFires : Set
CheckFires = Deriv (eqF (ap1 (checkAlphN Lstar_meta) (enc gLcodeDefAlph)) (ap1 s O))

DKrestProv : Set
DKrestProv = (r : Nat) (picks : Picks) -> KrestProv r picks

------------------------------------------------------------------------
-- The assembled  kdefClash  ( Steps 1-6 ) and the headline.

module _ (checkFires : CheckFires) (dKrestProv : DKrestProv) where

  myKdefClash : KdefClash
  myKdefClash con r rleN picks bound dComp =
    let c1 : C1 r picks
        c1 = buildC1 r picks dComp
               (coverBridgeKdefAlph M r (predEq Bnat Bpos))
               (dKrestProv r picks)
    in reflectFalse checkFires r picks (Sg.pr1 c1) (Sg.pr2 c1) con

  surpriseGIIDone : ConOpenInt -> Deriv (eqF O (ap1 s O))
  surpriseGIIDone = surpriseGII myKdefClash
