{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.KdefClashAssembly -- assembles  kdefClash : T4.SurpriseGII.KdefClash  from
-- the SHIPPED day- r  pieces, reducing surprise-GII to the single residual  C1
-- ( clos Steps 2-4 : encode + Sigma_1-lift of  K_rest  + encoded_mp ).
--
--   kdefClash checkFires sigmaLift : <the KdefClash type>
--
-- where
--   * checkFires  = "the diagonal program is a valid code of depth <= Lstar_meta"
--       ( the carried  L*-large-enough  fact, analog of  dLenStarDef ) ;
--   * sigmaLift  takes  frontToKdefAlph 's output  imp K_rest (KdefAlph(natCode r))
--       ( built HERE, IH-free, by  T4.MonoShift + T4.CoverBridgeAlph ) and returns
--       C1 r picks  = a closed proof code  W  with
--         Deriv (imp K_rest (thmT W = KcodeAlph (natCode r))) .
--
-- Then  T4.SurpriseGII.surpriseGII (kdefClash checkFires sigmaLift) con :
--   ConOpenInt -> Deriv (0 = 1) .
--
-- =====================================================================
-- THE C1 RESIDUAL ( the var-0 collision finding ).
-- =====================================================================
--
-- C1 = "under K_rest, T proves KdefAlph(natCode r)" is clos Steps 2-4 :
--   w1 := encode (frontToKdefAlph ...) ,  thmT_complete_rec  gives
--     thmT w1 = codeFormula (imp K_rest (KdefAlph(natCode r))) ;
--   then  imp_encoded_mp  peels  K_rest  against its Sigma_1-provability
--   ( dKrestProv : the  picks  run-data ),  and  KcodeAlph_correct  bridges
--   codeFormula (KdefAlph(natCode r)) = ap1 KcodeAlph (natCode r) .
--
-- The OBSTRUCTION ( why this is carried, not built ) :  the Sigma_1-lift of
-- K_rest  needs its fuel  var 0  num-installed ( clos "replace x0 by num x0" ),
-- but  T4.CoverBridge / T4.InternalCover  introduce the OPEN program of  KdefAlph
-- as the SAME  var 0 .   So  ruleInst 0 (num x0)  on the implication would also
-- freeze the diagonal's program, breaking the closer.   FIX for whoever builds
-- C1 :  re-point  internalCover / coverBridge / KdefAlph 's program variable from
-- var 0  to a fresh  var 2  ( distinct from  K_rest 's fuel  var 0  and the
-- diagonal fuel  var 1 ) ;  then  num-installing  var 0  hits only  K_rest .

open import T4.Base
open import BRA3.ChurchLeq      using ( leq )
open import T4.KGodel1BridgeDef using ( Lstar )

module T4.KdefClashAssembly
  (Lstar_meta : Nat)
  (lstarLe    : Deriv (leq (natCode Lstar_meta) Lstar))
  where

open import BRA3.RuleInst2          using ( NatLe ; simSubstT )
open import T4.Code               using ( falseF )
open import T4.ThmT               using ( thmT )
open import T4.CheckAlphN         using ( checkAlphN )
open import T4.ProgEnc            using ( enc )

open import T4.KdefAlph Lstar_meta      using ( KdefAlph ; KcodeAlph )
open import T4.KdefDiagAlph Lstar_meta  using ( gLcodeDefAlph )

open import T4.SurpriseG2.ConstantsConj    using ( SurpriseConstsConj )
open import T4.SurpriseG2.ConOpenIntDef    using ( ConOpenInt )
open import T4.SurpriseG2.BigConjFormula   using ( BigConjFormula )
open import T4.SurpriseG2.KdefBigConj      using ( KdefBigConj )
open import T4.SurpriseG2.StagePredFormula using ( Picks ; PicksBound )

open import T4.FrontToKdefAlph Lstar_meta lstarLe using ( consts ; frontToKdefAlph )
open import T4.KdefClashReflect Lstar_meta lstarLe using ( reflectFalse )

------------------------------------------------------------------------
-- The constants ( same record as  T4.SurpriseGII.consts ).

N : Nat
N = SurpriseConstsConj.N consts
M : Nat
M = SurpriseConstsConj.M consts
enum : Fun1
enum = SurpriseConstsConj.enum consts

------------------------------------------------------------------------
-- C1 :  the encode + Sigma_1-lift output, per  (r , picks) .

-- NO closedness on  W  ( the abstract Chaitin-GI closer takes any  W ).
record C1 (r : Nat) (picks : Picks) : Set where
  field
    W   : Term
    hit : Deriv (imp (BigConjFormula consts (suc r) picks)
                     (eqF (ap1 thmT W) (ap1 KcodeAlph (natCode r))))

------------------------------------------------------------------------
-- The assembled  kdefClash , parametric in the residuals.

CheckFires : Set
CheckFires = Deriv (eqF (ap1 (checkAlphN Lstar_meta) (enc gLcodeDefAlph)) (ap1 s O))

SigmaLift : Set
SigmaLift =
  (r : Nat) (picks : Picks) ->
  Deriv (imp (BigConjFormula consts (suc r) picks) (KdefAlph (natCode r))) ->
  C1 r picks

kdefClash :
  CheckFires -> SigmaLift ->
  ConOpenInt ->
  (r : Nat) -> NatLe r N ->
  (picks : Picks) -> PicksBound consts picks ->
  Deriv (imp (BigConjFormula consts (suc r) picks) (KdefBigConj M enum (natCode r))) ->
  Deriv (imp (BigConjFormula consts (suc r) picks) falseF)
kdefClash checkFires sigmaLift con r rleN picks bound dComp =
  let dImp : Deriv (imp (BigConjFormula consts (suc r) picks) (KdefAlph (natCode r)))
      dImp = frontToKdefAlph r picks dComp
      c1 : C1 r picks
      c1 = sigmaLift r picks dImp
  in reflectFalse checkFires r picks (C1.W c1) (C1.hit c1) con
