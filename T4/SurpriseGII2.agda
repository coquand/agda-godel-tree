{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SurpriseGII2 -- the TWO-FUEL-VARIABLE surprise-Goedel-II headline
-- ( handoff T4/SURPRISE-GII-TWOVAR-HANDOFF.md section 4 , now wired ).
--
-- =====================================================================
-- GOAL.
-- =====================================================================
--
--   surpriseGII2 : Sigma1ClashData -> ConOpenInt -> Deriv (eqF O (ap1 s O))
--
-- Same headline as the single-fuel  T4.SurpriseGII.surpriseGII , but the
-- per-step clash now routes through the TWO-FUEL front end  StepFrontEnd2.frontEnd2
-- ( K_rest @ x0 , phi @ x1 , distinct ) and the verified two-fuel barrier
-- KdefClash2.kdefClash2 .   This DISCHARGES the whole single-fuel  KdefClash
-- hypothesis ( which was UNbuildable -- a single  ruleInst 0 F  pins both
-- fuels ), replacing it with the strictly SMALLER, genuinely-external residual
--
--   Sigma1ClashData :  per ( r , picks )  the two Kritchman-Raz provability
--   facts  dKrest  ( "T proves K_rest[F0,F1]" , Eq. 2 per-day runs ) and
--   dComp  ( "T proves neg Inc[F1]" , the diagonal / enum-identification ) ,
--   plus the two pinned fuels  F0 ( picks halting bound ) and  F1 ( the
--   diagonal's halt time, NoVar ).
--
-- Everything else -- frontEnd2, the encoded mp chain, the substF-distribution,
-- the consistency clash -- is DERIVED ( no holes/postulates ).   The two
-- residual facts are the honest remaining long poles ( per-day run data +
-- enum-identification ), carried hypothesis-first per the repo STOP-rule.

open import T4.Base
open import BRA3.ChurchLeq        using ( leq )
open import T4.KGodel1BridgeDef   using ( Lstar )

module T4.SurpriseGII2
  (Lstar_meta : Nat)
  (lstarLe    : Deriv (leq (natCode Lstar_meta) Lstar))
  where

open import BRA3.RuleInst2          using ( NatLe )
open import T4.Code               using ( codeFormula ; falseF )
open import T4.ThmT               using ( thmT )
open import T4.Thm12.ConstTermFun1 using ( NoVar )
open import T4.SurpriseG2.ConstantsConj    using ( SurpriseConstsConj )
open import T4.SurpriseG2.ConOpenIntDef    using ( ConOpenInt )
open import T4.SurpriseG2.BigConjFormula   using ( BigConjFormula )
open import T4.SurpriseG2.StagePredFormula using ( StagePredF ; Picks ; PicksBound )
open import T4.KdefBigConjFuelBridge       using ( KdefBigConjF )
open import T4.StepFrontEnd2               using ( frontEnd2 )
open import T4.KdefClash2                  using ( kdefClash2 )
import T4.SurpriseG2.StageStepF
open import T4.SurpriseG2.SurpriseG2FinalFormula using ( surpriseG2F )

open import T4.CKMargin Lstar_meta lstarLe
  using ( N ; M ; enum ; ltMN )

------------------------------------------------------------------------
-- The concrete surprise-G2 constants ( N := Bnat , M := Bnat-1 , enum ).

consts : SurpriseConstsConj
consts = record { N = N ; M = M ; enum = enum }

------------------------------------------------------------------------
-- The genuinely-EXTERNAL residual ( the only remaining long poles ) : per
-- ( r , picks ) the two Kritchman-Raz provability facts, at the two pinned
-- fuels  F0 ( K_rest 's bound ) and  F1 ( the diagonal's halt time ).

record ClashInputs (r : Nat) (picks : Picks) : Set where
  field
    F0 F1  : Term
    nvF1   : NoVar F1
    -- dKrest : "T proves K_rest[var0:=F0, var1:=F1]"  ( Eq. 2 per-day runs ).
    wKrest : Term
    dKrest : Deriv (eqF (ap1 thmT wKrest)
                        (codeFormula (substF zero F0 (substF (suc zero) F1
                          (BigConjFormula consts (suc r) picks)))))
    -- dComp : "T proves neg Inc[F1]"  ( diagonal / enum-identification ).
    wComp  : Term
    dComp  : Deriv (eqF (ap1 thmT wComp)
                        (codeFormula (neg (KdefBigConjF enum F1 M (natCode r)))))

Sigma1ClashData : Set
Sigma1ClashData =
  (r : Nat) -> NatLe r N -> (picks : Picks) -> PicksBound consts picks ->
  ClashInputs r picks

------------------------------------------------------------------------
-- The day-r clash, two-fuel : frontEnd2 -> kdefClash2 .

module _ (con : ConOpenInt) (cd : Sigma1ClashData) where

  dayClash2 :
    (r : Nat) -> NatLe r N -> StagePredF consts r ->
    (picks : Picks) -> PicksBound consts picks ->
    Deriv (imp (BigConjFormula consts (suc r) picks) falseF)
  dayClash2 r rleN IH picks bound =
    let ci : ClashInputs r picks
        ci = cd r rleN picks bound
        D : Deriv (imp (BigConjFormula consts (suc r) picks)
                       (KdefBigConjF enum (var (suc zero)) M (natCode r)))
        D = frontEnd2 consts r rleN IH picks bound
    in kdefClash2 enum M r
         (ClashInputs.F0 ci) (ClashInputs.F1 ci) (ClashInputs.nvF1 ci)
         (BigConjFormula consts (suc r) picks) con D
         (ClashInputs.wKrest ci) (ClashInputs.dKrest ci)
         (ClashInputs.wComp ci) (ClashInputs.dComp ci)

------------------------------------------------------------------------
-- The two-fuel headline.

surpriseGII2 : Sigma1ClashData -> ConOpenInt -> Deriv (eqF O (ap1 s O))
surpriseGII2 cd con =
  surpriseG2F consts ltMN
    (T4.SurpriseG2.StageStepF.stageStepF consts (dayClash2 con cd))
