{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.KdefClashReflect -- Task D of  T4/SURPRISE-GII-FINISH-HANDOFF.md : the
-- ConOpenInt reflection that closes the day- r  clash.
--
-- GIVEN the "T proves day- r incompressibility, under K_rest" fact
--
--   dHit : imp K_rest (eqF (ap1 thmT W) (ap1 KcodeAlph (natCode r)))     -- (C1)
--
-- ( for a CLOSED proof code  W  -- the Sigma_1 / encode output of clos Steps
-- 2-4, the genuine remaining residual ), produce the kdefClash conclusion
--   imp K_rest falseF .
--
-- All Carneiro imp-threading, under  K_rest :  read the subject back
-- ( imp_outKdefAlph_correct ), bridge to the closer's self-referential
-- hypothesis, apply the SHIPPED  cgFalseImpDedAlph , then  ConOpenInt  at
-- cgFunAlph W  +  negToImpFalse  +  compI .

open import T4.Base
open import BRA3.ChurchLeq      using ( leq )
open import T4.KGodel1BridgeDef using ( Lstar )

module T4.KdefClashReflect
  (Lstar_meta : Nat)
  (lstarLe    : Deriv (leq (natCode Lstar_meta) Lstar))
  where

open import T4.Code             using ( codeFalse ; falseF )
open import T4.ThmT             using ( thmT )
open import T4.CheckAlphN       using ( checkAlphN )
open import T4.ProgEnc          using ( enc )
open import T4.Counting         using ( negToImpFalse )

open import T4.KdefAlph Lstar_meta        using ( KcodeAlph )
open import T4.KdefRecogAlph Lstar_meta   using ( outKdefAlph )
open import T4.KdefRecogImpAlph Lstar_meta using ( imp_outKdefAlph_correct )
open import T4.KdefDiagAlph Lstar_meta    using ( gLcodeDefAlph )
open import T4.CgFunAlph Lstar_meta       using ( cgFunAlph )
open import T4.CgFalseImpAlph Lstar_meta  using ( cgFalseImpDedAlph )

open import T4.SurpriseG2.ConstantsConj    using ( SurpriseConstsConj )
open import T4.SurpriseG2.BigConjFormula   using ( BigConjFormula )
open import T4.SurpriseG2.StagePredFormula using ( Picks )
open import T4.SurpriseG2.ConOpenIntDef    using ( ConOpenInt )
open import T4.FrontToKdefAlph Lstar_meta lstarLe using ( consts )

open import T4.Thm12.ImpHelpers using ( impRuleSym ; impCong1 )
open import T4.ImpExtras        using ( imp_eqTrans_imp )
open import BRA3.Contrapositive using ( compI )
open import BRA3.RuleInst2      using ( simSubstT )

------------------------------------------------------------------------
-- The day- r  reflection.   W = a CLOSED proof code ( sub0_W / sub1_W /
-- sim_W = refl in practice ).

-- NO  W -closedness : the closer is taken ABSTRACTLY at the fresh  var 2
-- ( which IS closed at vars 0/1 , witnesses  refl ), then  ruleInst (suc (suc
-- zero)) W  specialises the closed implication to ANY  W  ( open in  var 0  is
-- fine -- the Chaitin-GI STATEMENT is parametric in  W , and  closeW  acts only
-- on  var 2  inside the lemma, never on  W ).   The diagonal at  W  is
-- GW = substT 2 W (cgFunAlph (var 2)) .

v2 : Term
v2 = var (suc (suc zero))

reflectFalse :
  Deriv (eqF (ap1 (checkAlphN Lstar_meta) (enc gLcodeDefAlph)) (ap1 s O)) ->  -- checkFires
  (r : Nat) (picks : Picks) (W : Term) ->
  Deriv (imp (BigConjFormula consts (suc r) picks)
             (eqF (ap1 thmT W) (ap1 KcodeAlph (natCode r)))) ->                -- dHit (C1)
  ConOpenInt ->
  Deriv (imp (BigConjFormula consts (suc r) picks) falseF)
reflectFalse checkFires r picks W dHit con =
  let Krest : Formula
      Krest = BigConjFormula consts (suc r) picks

      GW : Term
      GW = substT (suc (suc zero)) W (cgFunAlph v2)

      -- abstract Chaitin-GI : closed at  var 2 , then  ruleInst 2 W .
      atV2 : Deriv (imp (eqF (ap1 thmT v2) (ap1 KcodeAlph (ap1 outKdefAlph v2)))
                        (eqF (ap1 thmT (cgFunAlph v2)) codeFalse))
      atV2 = cgFalseImpDedAlph checkFires v2 (\ _ -> refl) (\ _ -> refl) (\ _ _ -> refl)

      closerW : Deriv (imp (eqF (ap1 thmT W) (ap1 KcodeAlph (ap1 outKdefAlph W)))
                           (eqF (ap1 thmT GW) codeFalse))
      closerW = ruleInst (suc (suc zero)) W atV2

      -- subject read-back ( under K_rest ).
      dBack : Deriv (imp Krest (eqF (ap1 outKdefAlph W) (natCode r)))
      dBack = imp_outKdefAlph_correct Krest W (natCode r) dHit

      dCong : Deriv (imp Krest (eqF (ap1 KcodeAlph (natCode r))
                                    (ap1 KcodeAlph (ap1 outKdefAlph W))))
      dCong = impCong1 KcodeAlph (natCode r) (ap1 outKdefAlph W) (impRuleSym dBack)

      dCloserHyp : Deriv (imp Krest (eqF (ap1 thmT W)
                                         (ap1 KcodeAlph (ap1 outKdefAlph W))))
      dCloserHyp = imp_eqTrans_imp dHit dCong

      dToFalseCode : Deriv (imp Krest (eqF (ap1 thmT GW) codeFalse))
      dToFalseCode = compI dCloserHyp closerW

      conInst : Deriv (neg (eqF (ap1 thmT GW) codeFalse))
      conInst = ruleInst zero GW con

      conImp : Deriv (imp (eqF (ap1 thmT GW) codeFalse) falseF)
      conImp = negToImpFalse (eqF (ap1 thmT GW) codeFalse) conInst
  in compI dToFalseCode conImp
