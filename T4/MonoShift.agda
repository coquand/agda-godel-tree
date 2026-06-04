{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.MonoShift -- the IH-FREE fuel shift of  clos 's "by monotonicity of run".
--
-- =====================================================================
-- WHAT THIS SHIPS.
-- =====================================================================
--
-- From the day- r  front-end output  ( fuel  var 0 , the form  DayClash 's
-- frontEnd  produces and  kdefClash  receives )
--
--   dComp : imp K_rest (KdefBigConj M enum (natCode r))            -- P(x0) => Q(x0)
--
-- derive, by run-monotonicity ALONE ( no IH, no  StagePredF, no  bound ),
--
--   monoShift dComp : imp K_rest (KdefBigConjF enum (var 1) M (natCode r))   -- P(x0) => Q(x1)
--
-- i.e. the consequent's per-program negations are shifted to the SECOND fuel
--  var 1 , the form  T4.CoverBridgeAlph.coverBridgeKdefAlph  consumes.   This is
-- exactly  clos  Steps "P(x0)=>Q(x0) |- P(x0)=>Q(x1)" : instantiate the
-- assumption at the common fuel  common = x0 + x1 , lift  K_rest  up
-- ( x0 -> common , the picks halting is stable upward ) and push the negated
-- defines down ( common -> x1 , contrapositive of run-monotonicity ).
--
-- ALL of it is Carneiro imp-threading : the per-conjunct step is
--   axContrapos (compI (imp_runProgMonoPlus ...) (prependEqLeft ...)) ;
-- the conjunction is rebuilt with  liftedAndIntro / fstAndImp / sndAndImp ;
-- the three legs ( up, instantiate, down ) compose with  compI .

module T4.MonoShift where

open import T4.Base

open import BRA3.Church          using ( sigma ; T36 )
open import BRA3.RuleInst2       using ( ruleInst2 )
open import BRA3.Contrapositive  using ( identP ; compI ; axContrapos )
open import BRA3.Logic           using ( prependEqLeft )

open import T4.Kdef        using ( runProg )
open import T4.RunProgMono using ( imp_runProgMonoPlus )

open import T4.SurpriseG2.ConstantsConj  using ( SurpriseConstsConj )
open import T4.SurpriseG2.BigConjFormula using ( BigConjFormula ; bigConjCountT ; countDays ; openFuel )
open import T4.SurpriseG2.StagePredFormula using ( Picks )
open import T4.SurpriseG2.KdefBigConj    using ( KdefBigConj )
open import T4.SurpriseG2.AndLemmas      using ( liftedAndIntro ; fstAndImp ; sndAndImp )
open import T4.KdefBigConjFuelBridge     using ( perProgNegF ; KdefBigConjF ; distKBC )
open import T4.StepFrontEnd2             using ( common ; constHalts ; F1 ; bigConjLift ; substBigConj )

------------------------------------------------------------------------
-- SECTION 1.  The per-program contrapositive shift  common -> x1 .

module _ (enum : Fun1) where

  -- runProg p x1 = s subj  =>  runProg p common = s subj   ( monotonicity
  -- x1 -> sigma x1 x0 , commuted to  common = sigma x0 x1 by T36 ).
  perConjShift :
    (subj : Term) (k : Nat) ->
    Deriv (imp (perProgNegF enum common subj k)
               (perProgNegF enum F1 subj k))
  perConjShift subj k =
    let p : Term
        p = ap1 enum (natCode k)
        E_F1 : Formula
        E_F1 = eqF (ap2 runProg p F1) (ap1 s subj)
        E_common : Formula
        E_common = eqF (ap2 runProg p common) (ap1 s subj)

        -- imp E_F1 (runProg p (sigma F1 x0) = s subj)  by run monotonicity.
        mono : Deriv (imp E_F1 (eqF (ap2 runProg p (ap2 sigma F1 (var zero))) (ap1 s subj)))
        mono = imp_runProgMonoPlus E_F1 p subj F1 (var zero) (identP E_F1)

        -- sigma F1 x0 = sigma (var 1)(var 0) = common = sigma (var 0)(var 1)  (T36).
        commEq : Deriv (eqF (ap2 sigma F1 (var zero)) common)
        commEq = ruleInst2 zero (var (suc zero)) (suc zero) (var zero) refl T36

        -- rewrite the fuel slot  sigma F1 x0 -> common  inside the eqF.
        rew : Deriv (imp (eqF (ap2 runProg p (ap2 sigma F1 (var zero))) (ap1 s subj)) E_common)
        rew = prependEqLeft (ap2 runProg p common)
                            (ap2 runProg p (ap2 sigma F1 (var zero)))
                            (ap1 s subj)
                            (congR runProg p (ruleSym commEq))

        impFC : Deriv (imp E_F1 E_common)
        impFC = compI mono rew
    in mp (axContrapos E_F1 E_common) impFC

  ------------------------------------------------------------------------
  -- SECTION 2.  The conjunction shift  KdefBigConjF common -> KdefBigConjF x1 .

  kbcShift :
    (subj : Term) (M : Nat) ->
    Deriv (imp (KdefBigConjF enum common M subj)
               (KdefBigConjF enum F1 M subj))
  kbcShift subj zero      = perConjShift subj zero
  kbcShift subj (suc M')  =
    let hd : Formula
        hd = perProgNegF enum common subj (suc M')
        tl : Formula
        tl = KdefBigConjF enum common M' subj
        X : Formula
        X = KdefBigConjF enum common (suc M') subj    -- = conjF hd tl
    in liftedAndIntro X (perProgNegF enum F1 subj (suc M'))
                        (KdefBigConjF enum F1 M' subj)
         (compI (fstAndImp hd tl) (perConjShift subj (suc M')))
         (compI (sndAndImp hd tl) (kbcShift subj M'))

------------------------------------------------------------------------
-- SECTION 3.  The headline shift  P(x0)=>Q(x0)  |-  P(x0)=>Q(x1) .

monoShift :
  (consts : SurpriseConstsConj) (r : Nat) (picks : Picks) ->
  Deriv (imp (BigConjFormula consts (suc r) picks)
             (KdefBigConj (SurpriseConstsConj.M consts)
                          (SurpriseConstsConj.enum consts) (natCode r))) ->
  Deriv (imp (BigConjFormula consts (suc r) picks)
             (KdefBigConjF (SurpriseConstsConj.enum consts) F1
                           (SurpriseConstsConj.M consts) (natCode r)))
monoShift consts r picks dComp =
  let N : Nat
      N = SurpriseConstsConj.N consts
      M : Nat
      M = SurpriseConstsConj.M consts
      enum : Fun1
      enum = SurpriseConstsConj.enum consts

      Krest : Formula
      Krest = BigConjFormula consts (suc r) picks
              -- = bigConjCountT enum (countDays N (suc r)) (suc r) picks openFuel

      Krc : Formula
      Krc = bigConjCountT enum (countDays N (suc r)) (suc r) picks constHalts

      -- (up)  K_rest @ x0  =>  K_rest @ common   ( = substF 0 common K_rest ).
      step1 : Deriv (imp Krest Krc)
      step1 = bigConjLift enum (countDays N (suc r)) (suc r) picks

      -- instantiate  dComp  at the common fuel.
      raw2 : Deriv (imp (substF zero common Krest)
                        (substF zero common (KdefBigConj M enum (natCode r))))
      raw2 = ruleInst zero common dComp

      step2a : Deriv (imp Krc (substF zero common (KdefBigConj M enum (natCode r))))
      step2a = eqSubst
                 (\ A -> Deriv (imp A (substF zero common (KdefBigConj M enum (natCode r)))))
                 (substBigConj enum (countDays N (suc r)) (suc r) picks)
                 raw2

      step2 : Deriv (imp Krc (KdefBigConjF enum common M (natCode r)))
      step2 = eqSubst (\ B -> Deriv (imp Krc B)) (distKBC enum common M r) step2a

      -- (down)  Q @ common  =>  Q @ x1 .
      step3 : Deriv (imp (KdefBigConjF enum common M (natCode r))
                         (KdefBigConjF enum F1 M (natCode r)))
      step3 = kbcShift enum (natCode r) M
  in compI step1 (compI step2 step3)
