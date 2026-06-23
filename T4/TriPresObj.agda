{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.TriPresObj -- the INTERNAL Church-Rosser triangle-preservation theorem,
-- universal in the code:
--
--   triPresObjOpaque :
--     (p : Term) ->
--     Deriv (imp (wfRedSized p = O) (wfRedSized (triFSized p) = O))
--
-- Proved by object  ruleIndNat  on the bound K (var 0) with invariant
--   PhiK = (bigC qcheck O K = O)  =  "every code <= K satisfies Q",
-- whose step is the 5-way tag dispatch (T4.TriPresDispatch.triPresStep), then
-- extracted at a free p via bigCLe + qcheck_sound.
--
-- This discharges the last gap of the BRA internal CR (Theorem A); the object
-- diamond / confluence / Con(Eq) reflection follow downstream.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.TriPresObj where

open import T4.Base

open import T4.DerTriS using ( triFSized ; triStep )
open import T4.WfRedSized using ( wfRedSized ; wfStep )
open import T4.QCheck using ( qcheck ; qcheck_complete ; qcheck_sound )
open import T4.QCheckProj using ( PhiK )
open import T4.BoundedConj using ( bigC ; bigC_base ; bigC_step )
open import T4.BoundedConjProj using ( bigCLe )
open import T4.TriPresDispatch using ( triPresStep )

open import T4.FoldRec using ( fold_at_O )
open import T4.Counting using ( sigma_both_zero_imp )
open import BRA3.Church using ( sigma ; sub ; pi ; T33 )
open import BRA3.PairAlgebra using ( Post ; axZ )
open import BRA3.RecBRA3AtPairUniv using ( sub_self )
open import BRA3.Contrapositive using ( identP )
open import T4.Thm12.ImpHelpers using ( impLift ; impEqTrans )
open import BRA3.RuleInst2 using ( ruleInst2 )

------------------------------------------------------------------------
-- Closed-O facts:  triFSized O = O ,  wfRedSized O = O .

private
  triFSizedO : Deriv (eqF (ap1 triFSized O) O)
  triFSizedO = ruleTrans (fold_at_O Z (Post triStep pi)) (axZ O)

  wfRedSizedO : Deriv (eqF (ap1 wfRedSized O) O)
  wfRedSizedO = ruleTrans (fold_at_O Z (Post wfStep pi)) (axZ O)

  -- Q O :  imp (wfRedSized O = O) (wfRedSized (triFSized O) = O) .
  BO : Deriv (eqF (ap1 wfRedSized (ap1 triFSized O)) O)
  BO = ruleTrans (cong1 wfRedSized triFSizedO) wfRedSizedO

  qcheckO : Deriv (eqF (ap1 qcheck O) O)
  qcheckO = mp (qcheck_complete O) (impLift {eqF (ap1 wfRedSized O) O} BO)

------------------------------------------------------------------------
-- The induction:  PhiK holds for all K  (bigC qcheck O K = O).

phiAll : Deriv PhiK
phiAll = ruleIndNat 0 {P = PhiK} base step
  where
    base : Deriv (substF 0 O PhiK)
    base = ruleTrans (bigC_base qcheck O) qcheckO

    step : Deriv (imp PhiK (substF 0 (ap1 s (var 0)) PhiK))
    step =
      let sk : Term
          sk = ap1 s (var 0)
          bigK : Term
          bigK = ap2 (bigC qcheck) O (var 0)
          sigZero : Deriv (imp PhiK (eqF (ap2 sigma (ap1 qcheck sk) bigK) O))
          sigZero = sigma_both_zero_imp PhiK (ap1 qcheck sk) bigK
                      triPresStep (identP PhiK)
      in impEqTrans (ap2 (bigC qcheck) O sk) (ap2 sigma (ap1 qcheck sk) bigK) O
           (impLift {PhiK} (bigC_step qcheck O (var 0))) sigZero

------------------------------------------------------------------------
-- Extraction at a free code  p .

triPresObjOpaque : (p : Term) ->
  Deriv (imp (eqF (ap1 wfRedSized p) O) (eqF (ap1 wfRedSized (ap1 triFSized p)) O))
triPresObjOpaque p =
  let bigCq_at_p : Deriv (eqF (ap2 (bigC qcheck) O p) O)
      bigCq_at_p = ruleInst 0 p phiAll
      subpp : Deriv (eqF (ap2 sub p p) O)
      subpp = sub_self p
      sigBoth : Deriv (eqF (ap2 sigma (ap2 sub p p) (ap2 (bigC qcheck) O p)) O)
      sigBoth =
        ruleTrans (congL sigma (ap2 (bigC qcheck) O p) subpp)
          (ruleTrans (congR sigma O bigCq_at_p) (T33 O))
      inst : Deriv (imp (eqF (ap2 sigma (ap2 sub p p) (ap2 (bigC qcheck) O p)) O)
                        (eqF (ap1 qcheck p) O))
      inst = ruleInst2 1 p 0 p refl (bigCLe qcheck)
      qcheckp : Deriv (eqF (ap1 qcheck p) O)
      qcheckp = mp inst sigBoth
  in mp (qcheck_sound p) qcheckp
