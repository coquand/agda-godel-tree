{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.TriUDiamond -- the INTERNAL opaque CR DIAMOND on the unsized coding,
-- universal in the code:
--
--   diamondU : (p : Term) ->
--     Deriv (imp (wfRed p = O) (conj3 p = O))
--
-- where  conj3 p = O  bundles validity-preservation AND both triangle endpoints
-- (srcF (triF p) = tgtF p  and  tgtF (triF p) = devF (srcF p)).  Proved by object
-- ruleIndNat on the bound K (var 0) with invariant  PhiKU = (bigC qcheckU O K = O) ,
-- whose step is the leaf/node tag dispatch (T4.TriUDispatch.triUStep), then
-- extracted at a free p via bigCLe + qcheckU_sound.  Ports T4.TriPresObj.
--
-- The induction base  qcheckU O = O  holds VACUOUSLY: the strict validity has
-- wfRed O = s O (the fold base is rejectCell), so the guard  wfRed O = O  is
-- absurd -- exactly the "O is not a derivation" strengthening that makes the
-- diamond true universally.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.TriUDiamond where

open import T4.Base

open import T4.WfRed using ( wfRed )
open import T4.QCheckU using ( conj3 ; qcheckU ; qcheckU_complete ; qcheckU_sound )
open import T4.QCheckProjU using ( PhiKU )
open import T4.BoundedConj using ( bigC ; bigC_base ; bigC_step )
open import T4.BoundedConjProj using ( bigCLe )
open import T4.TriUDispatch using ( triUStep )
open import T4.WfRedUOpaque using () renaming ( wfRed_O to wfRedO )
open import T4.DescSndImp using ( neSucc )

open import T4.Counting using ( sigma_both_zero_imp )
open import BRA3.Church using ( sigma ; sub ; T33 )
open import BRA3.RecBRA3AtPairUniv using ( sub_self )
open import BRA3.Contrapositive using ( compI ; identP ; axExFalso )
open import T4.Thm12.ImpHelpers using ( impLift ; impEqTrans )
open import BRA3.RuleInst2 using ( ruleInst2 )
open import T4.GammaCtx using ( gWeak ; gMp ; gApply )

------------------------------------------------------------------------
-- Base:  qcheckU O = O , vacuously (wfRed O = s O).

private
  -- Q O = imp (wfRed O = O) (conj3 O = O) , proved by ex falso from the absurd
  -- guard  wfRed O = O  (since  wfRed O = s O).
  QO : Deriv (imp (eqF (ap1 wfRed O) O) (eqF (ap1 conj3 O) O))
  QO =
    let H : Formula
        H = eqF (ap1 wfRed O) O
        sOeqO : Deriv (imp H (eqF (ap1 s O) O))
        sOeqO = impEqTrans (ap1 s O) (ap1 wfRed O) O (impLift (ruleSym wfRedO)) (identP H)
    in gMp (gApply (axExFalso (eqF (ap1 s O) O) (eqF (ap1 conj3 O) O)) sOeqO)
           (gWeak H (neSucc O))

  qcheckUO : Deriv (eqF (ap1 qcheckU O) O)
  qcheckUO = mp (qcheckU_complete O) QO

------------------------------------------------------------------------
-- The induction:  PhiKU holds for all K .

phiAll : Deriv PhiKU
phiAll = ruleIndNat 0 {P = PhiKU} base step
  where
    base : Deriv (substF 0 O PhiKU)
    base = ruleTrans (bigC_base qcheckU O) qcheckUO

    step : Deriv (imp PhiKU (substF 0 (ap1 s (var 0)) PhiKU))
    step =
      let sk : Term
          sk = ap1 s (var 0)
          bigK : Term
          bigK = ap2 (bigC qcheckU) O (var 0)
          sigZero : Deriv (imp PhiKU (eqF (ap2 sigma (ap1 qcheckU sk) bigK) O))
          sigZero = sigma_both_zero_imp PhiKU (ap1 qcheckU sk) bigK triUStep (identP PhiKU)
      in impEqTrans (ap2 (bigC qcheckU) O sk) (ap2 sigma (ap1 qcheckU sk) bigK) O
           (impLift {PhiKU} (bigC_step qcheckU O (var 0))) sigZero

------------------------------------------------------------------------
-- Extraction at a free code  p :  the opaque diamond.

diamondU : (p : Term) ->
  Deriv (imp (eqF (ap1 wfRed p) O) (eqF (ap1 conj3 p) O))
diamondU p =
  let bigCq_at_p : Deriv (eqF (ap2 (bigC qcheckU) O p) O)
      bigCq_at_p = ruleInst 0 p phiAll
      sigBoth : Deriv (eqF (ap2 sigma (ap2 sub p p) (ap2 (bigC qcheckU) O p)) O)
      sigBoth =
        ruleTrans (congL sigma (ap2 (bigC qcheckU) O p) (sub_self p))
          (ruleTrans (congR sigma O bigCq_at_p) (T33 O))
      inst : Deriv (imp (eqF (ap2 sigma (ap2 sub p p) (ap2 (bigC qcheckU) O p)) O)
                        (eqF (ap1 qcheckU p) O))
      inst = ruleInst2 1 p 0 p refl (bigCLe qcheckU)
      qcheckUp : Deriv (eqF (ap1 qcheckU p) O)
      qcheckUp = mp inst sigBoth
  in mp (qcheckU_sound p) qcheckUp
