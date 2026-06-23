{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.PrWfRedShadow -- soundness of validity: every shadow-coded derivation is
-- valid,  wfRed (codeDer d) = O , by one structural induction on the refined
-- shadow (T4.PrTriShadow).  This is the "introduction" direction that lets an
-- object reduction E-witness be built from a meta shadow (E_intro on codeDer d).
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.PrWfRedShadow where

open import T4.Base

open import T4.PrTriShadow
  using ( DerM ; mRefl ; mAp1c ; mAp2c ; mO ; mU ; mV ; mC ; mRb ; mRs
        ; Fun1M ; Fun2M ; codeF1 ; codeF2 ; codeDer )
open import T4.PrWfRed
  using ( wfRed ; wfRed_reflO ; wfRed_ap1c ; wfRed_ap2c ; wfRed_rO ; wfRed_rU
        ; wfRed_rV ; wfRed_rC ; wfRed_rRb ; wfRed_rRs )
open import T4.ParEnds using ( pi_O_O )

open import BRA3.Church using ( pi )

------------------------------------------------------------------------
-- pi O O collapse from two O children.

piBothO : (l r : Term) -> Deriv (eqF l O) -> Deriv (eqF r O) ->
          Deriv (eqF (ap2 pi l r) O)
piBothO l r el er =
  ruleTrans (congL pi r el) (ruleTrans (congR pi O er) pi_O_O)

------------------------------------------------------------------------
-- wfRed (codeDer d) = O .

wfRedShadow : (d : DerM) -> Deriv (eqF (ap1 wfRed (codeDer d)) O)
wfRedShadow mRefl = wfRed_reflO
wfRedShadow (mAp1c fm d) =
  ruleTrans (wfRed_ap1c (codeF1 fm) (codeDer d)) (wfRedShadow d)
wfRedShadow (mAp2c fm d1 d2) =
  ruleTrans (wfRed_ap2c (codeF2 fm) (codeDer d1) (codeDer d2))
            (piBothO (ap1 wfRed (codeDer d1)) (ap1 wfRed (codeDer d2)) (wfRedShadow d1) (wfRedShadow d2))
wfRedShadow (mO d) = ruleTrans (wfRed_rO (codeDer d)) (wfRedShadow d)
wfRedShadow (mU d) = ruleTrans (wfRed_rU (codeDer d)) (wfRedShadow d)
wfRedShadow (mV d1 d2) =
  ruleTrans (wfRed_rV (codeDer d1) (codeDer d2))
            (piBothO (ap1 wfRed (codeDer d1)) (ap1 wfRed (codeDer d2)) (wfRedShadow d1) (wfRedShadow d2))
wfRedShadow (mC g h1 h2 d) =
  ruleTrans (wfRed_rC (codeF2 g) (codeF1 h1) (codeF1 h2) (codeDer d)) (wfRedShadow d)
wfRedShadow (mRb g h1 h2 d) =
  ruleTrans (wfRed_rRb (codeF1 g) (codeF2 h1) (codeF2 h2) (codeDer d)) (wfRedShadow d)
wfRedShadow (mRs g h1 h2 d1 d2) =
  ruleTrans (wfRed_rRs (codeF1 g) (codeF2 h1) (codeF2 h2) (codeDer d1) (codeDer d2))
            (piBothO (ap1 wfRed (codeDer d1)) (ap1 wfRed (codeDer d2)) (wfRedShadow d1) (wfRedShadow d2))
