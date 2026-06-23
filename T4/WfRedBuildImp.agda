{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.WfRedBuildImp -- the IMP-FORM (Carneiro) BUILD step: under a carried
-- hypothesis phi, the validity of the CHILDREN lifts to the validity of the
-- BUILT constructor.  These transform  imp phi (wfRedSized child = O)  into
-- imp phi (wfRedSized (szDer.. children) = O)  -- the "rebuild" half of the
-- covFuel step (T4.TriPresObjOpaque), composed after extract-imp + IH.
--
-- Immediate from the wfRedSized defining equations + sigma_both_zero_imp.
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.WfRedBuildImp where

open import T4.Base

open import T4.DerCodeS using ( szDerZe ; szDerSu ; szDerAd ; szDerRO ; szDerRS )
open import T4.WfRedSized
  using ( wfRedSized ; wfRedSized_Ze ; wfRedSized_Su ; wfRedSized_Ad
        ; wfRedSized_RO ; wfRedSized_RS )

open import BRA3.Church  using ( sigma )
open import BRA3.Logic   using ( prependEqLeft )
open import BRA3.Contrapositive using ( compI ; liftP )
open import T4.Counting  using ( sigma_both_zero_imp )

------------------------------------------------------------------------
-- sigma O Y = O  under phi, from  Y = O  under phi.

private
  sigOY_imp : (phi : Formula) (Y : Term) ->
    Deriv (imp phi (eqF Y O)) -> Deriv (imp phi (eqF (ap2 sigma O Y) O))
  sigOY_imp phi Y h =
    sigma_both_zero_imp phi O Y (liftP phi (axRefl O)) h

------------------------------------------------------------------------
-- The five build steps.

build_Ze_imp : (phi : Formula) ->
  Deriv (imp phi (eqF (ap1 wfRedSized szDerZe) O))
build_Ze_imp phi = liftP phi wfRedSized_Ze

build_Su_imp : (phi : Formula) (X : Term) ->
  Deriv (imp phi (eqF (ap1 wfRedSized X) O)) ->
  Deriv (imp phi (eqF (ap1 wfRedSized (szDerSu X)) O))
build_Su_imp phi X h =
  compI (sigOY_imp phi (ap1 wfRedSized X) h)
        (prependEqLeft (ap1 wfRedSized (szDerSu X))
                       (ap2 sigma O (ap1 wfRedSized X)) O (wfRedSized_Su X))

build_RO_imp : (phi : Formula) (X : Term) ->
  Deriv (imp phi (eqF (ap1 wfRedSized X) O)) ->
  Deriv (imp phi (eqF (ap1 wfRedSized (szDerRO X)) O))
build_RO_imp phi X h =
  compI (sigOY_imp phi (ap1 wfRedSized X) h)
        (prependEqLeft (ap1 wfRedSized (szDerRO X))
                       (ap2 sigma O (ap1 wfRedSized X)) O (wfRedSized_RO X))

build_Ad_imp : (phi : Formula) (X1 X2 : Term) ->
  Deriv (imp phi (eqF (ap1 wfRedSized X1) O)) ->
  Deriv (imp phi (eqF (ap1 wfRedSized X2) O)) ->
  Deriv (imp phi (eqF (ap1 wfRedSized (szDerAd X1 X2)) O))
build_Ad_imp phi X1 X2 h1 h2 =
  let inner : Deriv (imp phi (eqF (ap2 sigma (ap1 wfRedSized X1) (ap1 wfRedSized X2)) O))
      inner = sigma_both_zero_imp phi (ap1 wfRedSized X1) (ap1 wfRedSized X2) h1 h2
  in compI (sigOY_imp phi (ap2 sigma (ap1 wfRedSized X1) (ap1 wfRedSized X2)) inner)
           (prependEqLeft (ap1 wfRedSized (szDerAd X1 X2))
                          (ap2 sigma O (ap2 sigma (ap1 wfRedSized X1) (ap1 wfRedSized X2))) O
                          (wfRedSized_Ad X1 X2))

build_RS_imp : (phi : Formula) (X1 X2 : Term) ->
  Deriv (imp phi (eqF (ap1 wfRedSized X1) O)) ->
  Deriv (imp phi (eqF (ap1 wfRedSized X2) O)) ->
  Deriv (imp phi (eqF (ap1 wfRedSized (szDerRS X1 X2)) O))
build_RS_imp phi X1 X2 h1 h2 =
  let inner : Deriv (imp phi (eqF (ap2 sigma (ap1 wfRedSized X1) (ap1 wfRedSized X2)) O))
      inner = sigma_both_zero_imp phi (ap1 wfRedSized X1) (ap1 wfRedSized X2) h1 h2
  in compI (sigOY_imp phi (ap2 sigma (ap1 wfRedSized X1) (ap1 wfRedSized X2)) inner)
           (prependEqLeft (ap1 wfRedSized (szDerRS X1 X2))
                          (ap2 sigma O (ap2 sigma (ap1 wfRedSized X1) (ap1 wfRedSized X2))) O
                          (wfRedSized_RS X1 X2))
