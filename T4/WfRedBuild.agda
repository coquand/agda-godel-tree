{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.WfRedBuild -- the BUILD (soundness) direction of the sized verifier:
-- from the child validities, the BUILT constructor is valid.  These are the
-- converse of T4.WfRedExtract and are immediate from the defining equations
-- in T4.WfRedSized (the size check passes by construction, sub_self):
--
--   wfRedSized (szDerSu d)     = sigma O (wfRedSized d)
--   wfRedSized (szDerAd d1 d2) = sigma O (sigma (wfRedSized d1) (wfRedSized d2))
--   ...
--
-- so  wfRedSized child = O  collapses each to  O  by  sigma_at_O_univ .
-- These feed triPresObjOpaque's per-constructor "rebuild" step.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.WfRedBuild where

open import T4.Base

open import T4.DerCodeS using ( szDerZe ; szDerSu ; szDerAd ; szDerRO ; szDerRS )
open import T4.WfRedSized
  using ( wfRedSized ; wfRedSized_Ze ; wfRedSized_Su ; wfRedSized_Ad
        ; wfRedSized_RO ; wfRedSized_RS )

open import BRA3.Church  using ( sigma )
open import T4.LoopReaches using ( sigma_at_O_univ )

------------------------------------------------------------------------
-- sigma O X = O  from  X = O .

private
  sigOX : (b : Term) -> Deriv (eqF b O) -> Deriv (eqF (ap2 sigma O b) O)
  sigOX b hb = ruleTrans (congR sigma O hb) (sigma_at_O_univ O)

  -- sigma X Y = O  from  X = O  and  Y = O .
  sigXY : (a b : Term) ->
    Deriv (eqF a O) -> Deriv (eqF b O) -> Deriv (eqF (ap2 sigma a b) O)
  sigXY a b ha hb =
    ruleTrans (congL sigma b ha) (sigOX b hb)

------------------------------------------------------------------------
-- The five build lemmas.

wfBuild_Ze : Deriv (eqF (ap1 wfRedSized szDerZe) O)
wfBuild_Ze = wfRedSized_Ze

wfBuild_Su : (d : Term) ->
  Deriv (eqF (ap1 wfRedSized d) O) ->
  Deriv (eqF (ap1 wfRedSized (szDerSu d)) O)
wfBuild_Su d hd = ruleTrans (wfRedSized_Su d) (sigOX (ap1 wfRedSized d) hd)

wfBuild_RO : (d : Term) ->
  Deriv (eqF (ap1 wfRedSized d) O) ->
  Deriv (eqF (ap1 wfRedSized (szDerRO d)) O)
wfBuild_RO d hd = ruleTrans (wfRedSized_RO d) (sigOX (ap1 wfRedSized d) hd)

wfBuild_Ad : (d1 d2 : Term) ->
  Deriv (eqF (ap1 wfRedSized d1) O) ->
  Deriv (eqF (ap1 wfRedSized d2) O) ->
  Deriv (eqF (ap1 wfRedSized (szDerAd d1 d2)) O)
wfBuild_Ad d1 d2 h1 h2 =
  ruleTrans (wfRedSized_Ad d1 d2)
    (sigOX (ap2 sigma (ap1 wfRedSized d1) (ap1 wfRedSized d2))
           (sigXY (ap1 wfRedSized d1) (ap1 wfRedSized d2) h1 h2))

wfBuild_RS : (d1 d2 : Term) ->
  Deriv (eqF (ap1 wfRedSized d1) O) ->
  Deriv (eqF (ap1 wfRedSized d2) O) ->
  Deriv (eqF (ap1 wfRedSized (szDerRS d1 d2)) O)
wfBuild_RS d1 d2 h1 h2 =
  ruleTrans (wfRedSized_RS d1 d2)
    (sigOX (ap2 sigma (ap1 wfRedSized d1) (ap1 wfRedSized d2))
           (sigXY (ap1 wfRedSized d1) (ap1 wfRedSized d2) h1 h2))
