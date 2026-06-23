{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.TriPresShadow -- STEP 1 (Theorem A), the STRUCTURAL way: the Takahashi
-- triangle map  triFSized  sends the code of a derivation to the code of a
-- derivation, and hence preserves validity.
--
-- This follows Escardo's Groups.Free Church-Rosser proof in spirit: there the
-- diamond is closed by a function that recurses STRUCTURALLY on the word
-- (each cons-step recurses on the tail, the case split IS the structure), with
-- no measure/fuel and no separate "non-empty" obligation.  Here the analogue is
-- structural recursion on the meta derivation shadow  DerMS  (T4.DerCodeS):
-- every node is a BUILT constructor  szDer..  (its children are explicit
-- codeDerS sub-shadows), so we use the BUILT triFSized / wfBuild equations,
-- the child "descent" is just the recursive call, and the Ad critical-pair
-- dispatch (Ze / Su / else) is read off the LEFT child shadow -- exactly the
-- leaf/node dispatch that  T4.BinTreeInd.binTreeInd  gets from the shadow.
--
-- This deliberately AVOIDS the covFuel-on-opaque-code route, whose meta-level
-- IH demands a BARE child-descent bound (hence a bare  d != O ) that the tag
-- dispatch only ever supplies as an imp-antecedent -- the genuine structural
-- gap documented for the opaque route (cf. T4/BinTreeInd.agda:34-36).
--
-- Delivered:
--   devM      : DerMS -> DerMS                    -- meta development map
--   triShadow : triFSized (codeDerS b) = codeDerS (devM b)
--   validShadow : wfRedSized (codeDerS b) = O     -- every shadow code is valid
--   triPres   : wfRedSized (triFSized (codeDerS b)) = O   -- the triangle is valid
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.TriPresShadow where

open import T4.Base

open import T4.DerCodeS
  using ( DerMS ; msZe ; msSu ; msAd ; msRO ; msRS ; codeDerS
        ; szDerZe ; szDerSu ; szDerAd ; szDerRO ; szDerRS
        ; dtag ; dtag_Ad ; dtag_RO ; dtag_RS )
open import T4.DerCodeSFun
  using ( szDerSuF ; szDerROF ; szDerAdF ; szDerRSF
        ; szDerSuF_eq ; szDerROF_eq ; szDerAdF_eq ; szDerRSF_eq )
open import T4.DerTriS
  using ( triFSized ; triFSized_Ze ; triFSized_Su ; triFSized_RO ; triFSized_RS
        ; triFSized_Ad_Ze ; triFSized_Ad_Su ; triFSized_Ad_else )
open import T4.WfRedSized using ( wfRedSized )
open import T4.WfRedBuild
  using ( wfBuild_Ze ; wfBuild_Su ; wfBuild_RO ; wfBuild_Ad ; wfBuild_RS )

open import BRA3.SubT.V2NatNeq using ( NatNeqWitness ; decideNatNeq )

------------------------------------------------------------------------
-- SECTION 0.  Constructor congruences (via the Fun-code build equations).
-- From  X = Y  derive  szDer.. X = szDer.. Y , by routing through the object
-- Fun-codes  szDer..F  (cong1 / congL / congR) and the build eqs szDer..F_eq.

szSuCong : {X Y : Term} -> Deriv (eqF X Y) -> Deriv (eqF (szDerSu X) (szDerSu Y))
szSuCong {X} {Y} eq =
  ruleTrans (ruleSym (szDerSuF_eq X))
            (ruleTrans (cong1 szDerSuF eq) (szDerSuF_eq Y))

szROCong : {X Y : Term} -> Deriv (eqF X Y) -> Deriv (eqF (szDerRO X) (szDerRO Y))
szROCong {X} {Y} eq =
  ruleTrans (ruleSym (szDerROF_eq X))
            (ruleTrans (cong1 szDerROF eq) (szDerROF_eq Y))

szAdCong : {X1 Y1 X2 Y2 : Term} ->
  Deriv (eqF X1 Y1) -> Deriv (eqF X2 Y2) ->
  Deriv (eqF (szDerAd X1 X2) (szDerAd Y1 Y2))
szAdCong {X1} {Y1} {X2} {Y2} e1 e2 =
  ruleTrans (ruleSym (szDerAdF_eq X1 X2))
    (ruleTrans (ruleTrans (congL szDerAdF X2 e1) (congR szDerAdF Y1 e2))
               (szDerAdF_eq Y1 Y2))

szRSCong : {X1 Y1 X2 Y2 : Term} ->
  Deriv (eqF X1 Y1) -> Deriv (eqF X2 Y2) ->
  Deriv (eqF (szDerRS X1 X2) (szDerRS Y1 Y2))
szRSCong {X1} {Y1} {X2} {Y2} e1 e2 =
  ruleTrans (ruleSym (szDerRSF_eq X1 X2))
    (ruleTrans (ruleTrans (congL szDerRSF X2 e1) (congR szDerRSF Y1 e2))
               (szDerRSF_eq Y1 Y2))

------------------------------------------------------------------------
-- SECTION 1.  The meta development map on shadows  (mirrors the triFSized
-- equations; the Ad case dispatches on the LEFT child shadow).

devM : DerMS -> DerMS
devM msZe              = msZe
devM (msSu a)          = msSu (devM a)
devM (msRO a)          = devM a
devM (msRS l r)        = msSu (msAd (devM l) (devM r))
devM (msAd msZe r)     = msRO (devM r)
devM (msAd (msSu a) r) = msRS (devM a) (devM r)
devM (msAd (msAd l0 r0) r) = msAd (devM (msAd l0 r0)) (devM r)
devM (msAd (msRO a0) r)    = msAd (devM (msRO a0)) (devM r)
devM (msAd (msRS l0 r0) r) = msAd (devM (msRS l0 r0)) (devM r)

------------------------------------------------------------------------
-- SECTION 2.  Neq witnesses for the Ad-else dispatch (left tag 2 / 3 / 4).

w20 : NatNeqWitness 2 0
w20 = decideNatNeq 2 0 (\ ())
w21 : NatNeqWitness 2 1
w21 = decideNatNeq 2 1 (\ ())
w30 : NatNeqWitness 3 0
w30 = decideNatNeq 3 0 (\ ())
w31 : NatNeqWitness 3 1
w31 = decideNatNeq 3 1 (\ ())
w40 : NatNeqWitness 4 0
w40 = decideNatNeq 4 0 (\ ())
w41 : NatNeqWitness 4 1
w41 = decideNatNeq 4 1 (\ ())

------------------------------------------------------------------------
-- SECTION 3.  The triangle on shadows:  triFSized (codeDerS b) = codeDerS (devM b).
-- Structural recursion on b; each case = the BUILT triFSized equation then the
-- constructor congruence applied to the recursive results.

triShadow : (b : DerMS) ->
  Deriv (eqF (ap1 triFSized (codeDerS b)) (codeDerS (devM b)))
triShadow msZe       = triFSized_Ze
triShadow (msSu a)   =
  ruleTrans (triFSized_Su (codeDerS a)) (szSuCong (triShadow a))
triShadow (msRO a)   =
  ruleTrans (triFSized_RO (codeDerS a)) (triShadow a)
triShadow (msRS l r) =
  ruleTrans (triFSized_RS (codeDerS l) (codeDerS r))
            (szSuCong (szAdCong (triShadow l) (triShadow r)))
triShadow (msAd msZe r) =
  ruleTrans (triFSized_Ad_Ze (codeDerS r)) (szROCong (triShadow r))
triShadow (msAd (msSu a) r) =
  ruleTrans (triFSized_Ad_Su (codeDerS a) (codeDerS r))
            (szRSCong (triShadow a) (triShadow r))
triShadow (msAd (msAd l0 r0) r) =
  ruleTrans
    (triFSized_Ad_else (codeDerS (msAd l0 r0)) (codeDerS r) 2 w20 w21
       (dtag_Ad (codeDerS l0) (codeDerS r0)))
    (szAdCong (triShadow (msAd l0 r0)) (triShadow r))
triShadow (msAd (msRO a0) r) =
  ruleTrans
    (triFSized_Ad_else (codeDerS (msRO a0)) (codeDerS r) 3 w30 w31
       (dtag_RO (codeDerS a0)))
    (szAdCong (triShadow (msRO a0)) (triShadow r))
triShadow (msAd (msRS l0 r0) r) =
  ruleTrans
    (triFSized_Ad_else (codeDerS (msRS l0 r0)) (codeDerS r) 4 w40 w41
       (dtag_RS (codeDerS l0) (codeDerS r0)))
    (szAdCong (triShadow (msRS l0 r0)) (triShadow r))

------------------------------------------------------------------------
-- SECTION 4.  Every shadow code is valid (structural recursion on the build
-- direction of the verifier).

validShadow : (b : DerMS) -> Deriv (eqF (ap1 wfRedSized (codeDerS b)) O)
validShadow msZe       = wfBuild_Ze
validShadow (msSu a)   = wfBuild_Su (codeDerS a) (validShadow a)
validShadow (msRO a)   = wfBuild_RO (codeDerS a) (validShadow a)
validShadow (msAd l r) =
  wfBuild_Ad (codeDerS l) (codeDerS r) (validShadow l) (validShadow r)
validShadow (msRS l r) =
  wfBuild_RS (codeDerS l) (codeDerS r) (validShadow l) (validShadow r)

------------------------------------------------------------------------
-- SECTION 5.  STEP 1: the triangle preserves validity.

triPres : (b : DerMS) ->
  Deriv (eqF (ap1 wfRedSized (ap1 triFSized (codeDerS b))) O)
triPres b =
  ruleTrans (cong1 wfRedSized (triShadow b)) (validShadow (devM b))
