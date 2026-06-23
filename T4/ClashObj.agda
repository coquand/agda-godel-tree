{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ClashObj -- STAGE I6 of attempt3 §11: the OBJECT CONSISTENCY ATOM
--
--     zeNotConflSuZe : Not (ConflObj ze (su ze))
--
-- the object analog of the meta  zeNotJoinSuZe / zeNotConvSuZe
-- (T4.ParHeadline): ze and su ze are NOT joinable BY GENUINE OBJECT
-- multi-step (Pars) derivations.  Composed with the forward bridge
-- convJoinObj (T4.JoinObj) this gives the object-route headline
--
--     zeNotConvSuZe-obj : Not (Conv ze (su ze))           [ = 0 != s0 ]
--
-- i.e. Con(T0) for the toy ze/su/ad theory, routed entirely through the
-- OBJECT joinability predicate  ConflObj  (apex + two  Deriv (Pars ..) legs).
--
-- DEPENDENCY ON THE CR TERMINAL (taken ABSTRACTLY -- see attempt3 §14 (E-cons),
-- JoinObj header "isolated as its own interface").  The ONLY thing this file
-- needs from the Church-Rosser internalisation is OBJECT HEAD-STABILITY: that an
-- object reduction  Deriv (Pars ze# w)  pins the apex to  ze , and
-- Deriv (Pars (su# t) w)  pins it to an  su -shape.  These are the coded analogs
-- of the meta  zeSteps / suSteps  and are exactly the Sigma1 reflection the CR
-- terminal is building (DevTrans -> object Par/Pars head-stability).  We package
-- them as the interface  HeadStab  and prove the clash + headline ON TOP, so
-- this file is GREEN and self-contained NOW; the CR terminal discharges
-- HeadStab later and instantiates the two results.
--
-- --safe --without-K --exact-split, no holes, no postulates.

module T4.ClashObj where

open import T4.ParReflPres using ( Tm ; ze ; su )
open import T4.ParConfl    using ( Sg ; car ; prf )
open import T4.ParConflObj using ( ConflObj ; apex ; PsObj ; legL ; legR )
open import T4.ParHeadline using ( Empty ; Not ; Eq ; eqTrans ; zeNeqSu ; Conv )
open import T4.JoinObj     using ( convJoinObj )

------------------------------------------------------------------------
-- The abstract object head-stability interface (the Sigma1 reflection seam,
-- discharged by the CR terminal).  Returns META  Eq  on  Tm : reduction from a
-- constructor is structurally constrained, so the apex shape is a meta fact --
-- exactly as the meta  zeSteps : StepsM ze u -> Eq ze u  and
-- suSteps : StepsM (su t) u -> Sg (\ t' -> Eq u (su t')) .
--
-- NOTE: the legs are taken as the SEALED  PsObj  (= Deriv (Pars (code _)(code _))
-- behind ParConflObj's abstract boundary), NOT the un-sealed  Deriv : feeding an
-- un-sealed leg whose apex is the projection  apex c  re-triggers the heavy
-- Pars-body normalisation (the SECTION 3 wall of ParConflObj) on the CONSUMPTION
-- side too.  With  PsObj  opaque, the constructor/spine comparison stays
-- syntactic.  The CR terminal un-seals with  ParConflObj.unPsObj  inside its own
-- head-stability proof (where the apex is a genuine variable -> fast).

record HeadStab : Set where
  field
    parsZeStab : (w : Tm) -> PsObj ze w -> Eq ze w
    parsSuStab : (t w : Tm) -> PsObj (su t) w -> Sg (\ w' -> Eq w (su w'))

------------------------------------------------------------------------
-- Given head-stability, the object consistency atom and the headline.

module _ (H : HeadStab) where
  open HeadStab H

  -- The two legs of an object join  ConflObj ze (su ze)  force the apex  w  to
  -- be simultaneously  ze  (left leg) and  su w'  (right leg) -- impossible.

  zeNotConflSuZe : Not (ConflObj ze (su ze))
  zeNotConflSuZe c =
    let w  = apex c
        eL = parsZeStab w (legL c)             -- Eq ze w
        sR = parsSuStab ze w (legR c)          -- Sg (\ w' -> Eq w (su w'))
    in zeNeqSu (eqTrans eL (prf sR))           -- Eq ze (su (car sR)) -> Empty

  -- Headline through the forward bridge: 0 is not convertible to s 0 --
  -- Con(T0) for the toy theory, via the OBJECT joinability route.

  zeNotConvSuZe-obj : Not (Conv ze (su ze))
  zeNotConvSuZe-obj cv = zeNotConflSuZe (convJoinObj cv)
