{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ParObj -- OBJECT internalisation of parallel reduction: the object
-- predicate  Par (code t)(code u)  (T4.ParIntro) has genuine  Deriv
-- introduction rules, obtained by lifting the certificate builders through
-- parIntro.  This turns the relational/certificate development into BRA
-- object derivations.
--
--   parObjOf  : ParM t u -> Deriv (Par (code t)(code u))   (the main bridge:
--               EVERY meta parallel step is an object Par-derivation)
--   parReflObj: Deriv (Par (code t)(code t))               (reflexivity)
--   parStepObj: StepM t u -> Deriv (Par (code t)(code u))  (Step <= Par)
--   parSuObj / parAdObj / parROObj / parRSObj             (the constructors)
--
-- All via  parIntro (T4.ParIntro) = E_intro at the certificate witness; the
-- ParCert side conditions are discharged once and for all there.

module T4.ParObj where

open import T4.Base

open import T4.ParReflPres using ( Tm ; ze ; su ; ad ; code ; parRefl )
open import T4.ParTri      using ( ParM )
open import T4.ParStep     using ( StepM ; stepPar )
open import T4.ParCertOf   using ( certOf )
open import T4.ParIntro    using ( Par ; parIntro )

------------------------------------------------------------------------
-- The main bridge: meta parallel reduction -> object Par derivation.

parObjOf : (t uu : Tm) -> ParM t uu -> Deriv (Par (code t) (code uu))
parObjOf t uu p = parIntro t uu (certOf p)

------------------------------------------------------------------------
-- Named introduction rules (reflexivity and single-step inclusion).

parReflObj : (t : Tm) -> Deriv (Par (code t) (code t))
parReflObj t = parIntro t t (parRefl t)

parStepObj : (t uu : Tm) -> StepM t uu -> Deriv (Par (code t) (code uu))
parStepObj t uu st = parIntro t uu (stepPar st)
