{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.JoinObj -- the FORWARD soundness bridge of the object Church-Rosser
-- internalisation: META convertibility / joinability of toy terms is realised
-- by genuine OBJECT joinability derivations.
--
--   joinObjOf   : Join t u -> ConflObj t u     (lift a meta join to object Pars)
--   convJoinObj : Conv t u -> ConflObj t u     (= joinObjOf . convJoin)
--
-- where  ConflObj t u  (T4.ParConflObj) packages a common apex  w  with two
-- OBJECT multi-step derivations  Deriv (Pars (code t)(code w)) ,
-- Deriv (Pars (code u)(code w)) .
--
-- ARCHITECTURE.  This is the "(b) soundness, forward direction" of attempt3
-- §10-12: every META reduction sequence  StepsM  out of a toy term is lifted,
-- step by step, to an object  Pars  derivation by  T4.ParsObj.parsObjOf (after
-- StepsM -> ParsM via  stepsParsM).  No object reflection is needed for THIS
-- direction -- the meta witness  car j  supplies the apex and the two legs are
-- pushed into the object world unchanged.
--
-- WHAT REMAINS (the hard half, NOT in this file).  The BACKWARD direction --
-- object NON-joinability  Not (ConflObj ze (su ze))  giving BRA |- Con(T0) --
-- needs object head-stability (the coded analog of  zeSteps / suSteps : an
-- object  Deriv (Pars ze# w)  forces  w  to be ze-shaped), which is the genuine
-- Sigma1 reflection / (E-cons) obligation of attempt3 §14.  A bare  ConflObj
-- carries no meta source to invert, so it cannot be discharged by the lifting
-- used here; it is isolated as its own interface (cf. T4.ConvInterface).
--
-- --safe --without-K --exact-split, no holes, no postulates.

module T4.JoinObj where

open import T4.Base

open import T4.ParReflPres using ( Tm ; code )
open import T4.ParConfl    using
  ( Sg ; mkSg ; car ; prf ; Conj ; mkConj ; prjL ; prjR ; StepsM ; stepsParsM )
open import T4.ParsObj     using ( Pars ; parsObjOf )
open import T4.ParConflObj using ( ConflObj )
open import T4.ParHeadline using ( Join ; Conv ; convJoin )

------------------------------------------------------------------------
-- SECTION 1.  Meta join -> object join.
--   Both meta  StepsM  legs of the join are converted to  ParsM  (stepsParsM)
--   and then lifted to object  Pars  derivations (parsObjOf) over the common
--   apex  car j .

joinObjOf : {t uu : Tm} -> Join t uu -> ConflObj t uu
joinObjOf {t} {uu} j =
  mkSg (car j)
       (mkConj (parsObjOf t (car j) (stepsParsM (prjL (prf j))))
               (parsObjOf uu (car j) (stepsParsM (prjR (prf j)))))

------------------------------------------------------------------------
-- SECTION 2.  Meta convertibility -> object joinability.
--   The Church-Rosser corollary  convJoin (T4.ParHeadline) turns convertibility
--   into a meta join; Section 1 then delivers the object derivations.

convJoinObj : {t uu : Tm} -> Conv t uu -> ConflObj t uu
convJoinObj c = joinObjOf (convJoin c)
