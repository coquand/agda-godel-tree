{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ParToCert -- the bridge from the green META confluence (T4.ParConfl, over
-- the indexed ParM) to the green object head-clash (T4.ChainClash, over the
-- CertM trace coding): map each meta parallel step to a cert tree, matching
-- endpoints.
--
--   parToCert  : ParM t u -> CertM
--   srcParToCert : srcM (parToCert p) = code t      (meta Eq)
--   tgtParToCert : tgtM (parToCert p) = code u      (meta Eq)
--
-- Pure meta (Agda) recursion + cong; the endpoint equalities hold because the
-- cert coding's srcM / tgtM (T4.CertTree / T4.ParProof) follow the Par
-- constructors exactly and  code  embeds  ze/su/ad  as  ze#/su#/ad# .
--
-- This connects a meta reduction  StepsM t w  to a transparent trace
-- ChainM (code t)(code w), so  chainHeadZe / joinClash  apply.  (NB this yields
-- the META-INPUT object-leaved consistency; the OBJECT-INPUT BRA |- Con(T0)
-- additionally needs the compileFuel proof-translation + object confluence.)
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.ParToCert where

open import T4.Base

open import T4.ParReflPres using ( Tm ; ze ; su ; ad ; code )
open import T4.ParTri      using ( ParM ; pZe ; pSu ; pAd ; pRO ; pRS )
open import T4.CertTree    using ( CertM ; mZe ; mSu ; mAd ; mRO ; mRS ; srcM )
open import T4.ParProof    using ( tgtM )
open import T4.TrsCodeObj  using ( ze# ; su# ; ad# )

------------------------------------------------------------------------
-- Local meta equality (Term-level, Agda propositional).

data MEq {A : Set} (x : A) : A -> Set where
  mrefl : MEq x x

mcong : {A B : Set} (f : A -> B) {x y : A} -> MEq x y -> MEq (f x) (f y)
mcong f mrefl = mrefl

mcong2 : {A B C : Set} (f : A -> B -> C) {x x' : A} {y y' : B} ->
         MEq x x' -> MEq y y' -> MEq (f x y) (f x' y')
mcong2 f mrefl mrefl = mrefl

------------------------------------------------------------------------
-- The translation.

parToCert : {t u : Tm} -> ParM t u -> CertM
parToCert pZe          = mZe
parToCert (pSu p)      = mSu (parToCert p)
parToCert (pAd pa pb)  = mAd (parToCert pa) (parToCert pb)
parToCert (pRO p)      = mRO (parToCert p)
parToCert (pRS px py)  = mRS (parToCert px) (parToCert py)

------------------------------------------------------------------------
-- Endpoint preservation (source).

srcParToCert : {t u : Tm} (p : ParM t u) -> MEq (srcM (parToCert p)) (code t)
srcParToCert pZe         = mrefl
srcParToCert (pSu p)     = mcong su# (srcParToCert p)
srcParToCert (pAd pa pb) = mcong2 ad# (srcParToCert pa) (srcParToCert pb)
srcParToCert (pRO p)     = mcong (\ x -> ad# ze# x) (srcParToCert p)
srcParToCert (pRS px py) =
  mcong2 (\ a b -> ad# (su# a) b) (srcParToCert px) (srcParToCert py)

------------------------------------------------------------------------
-- Endpoint preservation (target).

tgtParToCert : {t u : Tm} (p : ParM t u) -> MEq (tgtM (parToCert p)) (code u)
tgtParToCert pZe         = mrefl
tgtParToCert (pSu p)     = mcong su# (tgtParToCert p)
tgtParToCert (pAd pa pb) = mcong2 ad# (tgtParToCert pa) (tgtParToCert pb)
tgtParToCert (pRO p)     = tgtParToCert p
tgtParToCert (pRS px py) =
  mcong2 (\ a b -> su# (ad# a b)) (tgtParToCert px) (tgtParToCert py)
