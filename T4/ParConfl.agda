{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ParConfl -- STAGE 4b (deliverable 2c): CONFLUENCE of the toy TRS,
-- by the Tait/Martin-Loef parallel-reduction method (strip + tiling),
-- TERMINATION-FREE.  Object analog of  ChurchRosserProto.{strip,confl,
-- confluence}.
--
-- ARCHITECTURE (chosen): the confluence COMBINATORICS is replayed at the
-- META level over the inductive  ParM  (T4.ParTri), faithful to the proto
-- spec.  The triangle here is the META-VALUED  triM : ParM t u -> ParM u
-- (dev t)  (the proto's  tri ), which COMPOSES -- strip feeds a diamond leg
-- back into the next diamond, so the apex must again be an inductive  ParM
-- (a bare object  ParCert  is inert and cannot be re-developed).  The OBJECT
-- content -- a Par-certificate for every meta step -- is supplied separately
-- by the homomorphism  T4.ParCertOf.certOf : ParM t u -> ParCert (code t)
-- (code u)  (and  T4.ParTri.tri  is its triangle instance).
--
-- This file is pure meta combinatorics (no object Term / Deriv); it is the
-- VERIFIED SPEC whose every leaf carries an object certificate via certOf.

module T4.ParConfl where

open import T4.ParReflPres using ( Tm ; ze ; su ; ad )
open import T4.ParTri      using ( ParM ; pZe ; pSu ; pAd ; pRO ; pRS ; dev )
open import T4.ParStep     using ( StepM ; stO ; stS ; stSu ; stA1 ; stA2 )

------------------------------------------------------------------------
-- Minimal meta prelude (Sigma over Tm, binary conjunction).

record Sg (B : Tm -> Set) : Set where
  constructor mkSg
  field
    car : Tm
    prf : B car
open Sg public

data Conj (A B : Set) : Set where
  mkConj : A -> B -> Conj A B

prjL : {A B : Set} -> Conj A B -> A
prjL (mkConj a _) = a

prjR : {A B : Set} -> Conj A B -> B
prjR (mkConj _ b) = b

------------------------------------------------------------------------
-- The META triangle (proto  tri , returning an inductive  ParM ).

triM : {t u : Tm} -> ParM t u -> ParM u (dev t)
triM pZe                    = pZe
triM (pSu p)                = pSu (triM p)
triM (pAd pZe pb)           = pRO (triM pb)
triM (pAd (pSu px) pb)      = pRS (triM px) (triM pb)
triM (pAd (pAd pa1 pa2) pb) = pAd (triM (pAd pa1 pa2)) (triM pb)
triM (pAd (pRO p) pb)       = pAd (triM (pRO p)) (triM pb)
triM (pAd (pRS px py) pb)   = pAd (triM (pRS px py)) (triM pb)
triM (pRO p)                = triM p
triM (pRS px py)            = pSu (pAd (triM px) (triM py))

-- Diamond for  ParM , immediate from the triangle.

diamondM : {t u1 u2 : Tm} -> ParM t u1 -> ParM t u2 ->
           Sg (\ w -> Conj (ParM u1 w) (ParM u2 w))
diamondM {t} p1 p2 = mkSg (dev t) (mkConj (triM p1) (triM p2))

------------------------------------------------------------------------
-- Reflexive-transitive closure of  ParM , and the strip lemma.

data ParsM : Tm -> Tm -> Set where
  pdone : {t : Tm}                                     -> ParsM t t
  pmore : {t u v : Tm} -> ParM t u -> ParsM u v        -> ParsM t v

stripM : {t u v : Tm} -> ParM t u -> ParsM t v ->
         Sg (\ w -> Conj (ParsM u w) (ParM v w))
stripM {t} {u} p pdone = mkSg u (mkConj pdone p)
stripM p (pmore q qs) =
  let d = diamondM p q
      r = stripM (prjR (prf d)) qs
  in mkSg (car r)
       (mkConj (pmore (prjL (prf d)) (prjL (prf r))) (prjR (prf r)))

confl : {t v1 v2 : Tm} -> ParsM t v1 -> ParsM t v2 ->
        Sg (\ w -> Conj (ParsM v1 w) (ParsM v2 w))
confl {t} {v1} {v2} pdone qs = mkSg v2 (mkConj qs pdone)
confl (pmore p ps) qs =
  let s = stripM p qs
      r = confl ps (prjL (prf s))
  in mkSg (car r)
       (mkConj (prjL (prf r)) (pmore (prjR (prf s)) (prjR (prf r))))

------------------------------------------------------------------------
-- Single-step reduction and its closure, and the Step <= Par <= Steps
-- sandwich (all META, proto-verbatim), giving confluence over  StepsM .

data StepsM : Tm -> Tm -> Set where
  doneS : {t : Tm}                                       -> StepsM t t
  moreS : {t u v : Tm} -> StepM t u -> StepsM u v         -> StepsM t v

stepsTransM : {t u v : Tm} -> StepsM t u -> StepsM u v -> StepsM t v
stepsTransM doneS         ss2 = ss2
stepsTransM (moreS st ss) ss2 = moreS st (stepsTransM ss ss2)

stepsSuM : {t t' : Tm} -> StepsM t t' -> StepsM (su t) (su t')
stepsSuM doneS         = doneS
stepsSuM (moreS st ss) = moreS (stSu st) (stepsSuM ss)

stepsA1M : {a a' b : Tm} -> StepsM a a' -> StepsM (ad a b) (ad a' b)
stepsA1M doneS         = doneS
stepsA1M (moreS st ss) = moreS (stA1 st) (stepsA1M ss)

stepsA2M : {a b b' : Tm} -> StepsM b b' -> StepsM (ad a b) (ad a b')
stepsA2M doneS         = doneS
stepsA2M (moreS st ss) = moreS (stA2 st) (stepsA2M ss)

stepsAM : {a a' b b' : Tm} -> StepsM a a' -> StepsM b b' ->
          StepsM (ad a b) (ad a' b')
stepsAM sa sb = stepsTransM (stepsA1M sa) (stepsA2M sb)

parReflM : (t : Tm) -> ParM t t
parReflM ze       = pZe
parReflM (su t)   = pSu (parReflM t)
parReflM (ad a b) = pAd (parReflM a) (parReflM b)

stepParM : {t u : Tm} -> StepM t u -> ParM t u
stepParM (stO y)            = pRO (parReflM y)
stepParM (stS x y)          = pRS (parReflM x) (parReflM y)
stepParM (stSu st)          = pSu (stepParM st)
stepParM (stA1 {a} {a'} {b} st) = pAd (stepParM st) (parReflM b)
stepParM (stA2 {a} {b} {b'} st) = pAd (parReflM a) (stepParM st)

parStepsM : {t u : Tm} -> ParM t u -> StepsM t u
parStepsM pZe                    = doneS
parStepsM (pSu p)                = stepsSuM (parStepsM p)
parStepsM (pAd pa pb)            = stepsAM (parStepsM pa) (parStepsM pb)
parStepsM (pRO {y} p)            = moreS (stO y) (parStepsM p)
parStepsM (pRS {x} {x'} {y} px py) =
  moreS (stS x y) (stepsSuM (stepsAM (parStepsM px) (parStepsM py)))

stepsParsM : {t u : Tm} -> StepsM t u -> ParsM t u
stepsParsM doneS         = pdone
stepsParsM (moreS st ss) = pmore (stepParM st) (stepsParsM ss)

parsStepsM : {t u : Tm} -> ParsM t u -> StepsM t u
parsStepsM pdone        = doneS
parsStepsM (pmore p ps) = stepsTransM (parStepsM p) (parsStepsM ps)

-- Church-Rosser for the toy TRS (over single-step reduction).

confluence : {t v1 v2 : Tm} -> StepsM t v1 -> StepsM t v2 ->
             Sg (\ w -> Conj (StepsM v1 w) (StepsM v2 w))
confluence s1 s2 =
  let r = confl (stepsParsM s1) (stepsParsM s2)
  in mkSg (car r)
       (mkConj (parsStepsM (prjL (prf r))) (parsStepsM (prjR (prf r))))
