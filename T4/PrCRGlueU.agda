{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.PrCRGlueU -- conj3 assembly / decomposition for the full-PR bundled CR
-- dispatch (analogue of T4.CRGlueU), over wfRedFull / PrTri / PrSrc / PrTgt /
-- PrDev.  conj3 p = O  built from
--   (V) wfRedFull (triF p) = O
--   (S) srcF (triF p) = tgtF p
--   (T) tgtF (triF p) = devF (srcF p)
-- and decomposed at a child.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.PrCRGlueU where

open import T4.Base

open import T4.PrQCheckU using ( conj3 ; srcEqF ; tgtEqF )
open import T4.EqDecO    using ( eqDecO ; eqDecO_complete ; eqDecO_sound )
open import T4.PrWfRedFull using ( wfRedFull )
open import T4.PrTri  using ( triF )
open import T4.PrSrc  using ( srcF )
open import T4.PrTgt  using ( tgtF )
open import T4.PrDev  using ( devF )
open import T4.SigmaZeroN using ( sigmaZeroL ; sigmaZeroR )

open import BRA3.Church       using ( pi ; sigma ; isZero ; T33 )
open import BRA3.SubT.NatEq   using ( natEqF )
open import BRA3.PairAlgebra  using ( compose1U ; compose1U_eq )

------------------------------------------------------------------------
-- SECTION 0.  Bare both-zero for sigma.

sigmaBothO : (a b : Term) -> Deriv (eqF a O) -> Deriv (eqF b O) ->
  Deriv (eqF (ap2 sigma a b) O)
sigmaBothO a b ha hb =
  ruleTrans (congL sigma b ha)
    (ruleTrans (congR sigma O hb) (T33 O))

------------------------------------------------------------------------
-- SECTION 1.  Unfolds.

srcEqF_unfold : (p : Term) ->
  Deriv (eqF (ap1 srcEqF p) (eqDecO (ap1 srcF (ap1 triF p)) (ap1 tgtF p)))
srcEqF_unfold p =
  ruleTrans (compose1U_eq isZero (C natEqF (compose1U srcF triF) tgtF) p)
    (cong1 isZero
      (ruleTrans (ax_C natEqF (compose1U srcF triF) tgtF p)
                 (congL natEqF (ap1 tgtF p) (compose1U_eq srcF triF p))))

tgtEqF_unfold : (p : Term) ->
  Deriv (eqF (ap1 tgtEqF p) (eqDecO (ap1 tgtF (ap1 triF p)) (ap1 devF (ap1 srcF p))))
tgtEqF_unfold p =
  ruleTrans (compose1U_eq isZero (C natEqF (compose1U tgtF triF) (compose1U devF srcF)) p)
    (cong1 isZero
      (ruleTrans (ax_C natEqF (compose1U tgtF triF) (compose1U devF srcF) p)
                 (ruleTrans (congL natEqF (ap1 (compose1U devF srcF) p) (compose1U_eq tgtF triF p))
                            (congR natEqF (ap1 tgtF (ap1 triF p)) (compose1U_eq devF srcF p)))))

conj3_unfold : (p : Term) ->
  Deriv (eqF (ap1 conj3 p)
             (ap2 sigma (ap1 wfRedFull (ap1 triF p))
                        (ap2 sigma (eqDecO (ap1 srcF (ap1 triF p)) (ap1 tgtF p))
                                   (eqDecO (ap1 tgtF (ap1 triF p)) (ap1 devF (ap1 srcF p))))))
conj3_unfold p =
  ruleTrans (ax_C sigma (compose1U wfRedFull triF) (C sigma srcEqF tgtEqF) p)
    (ruleTrans (congL sigma (ap1 (C sigma srcEqF tgtEqF) p) (compose1U_eq wfRedFull triF p))
      (congR sigma (ap1 wfRedFull (ap1 triF p))
        (ruleTrans (ax_C sigma srcEqF tgtEqF p)
          (ruleTrans (congL sigma (ap1 tgtEqF p) (srcEqF_unfold p))
                     (congR sigma (eqDecO (ap1 srcF (ap1 triF p)) (ap1 tgtF p))
                            (tgtEqF_unfold p))))))

------------------------------------------------------------------------
-- SECTION 2.  Build conj3 p = O.

buildConj3 : (p : Term) ->
  Deriv (eqF (ap1 wfRedFull (ap1 triF p)) O) ->
  Deriv (eqF (ap1 srcF (ap1 triF p)) (ap1 tgtF p)) ->
  Deriv (eqF (ap1 tgtF (ap1 triF p)) (ap1 devF (ap1 srcF p))) ->
  Deriv (eqF (ap1 conj3 p) O)
buildConj3 p hV hS hT =
  let sO : Deriv (eqF (eqDecO (ap1 srcF (ap1 triF p)) (ap1 tgtF p)) O)
      sO = eqDecO_complete (ap1 srcF (ap1 triF p)) (ap1 tgtF p) hS
      tO : Deriv (eqF (eqDecO (ap1 tgtF (ap1 triF p)) (ap1 devF (ap1 srcF p))) O)
      tO = eqDecO_complete (ap1 tgtF (ap1 triF p)) (ap1 devF (ap1 srcF p)) hT
      inner : Deriv (eqF (ap2 sigma (eqDecO (ap1 srcF (ap1 triF p)) (ap1 tgtF p))
                                    (eqDecO (ap1 tgtF (ap1 triF p)) (ap1 devF (ap1 srcF p)))) O)
      inner = sigmaBothO _ _ sO tO
      outer : Deriv (eqF (ap2 sigma (ap1 wfRedFull (ap1 triF p))
                            (ap2 sigma (eqDecO (ap1 srcF (ap1 triF p)) (ap1 tgtF p))
                                       (eqDecO (ap1 tgtF (ap1 triF p)) (ap1 devF (ap1 srcF p))))) O)
      outer = sigmaBothO _ _ hV inner
  in ruleTrans (conj3_unfold p) outer

------------------------------------------------------------------------
-- SECTION 3.  Decompose conj3 c = O.

childV : (c : Term) -> Deriv (eqF (ap1 conj3 c) O) ->
  Deriv (eqF (ap1 wfRedFull (ap1 triF c)) O)
childV c h =
  mp (sigmaZeroL _ _) (ruleTrans (ruleSym (conj3_unfold c)) h)

childS : (c : Term) -> Deriv (eqF (ap1 conj3 c) O) ->
  Deriv (eqF (ap1 srcF (ap1 triF c)) (ap1 tgtF c))
childS c h =
  let innerO = mp (sigmaZeroR _ _) (ruleTrans (ruleSym (conj3_unfold c)) h)
      sO = mp (sigmaZeroL _ _) innerO
  in eqDecO_sound (ap1 srcF (ap1 triF c)) (ap1 tgtF c) sO

childT : (c : Term) -> Deriv (eqF (ap1 conj3 c) O) ->
  Deriv (eqF (ap1 tgtF (ap1 triF c)) (ap1 devF (ap1 srcF c)))
childT c h =
  let innerO = mp (sigmaZeroR _ _) (ruleTrans (ruleSym (conj3_unfold c)) h)
      tO = mp (sigmaZeroR _ _) innerO
  in eqDecO_sound (ap1 tgtF (ap1 triF c)) (ap1 devF (ap1 srcF c)) tO
