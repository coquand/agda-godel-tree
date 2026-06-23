{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.PrCRGlueImpU -- imp-form conj3 child extractors for the full-PR bundled CR
-- dispatch glue (analogue of T4.CRGlueImpU's childV/S/T_imp, over wfRedFull and
-- PrTri/PrSrc/PrTgt/PrDev).  The eqDecO/sigma/pi imp-form helpers are GENERIC and
-- re-exported from T4.CRGlueImpU.
--
--   childV_imp c : imp (conj3 c = O) (wfRedFull (triF c) = O)
--   childS_imp c : imp (conj3 c = O) (srcF (triF c) = tgtF c)
--   childT_imp c : imp (conj3 c = O) (tgtF (triF c) = devF (srcF c))
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.PrCRGlueImpU where

open import T4.Base

open import T4.PrQCheckU using ( conj3 )
open import T4.EqDecO  using ( eqDecO )
open import T4.PrCRGlueU using ( conj3_unfold )
open import T4.PrWfRedFull using ( wfRedFull )
open import T4.PrTri  using ( triF )
open import T4.PrSrc  using ( srcF )
open import T4.PrTgt  using ( tgtF )
open import T4.PrDev  using ( devF )
open import T4.SigmaZeroN using ( sigmaZeroL ; sigmaZeroR )

-- re-export the generic imp-form helpers.
open import T4.CRGlueImpU public
  using ( eqDecO_complete_imp ; eqDecO_sound_imp ; sigmaBothO_imp
        ; piBothO_imp ; piZeroL_imp ; piZeroR_imp )

open import BRA3.Church       using ( pi ; sigma )
open import BRA3.Logic        using ( prependEqLeft )
open import BRA3.Contrapositive using ( compI )

------------------------------------------------------------------------

private
  toSigma : (c : Term) ->
    Deriv (imp (eqF (ap1 conj3 c) O)
               (eqF (ap2 sigma (ap1 wfRedFull (ap1 triF c))
                       (ap2 sigma (eqDecO (ap1 srcF (ap1 triF c)) (ap1 tgtF c))
                                  (eqDecO (ap1 tgtF (ap1 triF c)) (ap1 devF (ap1 srcF c))))) O))
  toSigma c =
    prependEqLeft (ap2 sigma (ap1 wfRedFull (ap1 triF c))
                    (ap2 sigma (eqDecO (ap1 srcF (ap1 triF c)) (ap1 tgtF c))
                               (eqDecO (ap1 tgtF (ap1 triF c)) (ap1 devF (ap1 srcF c)))))
                  (ap1 conj3 c) O (ruleSym (conj3_unfold c))

childV_imp : (c : Term) -> Deriv (imp (eqF (ap1 conj3 c) O) (eqF (ap1 wfRedFull (ap1 triF c)) O))
childV_imp c =
  compI (toSigma c)
    (sigmaZeroL (ap1 wfRedFull (ap1 triF c))
       (ap2 sigma (eqDecO (ap1 srcF (ap1 triF c)) (ap1 tgtF c))
                  (eqDecO (ap1 tgtF (ap1 triF c)) (ap1 devF (ap1 srcF c)))))

childS_imp : (c : Term) ->
  Deriv (imp (eqF (ap1 conj3 c) O) (eqF (ap1 srcF (ap1 triF c)) (ap1 tgtF c)))
childS_imp c =
  let inner = ap2 sigma (eqDecO (ap1 srcF (ap1 triF c)) (ap1 tgtF c))
                        (eqDecO (ap1 tgtF (ap1 triF c)) (ap1 devF (ap1 srcF c)))
      toInner : Deriv (imp (eqF (ap1 conj3 c) O) (eqF inner O))
      toInner = compI (toSigma c) (sigmaZeroR (ap1 wfRedFull (ap1 triF c)) inner)
      toSO : Deriv (imp (eqF (ap1 conj3 c) O) (eqF (eqDecO (ap1 srcF (ap1 triF c)) (ap1 tgtF c)) O))
      toSO = compI toInner (sigmaZeroL (eqDecO (ap1 srcF (ap1 triF c)) (ap1 tgtF c))
                              (eqDecO (ap1 tgtF (ap1 triF c)) (ap1 devF (ap1 srcF c))))
  in compI toSO (eqDecO_sound_imp (ap1 srcF (ap1 triF c)) (ap1 tgtF c))

childT_imp : (c : Term) ->
  Deriv (imp (eqF (ap1 conj3 c) O) (eqF (ap1 tgtF (ap1 triF c)) (ap1 devF (ap1 srcF c))))
childT_imp c =
  let inner = ap2 sigma (eqDecO (ap1 srcF (ap1 triF c)) (ap1 tgtF c))
                        (eqDecO (ap1 tgtF (ap1 triF c)) (ap1 devF (ap1 srcF c)))
      toInner : Deriv (imp (eqF (ap1 conj3 c) O) (eqF inner O))
      toInner = compI (toSigma c) (sigmaZeroR (ap1 wfRedFull (ap1 triF c)) inner)
      toTO : Deriv (imp (eqF (ap1 conj3 c) O)
                        (eqF (eqDecO (ap1 tgtF (ap1 triF c)) (ap1 devF (ap1 srcF c))) O))
      toTO = compI toInner (sigmaZeroR (eqDecO (ap1 srcF (ap1 triF c)) (ap1 tgtF c))
                              (eqDecO (ap1 tgtF (ap1 triF c)) (ap1 devF (ap1 srcF c))))
  in compI toTO (eqDecO_sound_imp (ap1 tgtF (ap1 triF c)) (ap1 devF (ap1 srcF c)))
