{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ParBuild -- the object analogs of the Par CONSTRUCTORS (pSu/pAd/pRO/pRS
-- of T4.ChurchRosserProto), as reusable  ParCert -> ParCert  combinators.
--
-- Each takes Par-certificates for the sub-terms and returns a Par-certificate
-- for the composite, with the three side conditions (isCert = O, src = …,
-- tgt = …) discharged by the deep cert equations of T4.ParEnds.  Endpoints
-- are arbitrary object Terms, so these are fully general building blocks for
-- stepPar / tri / confluence (T4.ParReflPres.parRefl is the pZe/diagonal one).
--
--   parSuC : ParCert t t'              -> ParCert (su# t)        (su# t')
--   parAdC : ParCert a a' -> ParCert b b' -> ParCert (ad# a b)  (ad# a' b')
--   parROC : ParCert y y'              -> ParCert (ad# ze# y)    y'
--   parRSC : ParCert x x' -> ParCert y y' -> ParCert (ad# (su# x) y) (su# (ad# x' y'))

module T4.ParBuild where

open import T4.Base

open import T4.ParCert    using ( cSu ; cAd ; cRO ; cRS )
open import T4.ParEnds    using
  ( src ; tgt ; isCert
  ; src_cSu ; src_cAd ; src_cRO ; src_cRS
  ; tgt_cSu ; tgt_cAd ; tgt_cRO ; tgt_cRS
  ; isCert_cSu ; isCert_cAd ; isCert_cRO ; isCert_cRS
  ; pi_O_O )
open import T4.ParReflPres using
  ( ParCert ; mkParCert ; wit ; valid ; srcEq ; tgtEq )
open import T4.TrsCodeObj using ( ze# ; su# ; ad# ; tagSu ; tagAd )

open import BRA3.Church using ( pi )

------------------------------------------------------------------------
-- pSu :  cert  cSu (sub) .

parSuC : {t t' : Term} -> ParCert t t' -> ParCert (su# t) (su# t')
parSuC r =
  mkParCert (cSu (wit r))
    (ruleTrans (isCert_cSu (wit r)) (valid r))
    (ruleTrans (src_cSu (wit r)) (congR Pair tagSu (srcEq r)))
    (ruleTrans (tgt_cSu (wit r)) (congR Pair tagSu (tgtEq r)))

------------------------------------------------------------------------
-- pAd :  cert  cAd (subA) (subB) .

parAdC : {a a' b b' : Term} ->
         ParCert a a' -> ParCert b b' -> ParCert (ad# a b) (ad# a' b')
parAdC {a} {a'} ra rb =
  mkParCert (cAd (wit ra) (wit rb))
    (ruleTrans (isCert_cAd (wit ra) (wit rb))
       (ruleTrans (congL pi (ap1 isCert (wit rb)) (valid ra))
          (ruleTrans (congR pi O (valid rb)) pi_O_O)))
    (ruleTrans (src_cAd (wit ra) (wit rb))
       (congR Pair tagAd
          (ruleTrans (congL Pair (ap1 src (wit rb)) (srcEq ra))
                     (congR Pair a (srcEq rb)))))
    (ruleTrans (tgt_cAd (wit ra) (wit rb))
       (congR Pair tagAd
          (ruleTrans (congL Pair (ap1 tgt (wit rb)) (tgtEq ra))
                     (congR Pair a' (tgtEq rb)))))

------------------------------------------------------------------------
-- pRO :  cert  cRO (sub) .

parROC : {y y' : Term} -> ParCert y y' -> ParCert (ad# ze# y) y'
parROC r =
  mkParCert (cRO (wit r))
    (ruleTrans (isCert_cRO (wit r)) (valid r))
    (ruleTrans (src_cRO (wit r)) (congR Pair tagAd (congR Pair ze# (srcEq r))))
    (ruleTrans (tgt_cRO (wit r)) (tgtEq r))

------------------------------------------------------------------------
-- pRS :  cert  cRS (subX) (subY) .

parRSC : {x x' y y' : Term} ->
         ParCert x x' -> ParCert y y' ->
         ParCert (ad# (su# x) y) (su# (ad# x' y'))
parRSC {x} {x'} rx ry =
  mkParCert (cRS (wit rx) (wit ry))
    (ruleTrans (isCert_cRS (wit rx) (wit ry))
       (ruleTrans (congL pi (ap1 isCert (wit ry)) (valid rx))
          (ruleTrans (congR pi O (valid ry)) pi_O_O)))
    (ruleTrans (src_cRS (wit rx) (wit ry))
       (congR Pair tagAd
          (ruleTrans (congL Pair (ap1 src (wit ry)) (congR Pair tagSu (srcEq rx)))
                     (congR Pair (su# x) (srcEq ry)))))
    (ruleTrans (tgt_cRS (wit rx) (wit ry))
       (congR Pair tagSu
          (congR Pair tagAd
             (ruleTrans (congL Pair (ap1 tgt (wit ry)) (tgtEq rx))
                        (congR Pair x' (tgtEq ry))))))
