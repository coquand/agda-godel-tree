{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.DevTriObj -- the OBJECT DIAGONAL DEVELOPMENT STEP, the first deliverable
-- of the internal triangle (attempt3 §11 I4):
--
--     triObj : (t : Tm) -> Deriv (Par (code t) (code (dev t)))
--
-- every term parallel-reduces, IN ONE OBJECT Par step, to its complete
-- development -- with the witness an OBJECT-COMPUTED certificate
-- devCertF (code t) (T4.DevCertF), not a meta-assembled one.  This is
-- tri at the reflexive step (ChurchRosserProto: tri (parRefl t) : Par t (dev t)),
-- now carried by the object development-cert builder.
--
-- The three certificate side conditions are the ENDPOINT / VALIDITY
-- preservation lemmas for  devCertF , each a structural META induction on
-- t : Tm  (the term structure is carried by  Tm , exactly as T4.ParReflPres /
-- T4.DevFCode) chaining the matching  devCertF  closure equation (T4.DevCertF)
-- with the matching  src / tgt / isCert  closure equation (T4.ParEnds) and the
-- subterm IH:
--     src_devCert    : src    (devCertF (code t)) = code t
--     tgt_devCert    : tgt    (devCertF (code t)) = code (dev t)
--     isCert_devCert : isCert (devCertF (code t)) = O
-- Each per-case object equation is itself a course-of-values ruleIndNat result
-- (the cov-folds devCertF / src / tgt / isCert), so the object content is fully
-- internal; the meta recursion only assembles the cases.  Then  parIntro
-- (T4.ParIntro) lifts the certificate to the genuine object  Deriv (Par ..) .
-- No holes, no postulates.

module T4.DevTriObj where

open import T4.Base

open import T4.DevCertF using
  ( devCertF
  ; devCert_at_ze ; devCert_at_su ; devCert_at_adZe ; devCert_at_adSu ; devCert_at_adAd )
open import T4.ParEnds using
  ( src ; tgt ; isCert ; pi_O_O
  ; src_cZe ; src_cSu ; src_cAd ; src_cRO ; src_cRS
  ; tgt_cZe ; tgt_cSu ; tgt_cAd ; tgt_cRO ; tgt_cRS
  ; isCert_cZe ; isCert_cSu ; isCert_cAd ; isCert_cRO ; isCert_cRS )
open import T4.TrsCodeObj  using ( ze# ; su# ; ad# ; tagSu ; tagAd )
open import T4.ParReflPres using ( Tm ; ze ; su ; ad ; code ; ParCert ; mkParCert )
open import T4.ParTri      using ( dev )
open import T4.ParIntro    using ( Par ; parIntro )

open import BRA3.Church using ( pi )

------------------------------------------------------------------------
-- SECTION 1.  Source preservation:  src (devCertF (code t)) = code t .

src_devCert : (t : Tm) -> Deriv (eqF (ap1 src (ap1 devCertF (code t))) (code t))
src_devCert ze =
  ruleTrans (cong1 src devCert_at_ze) src_cZe
src_devCert (su t) =
  ruleTrans (cong1 src (devCert_at_su (code t)))
    (ruleTrans (src_cSu (ap1 devCertF (code t)))
               (congR Pair tagSu (src_devCert t)))
src_devCert (ad ze y) =
  ruleTrans (cong1 src (devCert_at_adZe (code y)))
    (ruleTrans (src_cRO (ap1 devCertF (code y)))
               (congR Pair tagAd (congR Pair ze# (src_devCert y))))
src_devCert (ad (su x) y) =
  let inner : Deriv (eqF (ap2 Pair (su# (ap1 src (ap1 devCertF (code x))))
                                   (ap1 src (ap1 devCertF (code y))))
                         (ap2 Pair (su# (code x)) (code y)))
      inner = ruleTrans (congL Pair (ap1 src (ap1 devCertF (code y)))
                          (congR Pair tagSu (src_devCert x)))
                        (congR Pair (su# (code x)) (src_devCert y))
  in ruleTrans (cong1 src (devCert_at_adSu (code x) (code y)))
       (ruleTrans (src_cRS (ap1 devCertF (code x)) (ap1 devCertF (code y)))
                  (congR Pair tagAd inner))
src_devCert (ad (ad p q) y) =
  let inner : Deriv (eqF (ap2 Pair (ap1 src (ap1 devCertF (code (ad p q))))
                                   (ap1 src (ap1 devCertF (code y))))
                         (ap2 Pair (code (ad p q)) (code y)))
      inner = ruleTrans (congL Pair (ap1 src (ap1 devCertF (code y))) (src_devCert (ad p q)))
                        (congR Pair (code (ad p q)) (src_devCert y))
  in ruleTrans (cong1 src (devCert_at_adAd (code p) (code q) (code y)))
       (ruleTrans (src_cAd (ap1 devCertF (code (ad p q))) (ap1 devCertF (code y)))
                  (congR Pair tagAd inner))

------------------------------------------------------------------------
-- SECTION 2.  Target preservation:  tgt (devCertF (code t)) = code (dev t) .

tgt_devCert : (t : Tm) -> Deriv (eqF (ap1 tgt (ap1 devCertF (code t))) (code (dev t)))
tgt_devCert ze =
  ruleTrans (cong1 tgt devCert_at_ze) tgt_cZe
tgt_devCert (su t) =
  ruleTrans (cong1 tgt (devCert_at_su (code t)))
    (ruleTrans (tgt_cSu (ap1 devCertF (code t)))
               (congR Pair tagSu (tgt_devCert t)))
tgt_devCert (ad ze y) =
  ruleTrans (cong1 tgt (devCert_at_adZe (code y)))
    (ruleTrans (tgt_cRO (ap1 devCertF (code y))) (tgt_devCert y))
tgt_devCert (ad (su x) y) =
  let inner : Deriv (eqF (ap2 Pair (ap1 tgt (ap1 devCertF (code x)))
                                   (ap1 tgt (ap1 devCertF (code y))))
                         (ap2 Pair (code (dev x)) (code (dev y))))
      inner = ruleTrans (congL Pair (ap1 tgt (ap1 devCertF (code y))) (tgt_devCert x))
                        (congR Pair (code (dev x)) (tgt_devCert y))
  in ruleTrans (cong1 tgt (devCert_at_adSu (code x) (code y)))
       (ruleTrans (tgt_cRS (ap1 devCertF (code x)) (ap1 devCertF (code y)))
                  (congR Pair tagSu (congR Pair tagAd inner)))
tgt_devCert (ad (ad p q) y) =
  let inner : Deriv (eqF (ap2 Pair (ap1 tgt (ap1 devCertF (code (ad p q))))
                                   (ap1 tgt (ap1 devCertF (code y))))
                         (ap2 Pair (code (dev (ad p q))) (code (dev y))))
      inner = ruleTrans (congL Pair (ap1 tgt (ap1 devCertF (code y))) (tgt_devCert (ad p q)))
                        (congR Pair (code (dev (ad p q))) (tgt_devCert y))
  in ruleTrans (cong1 tgt (devCert_at_adAd (code p) (code q) (code y)))
       (ruleTrans (tgt_cAd (ap1 devCertF (code (ad p q))) (ap1 devCertF (code y)))
                  (congR Pair tagAd inner))

------------------------------------------------------------------------
-- SECTION 3.  Validity:  isCert (devCertF (code t)) = O .

isCert_devCert : (t : Tm) -> Deriv (eqF (ap1 isCert (ap1 devCertF (code t))) O)
isCert_devCert ze =
  ruleTrans (cong1 isCert devCert_at_ze) isCert_cZe
isCert_devCert (su t) =
  ruleTrans (cong1 isCert (devCert_at_su (code t)))
    (ruleTrans (isCert_cSu (ap1 devCertF (code t))) (isCert_devCert t))
isCert_devCert (ad ze y) =
  ruleTrans (cong1 isCert (devCert_at_adZe (code y)))
    (ruleTrans (isCert_cRO (ap1 devCertF (code y))) (isCert_devCert y))
isCert_devCert (ad (su x) y) =
  ruleTrans (cong1 isCert (devCert_at_adSu (code x) (code y)))
    (ruleTrans (isCert_cRS (ap1 devCertF (code x)) (ap1 devCertF (code y)))
      (ruleTrans (congL pi (ap1 isCert (ap1 devCertF (code y))) (isCert_devCert x))
        (ruleTrans (congR pi O (isCert_devCert y)) pi_O_O)))
isCert_devCert (ad (ad p q) y) =
  ruleTrans (cong1 isCert (devCert_at_adAd (code p) (code q) (code y)))
    (ruleTrans (isCert_cAd (ap1 devCertF (code (ad p q))) (ap1 devCertF (code y)))
      (ruleTrans (congL pi (ap1 isCert (ap1 devCertF (code y))) (isCert_devCert (ad p q)))
        (ruleTrans (congR pi O (isCert_devCert y)) pi_O_O)))

------------------------------------------------------------------------
-- SECTION 4.  The development certificate and the diagonal triangle.

triCert : (t : Tm) -> ParCert (code t) (code (dev t))
triCert t = mkParCert (ap1 devCertF (code t))
                      (isCert_devCert t) (src_devCert t) (tgt_devCert t)

triObj : (t : Tm) -> Deriv (Par (code t) (code (dev t)))
triObj t = parIntro t (dev t) (triCert t)
