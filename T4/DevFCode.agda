{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.DevFCode -- the bridge between the OBJECT complete-development function
-- devF : Fun1 (T4.DevF, a course-of-values fold over the term codes) and the
-- META complete development  dev : Tm -> Tm (T4.ParTri):
--
--     devF_code : (t : Tm) -> Deriv (eqF (ap1 devF (code t)) (code (dev t)))
--
-- i.e. on every CODED term the object fold computes exactly the code of the
-- meta development.  Proved by META structural induction on  t  (the same
-- five-case split as  dev / DevRun.runs), each case CHAINING the matching
-- DevF closure equation (dev_at_ze/su/adZe/adSu/adAd) with the IH at the
-- recursive subterms -- no object course-of-values induction needed (the term
-- structure is carried by the meta  Tm , exactly as in T4.ParReflPres).
--
-- This validates  devF  against the verified meta spec and lets later object
-- triangle work rewrite  devF (code t)  to  code (dev t)  (hence connect to the
-- meta confluence of T4.ParConfl).  No holes, no postulates.

module T4.DevFCode where

open import T4.Base
open import T4.DevF using
  ( devF ; dev_at_ze ; dev_at_su ; dev_at_adZe ; dev_at_adSu ; dev_at_adAd )
open import T4.TrsCodeObj  using ( ze# ; su# ; ad# ; tagSu ; tagAd )
open import T4.ParReflPres using ( Tm ; ze ; su ; ad ; code )
open import T4.ParTri      using ( dev )

devF_code : (t : Tm) -> Deriv (eqF (ap1 devF (code t)) (code (dev t)))

-- dev ze = ze ;  code (dev ze) = ze# = code ze .
devF_code ze = dev_at_ze

-- dev (su t) = su (dev t) ;  code = su# (code (dev t)) .
devF_code (su t) =
  ruleTrans (dev_at_su (code t))
            (congR Pair tagSu (devF_code t))

-- dev (ad ze y) = dev y .
devF_code (ad ze y) =
  ruleTrans (dev_at_adZe (code y)) (devF_code y)

-- dev (ad (su x) y) = su (ad (dev x) (dev y)) .
devF_code (ad (su x) y) =
  let inner : Deriv (eqF (ap2 Pair (ap1 devF (code x)) (ap1 devF (code y)))
                         (ap2 Pair (code (dev x)) (code (dev y))))
      inner = ruleTrans (congL Pair (ap1 devF (code y)) (devF_code x))
                        (congR Pair (code (dev x)) (devF_code y))
  in ruleTrans (dev_at_adSu (code x) (code y))
               (congR Pair tagSu (congR Pair tagAd inner))

-- dev (ad (ad p q) y) = ad (dev (ad p q)) (dev y) .
devF_code (ad (ad p q) y) =
  let inner : Deriv (eqF (ap2 Pair (ap1 devF (code (ad p q))) (ap1 devF (code y)))
                         (ap2 Pair (code (dev (ad p q))) (code (dev y))))
      inner = ruleTrans (congL Pair (ap1 devF (code y)) (devF_code (ad p q)))
                        (congR Pair (code (dev (ad p q))) (devF_code y))
  in ruleTrans (dev_at_adAd (code p) (code q) (code y))
               (congR Pair tagAd inner)
