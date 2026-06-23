{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.DerTriPres -- Theorem A (the triangle), ENDPOINT EQUATIONS, internalised
-- and proved STRUCTURE-CARRYING by induction on the derivation shadow DerM,
-- chaining the object fold equations of srcF / tgtF / triF (and devF, next).
-- This is the object analog of T4.ObjCR.triPresObj, on the clean DerCode coding.
--
--   src_tri : srcF (triF (codeDer d)) = tgtF (codeDer d)
--             ( "the source of the triangle of d is the target of d" )
--
-- proved by ONE meta induction on  d : DerM , each case a chain of the already-
-- green fold equations + congruences (mirrors ObjCR.triPresObj clause-for-clause,
-- incl the depth-2 pAd critical pairs).  Every conclusion is an object  Deriv .
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.DerTriPres where

open import T4.Base

open import T4.DerCode
  using ( DerM ; mZe ; mSu ; mAd ; mRO ; mRS ; codeDer
        ; derZe ; derSu ; derAd ; derRO ; derRS )
open import T4.DerSrc
  using ( srcF ; srcF_derZe ; srcF_derSu ; srcF_derAd ; srcF_derRO ; srcF_derRS )
open import T4.DerTgt
  using ( tgtF ; tgtF_derZe ; tgtF_derSu ; tgtF_derAd ; tgtF_derRO ; tgtF_derRS )
open import T4.DerTri
  using ( triF ; triF_derZe ; triF_derSu ; triF_derRO ; triF_derRS )
open import T4.DerTri2
  using ( triF_derAd_Ze ; triF_derAd_Su ; triF_derAd_Ad ; triF_derAd_RO ; triF_derAd_RS )
open import T4.DerDev
  using ( devF ; devF_ze# ; devF_su# ; devF_ad_ze ; devF_ad_su ; devF_ad_ad )
open import T4.TrsCodeObj using ( ze# ; su# ; ad# ; tagSu ; tagAd )

open import BRA3.Church using ( pi )

------------------------------------------------------------------------
-- Theorem A, source endpoint:  srcF (triF (codeDer d)) = tgtF (codeDer d) .

src_tri : (d : DerM) ->
  Deriv (eqF (ap1 srcF (ap1 triF (codeDer d))) (ap1 tgtF (codeDer d)))

src_tri mZe =
  ruleTrans (cong1 srcF triF_derZe)
    (ruleTrans srcF_derZe (ruleSym tgtF_derZe))

src_tri (mSu p) =
  let cp = codeDer p in
  ruleTrans (cong1 srcF (triF_derSu cp))
    (ruleTrans (srcF_derSu (ap1 triF cp))
      (ruleTrans (congR pi tagSu (src_tri p))
                 (ruleSym (tgtF_derSu cp))))

src_tri (mRO p) =
  let cp = codeDer p in
  ruleTrans (cong1 srcF (triF_derRO cp))
    (ruleTrans (src_tri p) (ruleSym (tgtF_derRO cp)))

src_tri (mRS p q) =
  let cp = codeDer p ; cq = codeDer q in
  ruleTrans (cong1 srcF (triF_derRS cp cq))
    (ruleTrans (srcF_derSu (derAd (ap1 triF cp) (ap1 triF cq)))
      (ruleTrans (congR pi tagSu (srcF_derAd (ap1 triF cp) (ap1 triF cq)))
        (ruleTrans (congR pi tagSu (congR pi tagAd
                     (ruleTrans (congL pi (ap1 srcF (ap1 triF cq)) (src_tri p))
                                (congR pi (ap1 tgtF cp) (src_tri q)))))
          (ruleSym (tgtF_derRS cp cq)))))

-- pAd critical pairs:

src_tri (mAd mZe q) =
  let cq = codeDer q
      tgt_side : Deriv (eqF (ap1 tgtF (derAd derZe cq)) (ad# ze# (ap1 tgtF cq)))
      tgt_side = ruleTrans (tgtF_derAd derZe cq)
                   (congR pi tagAd (congL pi (ap1 tgtF cq) tgtF_derZe))
  in ruleTrans (cong1 srcF (triF_derAd_Ze cq))
       (ruleTrans (srcF_derRO (ap1 triF cq))
         (ruleTrans (congR pi tagAd (congR pi ze# (src_tri q)))
                    (ruleSym tgt_side)))

src_tri (mAd (mSu p) q) =
  let cp = codeDer p ; cq = codeDer q
      tgt_side : Deriv (eqF (ap1 tgtF (derAd (derSu cp) cq))
                            (ad# (su# (ap1 tgtF cp)) (ap1 tgtF cq)))
      tgt_side = ruleTrans (tgtF_derAd (derSu cp) cq)
                   (congR pi tagAd (congL pi (ap1 tgtF cq) (tgtF_derSu cp)))
  in ruleTrans (cong1 srcF (triF_derAd_Su cp cq))
       (ruleTrans (srcF_derRS (ap1 triF cp) (ap1 triF cq))
         (ruleTrans (congR pi tagAd
                      (ruleTrans (congL pi (ap1 srcF (ap1 triF cq))
                                    (congR pi tagSu (src_tri p)))
                                 (congR pi (su# (ap1 tgtF cp)) (src_tri q))))
           (ruleSym tgt_side)))

src_tri (mAd (mAd p1 p2) q) =
  let a = derAd (codeDer p1) (codeDer p2) ; cq = codeDer q in
  ruleTrans (cong1 srcF (triF_derAd_Ad (codeDer p1) (codeDer p2) cq))
    (ruleTrans (srcF_derAd (ap1 triF a) (ap1 triF cq))
      (ruleTrans (congR pi tagAd
                   (ruleTrans (congL pi (ap1 srcF (ap1 triF cq)) (src_tri (mAd p1 p2)))
                              (congR pi (ap1 tgtF a) (src_tri q))))
        (ruleSym (tgtF_derAd a cq))))

src_tri (mAd (mRO p) q) =
  let a = derRO (codeDer p) ; cq = codeDer q in
  ruleTrans (cong1 srcF (triF_derAd_RO (codeDer p) cq))
    (ruleTrans (srcF_derAd (ap1 triF a) (ap1 triF cq))
      (ruleTrans (congR pi tagAd
                   (ruleTrans (congL pi (ap1 srcF (ap1 triF cq)) (src_tri (mRO p)))
                              (congR pi (ap1 tgtF a) (src_tri q))))
        (ruleSym (tgtF_derAd a cq))))

src_tri (mAd (mRS p1 p2) q) =
  let a = derRS (codeDer p1) (codeDer p2) ; cq = codeDer q in
  ruleTrans (cong1 srcF (triF_derAd_RS (codeDer p1) (codeDer p2) cq))
    (ruleTrans (srcF_derAd (ap1 triF a) (ap1 triF cq))
      (ruleTrans (congR pi tagAd
                   (ruleTrans (congL pi (ap1 srcF (ap1 triF cq)) (src_tri (mRS p1 p2)))
                              (congR pi (ap1 tgtF a) (src_tri q))))
        (ruleSym (tgtF_derAd a cq))))

------------------------------------------------------------------------
-- Theorem A, target endpoint:  tgtF (triF (codeDer d)) = devF (srcF (codeDer d)) .
-- ( "the target of the triangle of d is the development of the source of d" )
-- Same meta induction; the RHS develops the source via devF.

tgt_tri : (d : DerM) ->
  Deriv (eqF (ap1 tgtF (ap1 triF (codeDer d))) (ap1 devF (ap1 srcF (codeDer d))))

tgt_tri mZe =
  ruleTrans (cong1 tgtF triF_derZe)
    (ruleTrans tgtF_derZe
      (ruleSym (ruleTrans (cong1 devF srcF_derZe) devF_ze#)))

tgt_tri (mSu p) =
  let cp = codeDer p in
  ruleTrans (cong1 tgtF (triF_derSu cp))
    (ruleTrans (tgtF_derSu (ap1 triF cp))
      (ruleTrans (congR pi tagSu (tgt_tri p))
        (ruleSym (ruleTrans (cong1 devF (srcF_derSu cp)) (devF_su# (ap1 srcF cp))))))

tgt_tri (mRO p) =
  let cp = codeDer p in
  ruleTrans (cong1 tgtF (triF_derRO cp))
    (ruleTrans (tgt_tri p)
      (ruleSym (ruleTrans (cong1 devF (srcF_derRO cp)) (devF_ad_ze (ap1 srcF cp)))))

tgt_tri (mRS p q) =
  let cp = codeDer p ; cq = codeDer q in
  ruleTrans (cong1 tgtF (triF_derRS cp cq))
    (ruleTrans (tgtF_derSu (derAd (ap1 triF cp) (ap1 triF cq)))
      (ruleTrans (congR pi tagSu (tgtF_derAd (ap1 triF cp) (ap1 triF cq)))
        (ruleTrans (congR pi tagSu (congR pi tagAd
                     (ruleTrans (congL pi (ap1 tgtF (ap1 triF cq)) (tgt_tri p))
                                (congR pi (ap1 devF (ap1 srcF cp)) (tgt_tri q)))))
          (ruleSym (ruleTrans (cong1 devF (srcF_derRS cp cq))
                              (devF_ad_su (ap1 srcF cp) (ap1 srcF cq)))))))

tgt_tri (mAd mZe q) =
  let cq = codeDer q in
  ruleTrans (cong1 tgtF (triF_derAd_Ze cq))
    (ruleTrans (tgtF_derRO (ap1 triF cq))
      (ruleTrans (tgt_tri q)
        (ruleSym (ruleTrans (cong1 devF (srcF_derAd derZe cq))
          (ruleTrans (cong1 devF (congR pi tagAd (congL pi (ap1 srcF cq) srcF_derZe)))
                     (devF_ad_ze (ap1 srcF cq)))))))

tgt_tri (mAd (mSu p) q) =
  let cp = codeDer p ; cq = codeDer q in
  ruleTrans (cong1 tgtF (triF_derAd_Su cp cq))
    (ruleTrans (tgtF_derRS (ap1 triF cp) (ap1 triF cq))
      (ruleTrans (congR pi tagSu (congR pi tagAd
                   (ruleTrans (congL pi (ap1 tgtF (ap1 triF cq)) (tgt_tri p))
                              (congR pi (ap1 devF (ap1 srcF cp)) (tgt_tri q)))))
        (ruleSym (ruleTrans (cong1 devF (srcF_derAd (derSu cp) cq))
          (ruleTrans (cong1 devF (congR pi tagAd (congL pi (ap1 srcF cq) (srcF_derSu cp))))
                     (devF_ad_su (ap1 srcF cp) (ap1 srcF cq)))))))

-- shared development of  srcF (derAd a cq)  where  srcF a = ad# P Q  (else cases):
--   devF (srcF (derAd a cq)) = ad# (devF (srcF a)) (devF (srcF cq)) .
tgt_tri (mAd (mAd p1 p2) q) =
  let cp1 = codeDer p1 ; cp2 = codeDer p2 ; cq = codeDer q
      a = derAd cp1 cp2
      srcA : Deriv (eqF (ap1 srcF a) (ad# (ap1 srcF cp1) (ap1 srcF cp2)))
      srcA = srcF_derAd cp1 cp2
      rhs : Deriv (eqF (ap1 devF (ap1 srcF (derAd a cq)))
                       (ad# (ap1 devF (ap1 srcF a)) (ap1 devF (ap1 srcF cq))))
      rhs = ruleTrans (cong1 devF (srcF_derAd a cq))
              (ruleTrans (cong1 devF (congR pi tagAd (congL pi (ap1 srcF cq) srcA)))
                (ruleTrans (devF_ad_ad (ap1 srcF cp1) (ap1 srcF cp2) (ap1 srcF cq))
                  (congR pi tagAd (congL pi (ap1 devF (ap1 srcF cq))
                     (cong1 devF (ruleSym srcA))))))
  in ruleTrans (cong1 tgtF (triF_derAd_Ad cp1 cp2 cq))
       (ruleTrans (tgtF_derAd (ap1 triF a) (ap1 triF cq))
         (ruleTrans (congR pi tagAd
                      (ruleTrans (congL pi (ap1 tgtF (ap1 triF cq)) (tgt_tri (mAd p1 p2)))
                                 (congR pi (ap1 devF (ap1 srcF a)) (tgt_tri q))))
           (ruleSym rhs)))

tgt_tri (mAd (mRO p) q) =
  let cp = codeDer p ; cq = codeDer q
      a = derRO cp
      srcA : Deriv (eqF (ap1 srcF a) (ad# ze# (ap1 srcF cp)))
      srcA = srcF_derRO cp
      rhs : Deriv (eqF (ap1 devF (ap1 srcF (derAd a cq)))
                       (ad# (ap1 devF (ap1 srcF a)) (ap1 devF (ap1 srcF cq))))
      rhs = ruleTrans (cong1 devF (srcF_derAd a cq))
              (ruleTrans (cong1 devF (congR pi tagAd (congL pi (ap1 srcF cq) srcA)))
                (ruleTrans (devF_ad_ad ze# (ap1 srcF cp) (ap1 srcF cq))
                  (congR pi tagAd (congL pi (ap1 devF (ap1 srcF cq))
                     (cong1 devF (ruleSym srcA))))))
  in ruleTrans (cong1 tgtF (triF_derAd_RO cp cq))
       (ruleTrans (tgtF_derAd (ap1 triF a) (ap1 triF cq))
         (ruleTrans (congR pi tagAd
                      (ruleTrans (congL pi (ap1 tgtF (ap1 triF cq)) (tgt_tri (mRO p)))
                                 (congR pi (ap1 devF (ap1 srcF a)) (tgt_tri q))))
           (ruleSym rhs)))

tgt_tri (mAd (mRS p1 p2) q) =
  let cp1 = codeDer p1 ; cp2 = codeDer p2 ; cq = codeDer q
      a = derRS cp1 cp2
      srcA : Deriv (eqF (ap1 srcF a) (ad# (su# (ap1 srcF cp1)) (ap1 srcF cp2)))
      srcA = srcF_derRS cp1 cp2
      rhs : Deriv (eqF (ap1 devF (ap1 srcF (derAd a cq)))
                       (ad# (ap1 devF (ap1 srcF a)) (ap1 devF (ap1 srcF cq))))
      rhs = ruleTrans (cong1 devF (srcF_derAd a cq))
              (ruleTrans (cong1 devF (congR pi tagAd (congL pi (ap1 srcF cq) srcA)))
                (ruleTrans (devF_ad_ad (su# (ap1 srcF cp1)) (ap1 srcF cp2) (ap1 srcF cq))
                  (congR pi tagAd (congL pi (ap1 devF (ap1 srcF cq))
                     (cong1 devF (ruleSym srcA))))))
  in ruleTrans (cong1 tgtF (triF_derAd_RS cp1 cp2 cq))
       (ruleTrans (tgtF_derAd (ap1 triF a) (ap1 triF cq))
         (ruleTrans (congR pi tagAd
                      (ruleTrans (congL pi (ap1 tgtF (ap1 triF cq)) (tgt_tri (mRS p1 p2)))
                                 (congR pi (ap1 devF (ap1 srcF a)) (tgt_tri q))))
           (ruleSym rhs)))
