{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.TriFEnds -- the ENDPOINT preservation of the triangle transformer triF,
-- the sibling of T4.TriFPres (validity).  Structure-carrying: ONE structural
-- induction on the cert tree  c : CertM .
--
-- The triangle maps a cert d for Par(t,u) to a cert for Par(u, dev t), so its
-- SOURCE is the original TARGET:
--
--   src_triF : (c : CertM) -> src (triF (codeC c)) = tgt (codeC c)
--
-- proved here for ALL cases (mZe/mSu/mRO/mRS + the mAd dispatch over the first
-- child's five shapes), chaining triF's closure equations (T4.TriF.tri_at_*)
-- with src/tgt's defining equations (T4.ParEnds).  Same shape as TriFPres.
--
-- (The dual  tgt_triF : tgt (triF (codeC c)) = code (dev t)  is the
-- development-target side; see the SCOPE NOTE at the bottom.)
--
-- No holes, no postulates; --safe --without-K --exact-split.

module T4.TriFEnds where

open import T4.Base

open import T4.CertTree using ( CertM ; mZe ; mSu ; mAd ; mRO ; mRS ; codeC )
open import T4.ParCert  using ( cZe ; cSu ; cAd ; cRO ; cRS )
open import T4.TriF     using
  ( triF
  ; tri_at_cZe ; tri_at_cSu ; tri_at_cRO ; tri_at_cRS
  ; tri_at_cAd_cZe ; tri_at_cAd_cSu ; tri_at_cAd_cAd ; tri_at_cAd_cRO ; tri_at_cAd_cRS )
open import T4.ParEnds  using
  ( src ; tgt
  ; src_cZe ; src_cSu ; src_cAd ; src_cRO ; src_cRS
  ; tgt_cZe ; tgt_cSu ; tgt_cAd ; tgt_cRO ; tgt_cRS )
open import T4.TrsCodeObj using ( ze# ; su# ; ad# ; tagSu ; tagAd )
open import T4.DevF using
  ( devF ; dev_at_ze ; dev_at_su ; dev_at_adZe ; dev_at_adSu ; dev_at_adAd )

------------------------------------------------------------------------
-- Constructor congruences (su# / ad# are Pair-with-tag, so congL/congR Pair).

suCong : (a b : Term) -> Deriv (eqF a b) -> Deriv (eqF (su# a) (su# b))
suCong a b e = congR Pair tagSu e

adCong : (a a' b b' : Term) ->
  Deriv (eqF a a') -> Deriv (eqF b b') -> Deriv (eqF (ad# a b) (ad# a' b'))
adCong a a' b b' ea eb =
  congR Pair tagAd (ruleTrans (congL Pair b ea) (congR Pair a' eb))

------------------------------------------------------------------------
-- src (triF (codeC c)) = tgt (codeC c)  --  by structural induction on c.

src_triF : (c : CertM) ->
  Deriv (eqF (ap1 src (ap1 triF (codeC c))) (ap1 tgt (codeC c)))

-- cZe :  triF cZe = cZe ; src cZe = ze# = tgt cZe .
src_triF mZe =
  ruleTrans (cong1 src tri_at_cZe)
    (ruleTrans src_cZe (ruleSym tgt_cZe))

-- cSu :  triF (cSu d) = cSu (triF d) ; src (cSu _) = su# (src _) ; tgt (cSu d)=su#(tgt d).
src_triF (mSu c) =
  let d = codeC c in
  ruleTrans (cong1 src (tri_at_cSu d))
    (ruleTrans (src_cSu (ap1 triF d))
      (ruleTrans (suCong (ap1 src (ap1 triF d)) (ap1 tgt d) (src_triF c))
        (ruleSym (tgt_cSu d))))

-- cRO :  triF (cRO d) = triF d ; tgt (cRO d) = tgt d .
src_triF (mRO c) =
  let d = codeC c in
  ruleTrans (cong1 src (tri_at_cRO d))
    (ruleTrans (src_triF c) (ruleSym (tgt_cRO d)))

-- cRS :  triF (cRS d1 d2) = cSu (cAd (triF d1)(triF d2)) ;
--        tgt (cRS d1 d2) = su# (ad# (tgt d1)(tgt d2)) .
src_triF (mRS c1 c2) =
  let d1 = codeC c1 ; d2 = codeC c2
      inner : Deriv (eqF (ap1 src (cAd (ap1 triF d1) (ap1 triF d2)))
                         (ad# (ap1 tgt d1) (ap1 tgt d2)))
      inner = ruleTrans (src_cAd (ap1 triF d1) (ap1 triF d2))
                (adCong (ap1 src (ap1 triF d1)) (ap1 tgt d1)
                        (ap1 src (ap1 triF d2)) (ap1 tgt d2)
                        (src_triF c1) (src_triF c2))
  in ruleTrans (cong1 src (tri_at_cRS d1 d2))
       (ruleTrans (src_cSu (cAd (ap1 triF d1) (ap1 triF d2)))
         (ruleTrans (suCong (ap1 src (cAd (ap1 triF d1) (ap1 triF d2)))
                            (ad# (ap1 tgt d1) (ap1 tgt d2)) inner)
           (ruleSym (tgt_cRS d1 d2))))

-- cAd cZe d2 :  triF = cRO (triF d2) ; src (cRO _)=ad# ze# (src _) ;
--               tgt (cAd cZe d2)=ad#(tgt cZe)(tgt d2)=ad# ze#(tgt d2).
src_triF (mAd mZe c2) =
  let d2 = codeC c2
      tgtside : Deriv (eqF (ad# ze# (ap1 tgt d2)) (ap1 tgt (cAd cZe d2)))
      tgtside = ruleSym (ruleTrans (tgt_cAd cZe d2)
                  (adCong (ap1 tgt cZe) ze# (ap1 tgt d2) (ap1 tgt d2)
                          tgt_cZe (axRefl (ap1 tgt d2))))
  in ruleTrans (cong1 src (tri_at_cAd_cZe d2))
       (ruleTrans (src_cRO (ap1 triF d2))
         (ruleTrans (adCong ze# ze# (ap1 src (ap1 triF d2)) (ap1 tgt d2)
                            (axRefl ze#) (src_triF c2))
           tgtside))

-- cAd (cSu d1') d2 :  triF = cRS (triF d1')(triF d2) ;
--    src (cRS _ _)=ad#(su#(src _))(src _) ; tgt(cAd(cSu d1')d2)=ad#(su#(tgt d1'))(tgt d2).
src_triF (mAd (mSu c1') c2) =
  let d1' = codeC c1' ; d2 = codeC c2
      tgtside : Deriv (eqF (ad# (su# (ap1 tgt d1')) (ap1 tgt d2))
                           (ap1 tgt (cAd (cSu d1') d2)))
      tgtside = ruleSym (ruleTrans (tgt_cAd (cSu d1') d2)
                  (adCong (ap1 tgt (cSu d1')) (su# (ap1 tgt d1')) (ap1 tgt d2) (ap1 tgt d2)
                          (tgt_cSu d1') (axRefl (ap1 tgt d2))))
  in ruleTrans (cong1 src (tri_at_cAd_cSu d1' d2))
       (ruleTrans (src_cRS (ap1 triF d1') (ap1 triF d2))
         (ruleTrans (adCong (su# (ap1 src (ap1 triF d1'))) (su# (ap1 tgt d1'))
                            (ap1 src (ap1 triF d2)) (ap1 tgt d2)
                            (suCong (ap1 src (ap1 triF d1')) (ap1 tgt d1') (src_triF c1'))
                            (src_triF c2))
           tgtside))

-- cAd (cAd d1a d1b) d2 :  triF = cAd (triF (cAd d1a d1b)) (triF d2) ;
--    tgt (cAd (cAd ..) d2) = ad# (tgt (cAd ..)) (tgt d2) .
src_triF (mAd (mAd c1a c1b) c2) =
  let d1a = codeC c1a ; d1b = codeC c1b ; d2 = codeC c2
  in ruleTrans (cong1 src (tri_at_cAd_cAd d1a d1b d2))
       (ruleTrans (src_cAd (ap1 triF (cAd d1a d1b)) (ap1 triF d2))
         (ruleTrans (adCong (ap1 src (ap1 triF (cAd d1a d1b))) (ap1 tgt (cAd d1a d1b))
                            (ap1 src (ap1 triF d2)) (ap1 tgt d2)
                            (src_triF (mAd c1a c1b)) (src_triF c2))
           (ruleSym (tgt_cAd (cAd d1a d1b) d2))))

-- cAd (cRO d1') d2 :  triF = cAd (triF (cRO d1')) (triF d2) .
src_triF (mAd (mRO c1') c2) =
  let d1' = codeC c1' ; d2 = codeC c2
  in ruleTrans (cong1 src (tri_at_cAd_cRO d1' d2))
       (ruleTrans (src_cAd (ap1 triF (cRO d1')) (ap1 triF d2))
         (ruleTrans (adCong (ap1 src (ap1 triF (cRO d1'))) (ap1 tgt (cRO d1'))
                            (ap1 src (ap1 triF d2)) (ap1 tgt d2)
                            (src_triF (mRO c1')) (src_triF c2))
           (ruleSym (tgt_cAd (cRO d1') d2))))

-- cAd (cRS d1a d1b) d2 :  triF = cAd (triF (cRS d1a d1b)) (triF d2) .
src_triF (mAd (mRS c1a c1b) c2) =
  let d1a = codeC c1a ; d1b = codeC c1b ; d2 = codeC c2
  in ruleTrans (cong1 src (tri_at_cAd_cRS d1a d1b d2))
       (ruleTrans (src_cAd (ap1 triF (cRS d1a d1b)) (ap1 triF d2))
         (ruleTrans (adCong (ap1 src (ap1 triF (cRS d1a d1b))) (ap1 tgt (cRS d1a d1b))
                            (ap1 src (ap1 triF d2)) (ap1 tgt d2)
                            (src_triF (mRS c1a c1b)) (src_triF c2))
           (ruleSym (tgt_cAd (cRS d1a d1b) d2))))

------------------------------------------------------------------------
-- tgt (triF (codeC c)) = devF (src (codeC c))  --  the development-target
-- side of the triangle (Par(t,u) -> Par(u, dev t); tgt = code (dev t) =
-- devF (code t) = devF (src d)).  triF's cAd dispatch mirrors devF's ad
-- dispatch (dev_at_adZe / _adSu / _adAd), which is exactly why this holds.

-- Helper for the three ad#-headed-first-child cAd cases (cAd/cRO/cRS), where
-- devF uses dev_at_adAd:  given src(fc) = ad# P Q  and the IHs.
cAdAdCase : (fc d2 P Q : Term) ->
  Deriv (eqF (ap1 triF (cAd fc d2)) (cAd (ap1 triF fc) (ap1 triF d2))) ->
  Deriv (eqF (ap1 src fc) (ad# P Q)) ->
  Deriv (eqF (ap1 tgt (ap1 triF fc)) (ap1 devF (ap1 src fc))) ->
  Deriv (eqF (ap1 tgt (ap1 triF d2)) (ap1 devF (ap1 src d2))) ->
  Deriv (eqF (ap1 tgt (ap1 triF (cAd fc d2))) (ap1 devF (ap1 src (cAd fc d2))))
cAdAdCase fc d2 P Q triClo srcFc ihFc ihD2 =
  let devFsrcCAd : Deriv (eqF (ap1 devF (ap1 src (cAd fc d2)))
                              (ad# (ap1 devF (ap1 src fc)) (ap1 devF (ap1 src d2))))
      devFsrcCAd =
        ruleTrans (cong1 devF (src_cAd fc d2))
          (ruleTrans (cong1 devF (adCong (ap1 src fc) (ad# P Q) (ap1 src d2) (ap1 src d2)
                                         srcFc (axRefl (ap1 src d2))))
            (ruleTrans (dev_at_adAd P Q (ap1 src d2))
              (adCong (ap1 devF (ad# P Q)) (ap1 devF (ap1 src fc))
                      (ap1 devF (ap1 src d2)) (ap1 devF (ap1 src d2))
                      (cong1 devF (ruleSym srcFc)) (axRefl (ap1 devF (ap1 src d2))))))
  in ruleTrans (cong1 tgt triClo)
       (ruleTrans (tgt_cAd (ap1 triF fc) (ap1 triF d2))
         (ruleTrans (adCong (ap1 tgt (ap1 triF fc)) (ap1 devF (ap1 src fc))
                            (ap1 tgt (ap1 triF d2)) (ap1 devF (ap1 src d2)) ihFc ihD2)
           (ruleSym devFsrcCAd)))

tgt_triF : (c : CertM) ->
  Deriv (eqF (ap1 tgt (ap1 triF (codeC c))) (ap1 devF (ap1 src (codeC c))))

-- cZe :  tgt cZe = ze# ; devF (src cZe) = devF ze# = ze# .
tgt_triF mZe =
  ruleTrans (ruleTrans (cong1 tgt tri_at_cZe) tgt_cZe)
    (ruleSym (ruleTrans (cong1 devF src_cZe) dev_at_ze))

-- cSu :  tgt (cSu _) = su# (tgt _) ; devF (su# _) = su# (devF _) .
tgt_triF (mSu c) =
  let d = codeC c in
  ruleTrans (cong1 tgt (tri_at_cSu d))
    (ruleTrans (tgt_cSu (ap1 triF d))
      (ruleTrans (suCong (ap1 tgt (ap1 triF d)) (ap1 devF (ap1 src d)) (tgt_triF c))
        (ruleSym (ruleTrans (cong1 devF (src_cSu d)) (dev_at_su (ap1 src d))))))

-- cRO :  triF (cRO d) = triF d ; devF (src (cRO d)) = devF (ad# ze# (src d)) = devF (src d) .
tgt_triF (mRO c) =
  let d = codeC c in
  ruleTrans (cong1 tgt (tri_at_cRO d))
    (ruleTrans (tgt_triF c)
      (ruleSym (ruleTrans (cong1 devF (src_cRO d)) (dev_at_adZe (ap1 src d)))))

-- cRS :  triF = cSu (cAd ..) ; devF (src (cRS d1 d2)) = devF (ad#(su#(src d1))(src d2))
--        = su# (ad# (devF (src d1))(devF (src d2)))  by dev_at_adSu .
tgt_triF (mRS c1 c2) =
  let d1 = codeC c1 ; d2 = codeC c2
      midRS : Deriv (eqF (ap1 tgt (cAd (ap1 triF d1) (ap1 triF d2)))
                         (ad# (ap1 devF (ap1 src d1)) (ap1 devF (ap1 src d2))))
      midRS = ruleTrans (tgt_cAd (ap1 triF d1) (ap1 triF d2))
                (adCong (ap1 tgt (ap1 triF d1)) (ap1 devF (ap1 src d1))
                        (ap1 tgt (ap1 triF d2)) (ap1 devF (ap1 src d2))
                        (tgt_triF c1) (tgt_triF c2))
      rhsRS : Deriv (eqF (su# (ad# (ap1 devF (ap1 src d1)) (ap1 devF (ap1 src d2))))
                         (ap1 devF (ap1 src (cRS d1 d2))))
      rhsRS = ruleSym (ruleTrans (cong1 devF (src_cRS d1 d2))
                (dev_at_adSu (ap1 src d1) (ap1 src d2)))
  in ruleTrans (cong1 tgt (tri_at_cRS d1 d2))
       (ruleTrans (tgt_cSu (cAd (ap1 triF d1) (ap1 triF d2)))
         (ruleTrans (suCong (ap1 tgt (cAd (ap1 triF d1) (ap1 triF d2)))
                            (ad# (ap1 devF (ap1 src d1)) (ap1 devF (ap1 src d2))) midRS)
           rhsRS))

-- cAd cZe d2 :  triF = cRO (triF d2) ; devF (src (cAd cZe d2)) = devF (ad# ze# (src d2))
--              = devF (src d2)  by dev_at_adZe .
tgt_triF (mAd mZe c2) =
  let d2 = codeC c2
      rhsZe : Deriv (eqF (ap1 devF (ap1 src d2)) (ap1 devF (ap1 src (cAd cZe d2))))
      rhsZe = ruleSym (ruleTrans (cong1 devF (src_cAd cZe d2))
                (ruleTrans (cong1 devF (adCong (ap1 src cZe) ze# (ap1 src d2) (ap1 src d2)
                                               src_cZe (axRefl (ap1 src d2))))
                  (dev_at_adZe (ap1 src d2))))
  in ruleTrans (cong1 tgt (tri_at_cAd_cZe d2))
       (ruleTrans (tgt_cRO (ap1 triF d2))
         (ruleTrans (tgt_triF c2) rhsZe))

-- cAd (cSu d1') d2 :  triF = cRS .. ; devF (src ..) = devF (ad#(su#(src d1'))(src d2))
--                    = su#(ad#(devF(src d1'))(devF(src d2)))  by dev_at_adSu .
tgt_triF (mAd (mSu c1') c2) =
  let d1' = codeC c1' ; d2 = codeC c2
      midSu : Deriv (eqF (ap1 tgt (cRS (ap1 triF d1') (ap1 triF d2)))
                         (su# (ad# (ap1 devF (ap1 src d1')) (ap1 devF (ap1 src d2)))))
      midSu = ruleTrans (tgt_cRS (ap1 triF d1') (ap1 triF d2))
                (suCong (ad# (ap1 tgt (ap1 triF d1')) (ap1 tgt (ap1 triF d2)))
                        (ad# (ap1 devF (ap1 src d1')) (ap1 devF (ap1 src d2)))
                        (adCong (ap1 tgt (ap1 triF d1')) (ap1 devF (ap1 src d1'))
                                (ap1 tgt (ap1 triF d2)) (ap1 devF (ap1 src d2))
                                (tgt_triF c1') (tgt_triF c2)))
      rhsSu : Deriv (eqF (su# (ad# (ap1 devF (ap1 src d1')) (ap1 devF (ap1 src d2))))
                         (ap1 devF (ap1 src (cAd (cSu d1') d2))))
      rhsSu = ruleSym (ruleTrans (cong1 devF (src_cAd (cSu d1') d2))
                (ruleTrans (cong1 devF (adCong (ap1 src (cSu d1')) (su# (ap1 src d1'))
                                               (ap1 src d2) (ap1 src d2)
                                               (src_cSu d1') (axRefl (ap1 src d2))))
                  (dev_at_adSu (ap1 src d1') (ap1 src d2))))
  in ruleTrans (cong1 tgt (tri_at_cAd_cSu d1' d2)) (ruleTrans midSu rhsSu)

-- cAd (cAd ..) d2 / cAd (cRO ..) d2 / cAd (cRS ..) d2 : ad#-headed first child -> dev_at_adAd.
tgt_triF (mAd (mAd c1a c1b) c2) =
  cAdAdCase (cAd (codeC c1a) (codeC c1b)) (codeC c2) (ap1 src (codeC c1a)) (ap1 src (codeC c1b))
    (tri_at_cAd_cAd (codeC c1a) (codeC c1b) (codeC c2))
    (src_cAd (codeC c1a) (codeC c1b))
    (tgt_triF (mAd c1a c1b)) (tgt_triF c2)

tgt_triF (mAd (mRO c1') c2) =
  cAdAdCase (cRO (codeC c1')) (codeC c2) ze# (ap1 src (codeC c1'))
    (tri_at_cAd_cRO (codeC c1') (codeC c2))
    (src_cRO (codeC c1'))
    (tgt_triF (mRO c1')) (tgt_triF c2)

tgt_triF (mAd (mRS c1a c1b) c2) =
  cAdAdCase (cRS (codeC c1a) (codeC c1b)) (codeC c2)
    (su# (ap1 src (codeC c1a))) (ap1 src (codeC c1b))
    (tri_at_cAd_cRS (codeC c1a) (codeC c1b) (codeC c2))
    (src_cRS (codeC c1a) (codeC c1b))
    (tgt_triF (mRS c1a c1b)) (tgt_triF c2)
