{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.TriFPres -- the DIAMOND brick: the triangle transformer triF preserves
-- certificate VALIDITY.  This is the preservation lemma that STALLED in
-- attempt3 §14 (over an opaque cert it needed object structural induction
-- that did not exist).  Done here by the STRUCTURE-CARRYING method: a cert is
-- a meta tree  c : CertM  (T4.CertTree), embedded by  codeC , and the
-- preservation is ONE structural induction on  c  chaining triF's closure
-- equations (T4.TriF) with isCert's defining equations (T4.ParEnds):
--
--   isCert_triF_M : (c : CertM) -> Deriv (eqF (ap1 isCert (ap1 triF (codeC c))) O)
--
-- i.e. triF maps a (built) valid cert to a valid cert.  Mirrors
-- T4.CertTree.isCertC; the only subtlety is the  mAd  case, which dispatches
-- on the FIRST child's top constructor exactly as triF's own  cAd  clause does
-- (tri_at_cAd_cZe / _cSu / _cAd / _cRO / _cRS).
--
-- SCOPE NOTE (for the parent).  This is the version over cert codes carried
-- WITH their meta shadow (built / codeC-form), which is what the confluence
-- combinatorics actually produce (certs are BUILT by parSuC/parAdC/certOf,
-- never bare opaque E-witnesses).  The fully-OPAQUE form
--   (d : Term) -> isCert d = O -> isCert (triF d) = O
-- is NOT delivered: descSnd discharges the recursion DESCENT, but the step
-- still needs to DISPATCH on the cert tag of an opaque d to reach triF's
-- per-constructor closure equations -- an OBJECT 5-way tag case-analysis that
-- (i) cannot be a meta case-split on an opaque term and (ii) is not provided
-- by the weak isCert (tag>=5 is validated as cRS, so isCert d = O gives no
-- object tag-disjunction).  That needs a tag-PINNING wf + an object inversion
-- (the T4.BinTreeWf strict-wf direction), independent of descSnd.  The
-- structure-carrying form below avoids it (the shadow supplies the tag).
--
-- No holes, no postulates; --safe --without-K --exact-split.

module T4.TriFPres where

open import T4.Base

open import T4.CertTree using ( CertM ; mZe ; mSu ; mAd ; mRO ; mRS ; codeC )
open import T4.ParCert  using ( cAd )
open import T4.TriF     using
  ( triF
  ; tri_at_cZe ; tri_at_cSu ; tri_at_cRO ; tri_at_cRS
  ; tri_at_cAd_cZe ; tri_at_cAd_cSu ; tri_at_cAd_cAd ; tri_at_cAd_cRO ; tri_at_cAd_cRS )
open import T4.ParEnds  using
  ( isCert
  ; isCert_cZe ; isCert_cSu ; isCert_cRO ; isCert_cAd ; isCert_cRS
  ; pi_O_O )

open import BRA3.Church using ( pi )

------------------------------------------------------------------------
-- A reusable combiner for the binary (cAd / cRS) cases:
--   from  isCert a = O  and  isCert b = O  conclude  pi (isCert a)(isCert b) = O .

piBothO : (a b : Term) ->
  Deriv (eqF (ap1 isCert a) O) -> Deriv (eqF (ap1 isCert b) O) ->
  Deriv (eqF (ap2 pi (ap1 isCert a) (ap1 isCert b)) O)
piBothO a b ea eb =
  ruleTrans (congL pi (ap1 isCert b) ea)
    (ruleTrans (congR pi O eb) pi_O_O)

------------------------------------------------------------------------
-- triF preserves validity, by structural induction on the cert tree.

isCert_triF_M : (c : CertM) -> Deriv (eqF (ap1 isCert (ap1 triF (codeC c))) O)

-- cZe :  triF cZe = cZe ,  isCert cZe = O .
isCert_triF_M mZe =
  ruleTrans (cong1 isCert tri_at_cZe) isCert_cZe

-- cSu :  triF (cSu d) = cSu (triF d) ,  isCert (cSu _) = isCert _ .
isCert_triF_M (mSu c) =
  ruleTrans (cong1 isCert (tri_at_cSu (codeC c)))
    (ruleTrans (isCert_cSu (ap1 triF (codeC c))) (isCert_triF_M c))

-- cRO :  triF (cRO d) = triF d .
isCert_triF_M (mRO c) =
  ruleTrans (cong1 isCert (tri_at_cRO (codeC c))) (isCert_triF_M c)

-- cRS :  triF (cRS d1 d2) = cSu (cAd (triF d1) (triF d2)) .
isCert_triF_M (mRS c1 c2) =
  ruleTrans (cong1 isCert (tri_at_cRS (codeC c1) (codeC c2)))
    (ruleTrans (isCert_cSu (cAd (ap1 triF (codeC c1)) (ap1 triF (codeC c2))))
      (ruleTrans (isCert_cAd (ap1 triF (codeC c1)) (ap1 triF (codeC c2)))
        (piBothO (ap1 triF (codeC c1)) (ap1 triF (codeC c2))
          (isCert_triF_M c1) (isCert_triF_M c2))))

-- cAd : dispatch on the FIRST child's top constructor (as triF's cAd clause).

--   cAd cZe d2 :  triF = cRO (triF d2) .
isCert_triF_M (mAd mZe c2) =
  ruleTrans (cong1 isCert (tri_at_cAd_cZe (codeC c2)))
    (ruleTrans (isCert_cRO (ap1 triF (codeC c2))) (isCert_triF_M c2))

--   cAd (cSu d1') d2 :  triF = cRS (triF d1') (triF d2) .
isCert_triF_M (mAd (mSu c1') c2) =
  ruleTrans (cong1 isCert (tri_at_cAd_cSu (codeC c1') (codeC c2)))
    (ruleTrans (isCert_cRS (ap1 triF (codeC c1')) (ap1 triF (codeC c2)))
      (piBothO (ap1 triF (codeC c1')) (ap1 triF (codeC c2))
        (isCert_triF_M c1') (isCert_triF_M c2)))

--   cAd (cAd ..) d2 :  triF = cAd (triF (cAd ..)) (triF d2) .
isCert_triF_M (mAd (mAd c1a c1b) c2) =
  ruleTrans (cong1 isCert (tri_at_cAd_cAd (codeC c1a) (codeC c1b) (codeC c2)))
    (ruleTrans (isCert_cAd (ap1 triF (codeC (mAd c1a c1b))) (ap1 triF (codeC c2)))
      (piBothO (ap1 triF (codeC (mAd c1a c1b))) (ap1 triF (codeC c2))
        (isCert_triF_M (mAd c1a c1b)) (isCert_triF_M c2)))

--   cAd (cRO ..) d2 :  triF = cAd (triF (cRO ..)) (triF d2) .
isCert_triF_M (mAd (mRO c1') c2) =
  ruleTrans (cong1 isCert (tri_at_cAd_cRO (codeC c1') (codeC c2)))
    (ruleTrans (isCert_cAd (ap1 triF (codeC (mRO c1'))) (ap1 triF (codeC c2)))
      (piBothO (ap1 triF (codeC (mRO c1'))) (ap1 triF (codeC c2))
        (isCert_triF_M (mRO c1')) (isCert_triF_M c2)))

--   cAd (cRS ..) d2 :  triF = cAd (triF (cRS ..)) (triF d2) .
isCert_triF_M (mAd (mRS c1a c1b) c2) =
  ruleTrans (cong1 isCert (tri_at_cAd_cRS (codeC c1a) (codeC c1b) (codeC c2)))
    (ruleTrans (isCert_cAd (ap1 triF (codeC (mRS c1a c1b))) (ap1 triF (codeC c2)))
      (piBothO (ap1 triF (codeC (mRS c1a c1b))) (ap1 triF (codeC c2))
        (isCert_triF_M (mRS c1a c1b)) (isCert_triF_M c2)))
