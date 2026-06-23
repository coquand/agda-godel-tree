{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.CertTree -- the §14 structural-induction method applied to the REAL
-- Church-Rosser CERTIFICATE type (T4.ParCert: cZe / cSu / cAd / cRO / cRS).
--
-- This is the concrete fix for the stall recorded in attempt3 §14 / the
-- internal-CR handoff: the OLD object  triF : Fun1  consumed a certificate
-- by recursion on an OPAQUE code, so its preservation lemmas (src / tgt /
-- isCert of the transformed cert) seemed to need an object structural
-- induction over an opaque cert code -- machinery that did not exist -- and
-- the weak  isCert  cascade did not even pin the constructor tag.
--
-- The clean fix (the BinTree library's lesson): CARRY THE CERT STRUCTURE at
-- the META level.  A certificate is a 5-constructor tree
--
--     data CertM = mZe | mSu CertM | mAd CertM CertM | mRO CertM | mRS CertM CertM
--
-- with  codeC : CertM -> Term  the embedding into the existing ParCert
-- constructors.  Then EVERY preservation lemma is ONE structural induction
-- on  CertM , chaining the per-constructor defining equations from
-- T4.ParEnds.  We deliver the two that mattered:
--
--     srcC    : (c : CertM) -> src (codeC c)    = srcM c     (endpoint preservation)
--     isCertC : (c : CertM) -> isCert (codeC c) = O          (VALIDITY preservation)
--
-- isCertC is the decisive one: a cert BUILT as  codeC c  for a known
-- c : CertM  is ALWAYS valid, by induction -- the opaque-cert / weak-isCert
-- problem disappears because the structure is carried, never inverted.
-- (tgt is identical to src; omitted to keep the file focused.)
--
-- No holes, no postulates, no termination warnings.

module T4.CertTree where

open import T4.Base

open import T4.ParCert    using ( cZe ; cSu ; cAd ; cRO ; cRS )
open import T4.ParEnds    using
  ( src ; isCert
  ; src_cZe ; src_cSu ; src_cAd ; src_cRO ; src_cRS
  ; isCert_cZe ; isCert_cSu ; isCert_cAd ; isCert_cRO ; isCert_cRS
  ; pi_O_O )
open import T4.TrsCodeObj using ( ze# ; su# ; ad# ; tagSu ; tagAd )

open import BRA3.Church   using ( pi )

------------------------------------------------------------------------
-- SECTION 1.  The meta certificate tree and its embedding.

data CertM : Set where
  mZe : CertM
  mSu : CertM -> CertM
  mAd : CertM -> CertM -> CertM
  mRO : CertM -> CertM
  mRS : CertM -> CertM -> CertM

codeC : CertM -> Term
codeC mZe         = cZe
codeC (mSu c)     = cSu (codeC c)
codeC (mAd c1 c2) = cAd (codeC c1) (codeC c2)
codeC (mRO c)     = cRO (codeC c)
codeC (mRS c1 c2) = cRS (codeC c1) (codeC c2)

-- the structural induction / recursion principle (Agda recursion).
certInd :
  (P : CertM -> Set) ->
  P mZe ->
  ((c : CertM) -> P c -> P (mSu c)) ->
  ((c1 c2 : CertM) -> P c1 -> P c2 -> P (mAd c1 c2)) ->
  ((c : CertM) -> P c -> P (mRO c)) ->
  ((c1 c2 : CertM) -> P c1 -> P c2 -> P (mRS c1 c2)) ->
  (c : CertM) -> P c
certInd P z su ad ro rs mZe         = z
certInd P z su ad ro rs (mSu c)     = su c (certInd P z su ad ro rs c)
certInd P z su ad ro rs (mAd c1 c2) =
  ad c1 c2 (certInd P z su ad ro rs c1) (certInd P z su ad ro rs c2)
certInd P z su ad ro rs (mRO c)     = ro c (certInd P z su ad ro rs c)
certInd P z su ad ro rs (mRS c1 c2) =
  rs c1 c2 (certInd P z su ad ro rs c1) (certInd P z su ad ro rs c2)

------------------------------------------------------------------------
-- SECTION 2.  Source-endpoint preservation by structural induction.
--   srcM c = the SOURCE term code of the cert c (mirrors ParEnds.src_*).

srcM : CertM -> Term
srcM mZe         = ze#
srcM (mSu c)     = su# (srcM c)
srcM (mAd c1 c2) = ad# (srcM c1) (srcM c2)
srcM (mRO c)     = ad# ze# (srcM c)
srcM (mRS c1 c2) = ad# (su# (srcM c1)) (srcM c2)

srcC : (c : CertM) -> Deriv (eqF (ap1 src (codeC c)) (srcM c))
srcC mZe     = src_cZe
srcC (mSu c) =
  ruleTrans (src_cSu (codeC c)) (congR Pair tagSu (srcC c))
srcC (mAd c1 c2) =
  ruleTrans (src_cAd (codeC c1) (codeC c2))
    (congR Pair tagAd
      (ruleTrans (congL Pair (ap1 src (codeC c2)) (srcC c1))
                 (congR Pair (srcM c1) (srcC c2))))
srcC (mRO c) =
  ruleTrans (src_cRO (codeC c))
    (congR Pair tagAd (congR Pair ze# (srcC c)))
srcC (mRS c1 c2) =
  ruleTrans (src_cRS (codeC c1) (codeC c2))
    (congR Pair tagAd
      (ruleTrans (congL Pair (ap1 src (codeC c2)) (congR Pair tagSu (srcC c1)))
                 (congR Pair (su# (srcM c1)) (srcC c2))))

------------------------------------------------------------------------
-- SECTION 3.  VALIDITY preservation by structural induction.
--   Every cert BUILT as  codeC c  is valid:  isCert (codeC c) = O .
-- This is the lemma whose opaque-code version stalled triF; here it is a
-- four-line induction (the unary cases pass IH straight through; the binary
-- cases combine the two IHs with the Cantor conjunction  pi  + pi_O_O).

isCertC : (c : CertM) -> Deriv (eqF (ap1 isCert (codeC c)) O)
isCertC mZe     = isCert_cZe
isCertC (mSu c) = ruleTrans (isCert_cSu (codeC c)) (isCertC c)
isCertC (mRO c) = ruleTrans (isCert_cRO (codeC c)) (isCertC c)
isCertC (mAd c1 c2) =
  ruleTrans (isCert_cAd (codeC c1) (codeC c2))
    (ruleTrans (congL pi (ap1 isCert (codeC c2)) (isCertC c1))
      (ruleTrans (congR pi O (isCertC c2)) pi_O_O))
isCertC (mRS c1 c2) =
  ruleTrans (isCert_cRS (codeC c1) (codeC c2))
    (ruleTrans (congL pi (ap1 isCert (codeC c2)) (isCertC c1))
      (ruleTrans (congR pi O (isCertC c2)) pi_O_O))
