{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ParReflPres -- STAGE 4b: the ENDPOINT/VALIDITY PRESERVATION of the
-- reflexivity certificate builder (T4.ParRefl), completing the object
-- analog of  parRefl : (t : Tm) -> Par t t  (T4.ChurchRosserProto).
--
-- Method (the SAME shape as T4.ProgParse's round-trip  parse (enc t) = t ):
-- META structural induction on a term  t : Tm , transported to the object
-- code  code t  (ze#/su#/ad#).  Each case CHAINS the already-proved DEFINING
-- equations of  reflCert  (T4.ParRefl) and  src/tgt/isCert  (T4.ParEnds);
-- the IH closes the recursion.  No object course-of-values is needed because
-- the term structure is carried by the meta  Tm  (exactly as the proto's
-- parRefl is  (t : Tm) -> ... ).
--
-- Results, for every  t : Tm  (with  d = reflCert (code t)  the witness):
--     src    d = code t        (reflCert_src)
--     tgt    d = code t        (reflCert_tgt)
--     isCert d = O             (reflCert_isCert)
-- i.e.  d  is a VALID Par-certificate with source = target = code t :
-- the relational  Par (code t) (code t) .

module T4.ParReflPres where

open import T4.Base

open import T4.ParRefl using ( reflCert ; reflCert_ze ; reflCert_su ; reflCert_ad )
open import T4.ParEnds using
  ( src ; tgt ; isCert
  ; src_cZe ; src_cSu ; src_cAd
  ; tgt_cZe ; tgt_cSu ; tgt_cAd
  ; isCert_cZe ; isCert_cSu ; isCert_cAd
  ; pi_O_O )
open import T4.TrsCodeObj using ( ze# ; su# ; ad# ; tagSu ; tagAd )

open import BRA3.Church using ( pi )

------------------------------------------------------------------------
-- Meta term structure and its object coding (TrsCodeObj).

data Tm : Set where
  ze : Tm
  su : Tm -> Tm
  ad : Tm -> Tm -> Tm

code : Tm -> Term
code ze       = ze#
code (su t)   = su# (code t)
code (ad a b) = ad# (code a) (code b)

------------------------------------------------------------------------
-- Source preservation:  src (reflCert (code t)) = code t .

reflCert_src : (t : Tm) -> Deriv (eqF (ap1 src (ap1 reflCert (code t))) (code t))
reflCert_src ze =
  ruleTrans (cong1 src reflCert_ze) src_cZe
reflCert_src (su t) =
  ruleTrans (cong1 src (reflCert_su (code t)))
    (ruleTrans (src_cSu (ap1 reflCert (code t)))
               (congR Pair tagSu (reflCert_src t)))
reflCert_src (ad a b) =
  ruleTrans (cong1 src (reflCert_ad (code a) (code b)))
    (ruleTrans (src_cAd (ap1 reflCert (code a)) (ap1 reflCert (code b)))
               (congR Pair tagAd
                 (ruleTrans (congL Pair (ap1 src (ap1 reflCert (code b))) (reflCert_src a))
                            (congR Pair (code a) (reflCert_src b)))))

------------------------------------------------------------------------
-- Target preservation:  tgt (reflCert (code t)) = code t .

reflCert_tgt : (t : Tm) -> Deriv (eqF (ap1 tgt (ap1 reflCert (code t))) (code t))
reflCert_tgt ze =
  ruleTrans (cong1 tgt reflCert_ze) tgt_cZe
reflCert_tgt (su t) =
  ruleTrans (cong1 tgt (reflCert_su (code t)))
    (ruleTrans (tgt_cSu (ap1 reflCert (code t)))
               (congR Pair tagSu (reflCert_tgt t)))
reflCert_tgt (ad a b) =
  ruleTrans (cong1 tgt (reflCert_ad (code a) (code b)))
    (ruleTrans (tgt_cAd (ap1 reflCert (code a)) (ap1 reflCert (code b)))
               (congR Pair tagAd
                 (ruleTrans (congL Pair (ap1 tgt (ap1 reflCert (code b))) (reflCert_tgt a))
                            (congR Pair (code a) (reflCert_tgt b)))))

------------------------------------------------------------------------
-- Validity:  isCert (reflCert (code t)) = O .
-- (Binary case: isCert(cAd ..) = pi (isCert ..) (isCert ..) ; both = O by IH,
--  and pi O O = O.)

reflCert_isCert : (t : Tm) -> Deriv (eqF (ap1 isCert (ap1 reflCert (code t))) O)
reflCert_isCert ze =
  ruleTrans (cong1 isCert reflCert_ze) isCert_cZe
reflCert_isCert (su t) =
  ruleTrans (cong1 isCert (reflCert_su (code t)))
    (ruleTrans (isCert_cSu (ap1 reflCert (code t)))
               (reflCert_isCert t))
reflCert_isCert (ad a b) =
  ruleTrans (cong1 isCert (reflCert_ad (code a) (code b)))
    (ruleTrans (isCert_cAd (ap1 reflCert (code a)) (ap1 reflCert (code b)))
      (ruleTrans (congL pi (ap1 isCert (ap1 reflCert (code b))) (reflCert_isCert a))
        (ruleTrans (congR pi O (reflCert_isCert b)) pi_O_O)))

------------------------------------------------------------------------
-- A certificate of  Par t u  is a witness term  wit  with the three
-- object-derivable side conditions.  This is the relational  Par t u
-- "exists a valid cert with these endpoints" (the meta existential; the
-- object  E (parBody t u)  packaging is added once the Par PREDICATE is
-- defined, the same  wit  serving as the  E_intro  witness).  ParCert is
-- the value the CR cert-construction lemmas (parRefl here; stepPar, tri,
-- ... next) return.

record ParCert (t u : Term) : Set where
  constructor mkParCert
  field
    wit    : Term
    valid  : Deriv (eqF (ap1 isCert wit) O)
    srcEq  : Deriv (eqF (ap1 src wit) t)
    tgtEq  : Deriv (eqF (ap1 tgt wit) u)
open ParCert public

-- parRefl :  reflCert (code t)  certifies  Par (code t) (code t) .

parRefl : (t : Tm) -> ParCert (code t) (code t)
parRefl t =
  mkParCert (ap1 reflCert (code t))
            (reflCert_isCert t) (reflCert_src t) (reflCert_tgt t)
