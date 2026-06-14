{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ParStep -- STAGE 4b (deliverable 2a): the object analog of
--     stepPar : Step t u -> Par t u          (T4.ChurchRosserProto)
-- the inclusion of single-step reduction into parallel reduction, as a
-- CERTIFICATE BUILDER  StepM t u -> ParCert (code t) (code u) .
--
-- Method (the SAME shape as T4.ParReflPres): META structural induction on
-- a meta one-step derivation  StepM  (mirroring the proto's  Step ), with
-- each case CHAINING the already-proved defining equations of the cert
-- constructors (src/tgt/isCert in T4.ParEnds) and the reflexivity-cert
-- preservation lemmas (T4.ParReflPres).  No object course-of-values.
--
-- For the toy orthogonal recursor TRS (ze/su/ad):
--     stepPar (rO  y)   = cRO (reflCert (code y))         -- ad ze y      -> y
--     stepPar (rS  x y) = cRS (reflCert x)(reflCert y)    -- ad (su x) y  -> su (ad x y)
--     stepPar (cSu s)   = cSu (sub-cert)                  -- congruence under su
--     stepPar (cA1 s)   = cAd (sub-cert)(reflCert b)      -- congruence in ad arg 1
--     stepPar (cA2 s)   = cAd (reflCert a)(sub-cert)      -- congruence in ad arg 2
-- each with its three side conditions (isCert = O, src = code t, tgt = code u)
-- discharged by the deep equations + the IH.

module T4.ParStep where

open import T4.Base

open import T4.ParCert    using ( cSu ; cAd ; cRO ; cRS )
open import T4.ParRefl    using ( reflCert )
open import T4.ParEnds    using
  ( src ; tgt ; isCert
  ; src_cSu ; src_cAd ; src_cRO ; src_cRS
  ; tgt_cSu ; tgt_cAd ; tgt_cRO ; tgt_cRS
  ; isCert_cSu ; isCert_cAd ; isCert_cRO ; isCert_cRS
  ; pi_O_O )
open import T4.ParReflPres using
  ( Tm ; ze ; su ; ad ; code
  ; reflCert_src ; reflCert_tgt ; reflCert_isCert
  ; ParCert ; mkParCert ; wit ; valid ; srcEq ; tgtEq )
open import T4.TrsCodeObj using ( ze# ; su# ; ad# ; tagSu ; tagAd )

open import BRA3.Church using ( pi )

------------------------------------------------------------------------
-- Meta one-step reduction (the proto's  Step , over the meta terms  Tm ).

data StepM : Tm -> Tm -> Set where
  stO  : (y : Tm)                            -> StepM (ad ze y) y
  stS  : (x y : Tm)                          -> StepM (ad (su x) y) (su (ad x y))
  stSu : {t t' : Tm}   -> StepM t t'         -> StepM (su t) (su t')
  stA1 : {a a' b : Tm} -> StepM a a'         -> StepM (ad a b) (ad a' b)
  stA2 : {a b b' : Tm} -> StepM b b'         -> StepM (ad a b) (ad a b')

------------------------------------------------------------------------
-- The diagonal (reflexivity) certificate of a coded term, abbreviated.

rc : Tm -> Term
rc t = ap1 reflCert (code t)

------------------------------------------------------------------------
-- stepPar : every meta one-step  StepM t u  yields a Par-certificate
-- with source  code t  and target  code u .

stepPar : {t u : Tm} -> StepM t u -> ParCert (code t) (code u)

-- ad ze y -> y :  cert  cRO (reflCert (code y)) .
--   src (cRO d) = ad# ze# (src d) = ad# ze# (code y) = code (ad ze y)
--   tgt (cRO d) = tgt d = code y
stepPar (stO y) =
  mkParCert (cRO (rc y))
    (ruleTrans (isCert_cRO (rc y)) (reflCert_isCert y))
    (ruleTrans (src_cRO (rc y))
       (congR Pair tagAd (congR Pair ze# (reflCert_src y))))
    (ruleTrans (tgt_cRO (rc y)) (reflCert_tgt y))

-- ad (su x) y -> su (ad x y) :  cert  cRS (reflCert x)(reflCert y) .
--   src (cRS d1 d2) = ad# (su# (src d1)) (src d2) = ad# (su# (code x)) (code y)
--   tgt (cRS d1 d2) = su# (ad# (tgt d1)(tgt d2)) = su# (ad# (code x)(code y))
stepPar (stS x y) =
  mkParCert (cRS (rc x) (rc y))
    (ruleTrans (isCert_cRS (rc x) (rc y))
       (ruleTrans (congL pi (ap1 isCert (rc y)) (reflCert_isCert x))
          (ruleTrans (congR pi O (reflCert_isCert y)) pi_O_O)))
    (ruleTrans (src_cRS (rc x) (rc y))
       (congR Pair tagAd
          (ruleTrans (congL Pair (ap1 src (rc y))
                        (congR Pair tagSu (reflCert_src x)))
                     (congR Pair (su# (code x)) (reflCert_src y)))))
    (ruleTrans (tgt_cRS (rc x) (rc y))
       (congR Pair tagSu
          (congR Pair tagAd
             (ruleTrans (congL Pair (ap1 tgt (rc y)) (reflCert_tgt x))
                        (congR Pair (code x) (reflCert_tgt y))))))

-- congruence under su :  cert  cSu (sub-cert) .
stepPar (stSu st) =
  let r = stepPar st ; dw = wit r in
  mkParCert (cSu dw)
    (ruleTrans (isCert_cSu dw) (valid r))
    (ruleTrans (src_cSu dw) (congR Pair tagSu (srcEq r)))
    (ruleTrans (tgt_cSu dw) (congR Pair tagSu (tgtEq r)))

-- congruence in ad arg 1 :  cert  cAd (sub-cert)(reflCert b) .
stepPar (stA1 {a} {a'} {b} st) =
  let r = stepPar st ; dw = wit r ; db = rc b in
  mkParCert (cAd dw db)
    (ruleTrans (isCert_cAd dw db)
       (ruleTrans (congL pi (ap1 isCert db) (valid r))
          (ruleTrans (congR pi O (reflCert_isCert b)) pi_O_O)))
    (ruleTrans (src_cAd dw db)
       (congR Pair tagAd
          (ruleTrans (congL Pair (ap1 src db) (srcEq r))
                     (congR Pair (code a) (reflCert_src b)))))
    (ruleTrans (tgt_cAd dw db)
       (congR Pair tagAd
          (ruleTrans (congL Pair (ap1 tgt db) (tgtEq r))
                     (congR Pair (code a') (reflCert_tgt b)))))

-- congruence in ad arg 2 :  cert  cAd (reflCert a)(sub-cert) .
stepPar (stA2 {a} {b} {b'} st) =
  let r = stepPar st ; dw = wit r ; da = rc a in
  mkParCert (cAd da dw)
    (ruleTrans (isCert_cAd da dw)
       (ruleTrans (congL pi (ap1 isCert dw) (reflCert_isCert a))
          (ruleTrans (congR pi O (valid r)) pi_O_O)))
    (ruleTrans (src_cAd da dw)
       (congR Pair tagAd
          (ruleTrans (congL Pair (ap1 src dw) (reflCert_src a))
                     (congR Pair (code a) (srcEq r)))))
    (ruleTrans (tgt_cAd da dw)
       (congR Pair tagAd
          (ruleTrans (congL Pair (ap1 tgt dw) (reflCert_tgt a))
                     (congR Pair (code a) (tgtEq r)))))
