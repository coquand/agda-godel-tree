{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.CertHeadStab -- the SINGLE-STEP head-preservation core of object
-- head-stability (toward discharging HeadStab / object Con(T0)).
--
-- A valid Par-certificate whose SOURCE is ze-headed has a ze-headed TARGET:
-- only  cZe  has a ze#-headed source (cSu -> su#, cAd/cRO/cRS -> ad#), and
-- cZe's target is ze#.  The ze-head HYPOTHESIS itself pins the constructor:
-- every non-cZe shape makes  hd (src ..)  a SUCCESSOR tag (s O / s (s O)),
-- which contradicts  hd (src ..) = tagZe = O  by  succEqO_to_anything  -- so
-- no surjective pairing / no meta refuter is needed (the keystone-free route).
--
--   certHeadZeM : (c : CertM) -> hd (src (codeC c)) = tagZe
--                            -> hd (tgt (codeC c)) = tagZe
--
-- This is the STRUCTURE-CARRYING form (meta induction on the CertM shadow),
-- the per-step content of  parsZeStab .  The OPAQUE lifting (the same head
-- dispatch driven through  T4.SizedPres.foldOpaque  on an opaque cert) plus
-- the opaque-chain course-of-values (via  T4.DescSnd.descSnd) are the remaining
-- assembly for the full object  HeadStab .
--
-- No holes, no postulates; --safe --without-K --exact-split.

module T4.CertHeadStab where

open import T4.Base

open import T4.CertTree   using ( CertM ; mZe ; mSu ; mAd ; mRO ; mRS ; codeC )
open import T4.ParEnds    using
  ( src ; tgt
  ; hd_src_cZe ; hd_src_cSu ; hd_src_cAd ; hd_src_cRO ; hd_src_cRS
  ; hd_tgt_cZe ; hd_tgt_cSu )
open import T4.TrsCodeObj using ( hd ; tagZe ; tagSu ; tagAd )

open import BRA3.ChurchT80 using ( succEqO_to_anything )
open import BRA3.Church    using ( predecessor ; T_p_S_v0 )

------------------------------------------------------------------------
-- Single-step ze head-preservation, by induction on the cert shadow.

certHeadZeM : (c : CertM) ->
  Deriv (eqF (hd (ap1 src (codeC c))) tagZe) ->
  Deriv (eqF (hd (ap1 tgt (codeC c))) tagZe)
certHeadZeM mZe hyp = hd_tgt_cZe                       -- codeC mZe = cZe
certHeadZeM (mSu c') hyp =
  -- hd (src (cSu ..)) = tagSu = s O ; with hyp = O this is  s O = O  -> ex falso.
  let pSO : Deriv (eqF (ap1 s O) O)
      pSO = ruleTrans (ruleSym (hd_src_cSu (codeC c'))) hyp
  in mp (succEqO_to_anything O _) pSO
certHeadZeM (mAd c1 c2) hyp =
  -- hd (src (cAd ..)) = tagAd = s (s O) ; with hyp = O this is  s (s O) = O.
  let pSSO : Deriv (eqF (ap1 s (ap1 s O)) O)
      pSSO = ruleTrans (ruleSym (hd_src_cAd (codeC c1) (codeC c2))) hyp
  in mp (succEqO_to_anything (ap1 s O) _) pSSO
certHeadZeM (mRO c') hyp =
  let pSSO : Deriv (eqF (ap1 s (ap1 s O)) O)
      pSSO = ruleTrans (ruleSym (hd_src_cRO (codeC c'))) hyp
  in mp (succEqO_to_anything (ap1 s O) _) pSSO
certHeadZeM (mRS c1 c2) hyp =
  let pSSO : Deriv (eqF (ap1 s (ap1 s O)) O)
      pSSO = ruleTrans (ruleSym (hd_src_cRS (codeC c1) (codeC c2))) hyp
  in mp (succEqO_to_anything (ap1 s O) _) pSSO

------------------------------------------------------------------------
-- Single-step su head-preservation (only cSu has su#-headed source; its
-- target is su#-headed).  The non-cSu cases are ex falso: a ze head gives
-- O = s O (-> s O = O), an ad head gives s (s O) = s O (-> s O = O after one
-- predecessor cancellation).

-- ad-tag clash helper:  s (s O) = s O  is impossible (cancel one s).
ssEqsToSO : Deriv (eqF (ap1 s (ap1 s O)) (ap1 s O)) -> Deriv (eqF (ap1 s O) O)
ssEqsToSO p =
  let e1 : Deriv (eqF (ap1 predecessor (ap1 s (ap1 s O)))
                       (ap1 predecessor (ap1 s O)))
      e1 = mp (ax_eqCong1 predecessor (ap1 s (ap1 s O)) (ap1 s O)) p
      tps1 : Deriv (eqF (ap1 predecessor (ap1 s (ap1 s O))) (ap1 s O))
      tps1 = ruleInst 0 (ap1 s O) T_p_S_v0
      tps2 : Deriv (eqF (ap1 predecessor (ap1 s O)) O)
      tps2 = ruleInst 0 O T_p_S_v0
  in ruleTrans (ruleSym tps1) (ruleTrans e1 tps2)

certHeadSuM : (c : CertM) ->
  Deriv (eqF (hd (ap1 src (codeC c))) tagSu) ->
  Deriv (eqF (hd (ap1 tgt (codeC c))) tagSu)
certHeadSuM mZe hyp =
  -- hd (src cZe) = tagZe = O ; hyp = s O ; so  s O = O  -> ex falso.
  let pSO : Deriv (eqF (ap1 s O) O)
      pSO = ruleTrans (ruleSym hyp) hd_src_cZe
  in mp (succEqO_to_anything O _) pSO
certHeadSuM (mSu c') hyp = hd_tgt_cSu (codeC c')      -- cSu -> su# target
certHeadSuM (mAd c1 c2) hyp =
  let pAdSu : Deriv (eqF (ap1 s (ap1 s O)) (ap1 s O))
      pAdSu = ruleTrans (ruleSym (hd_src_cAd (codeC c1) (codeC c2))) hyp
  in mp (succEqO_to_anything O _) (ssEqsToSO pAdSu)
certHeadSuM (mRO c') hyp =
  let pAdSu : Deriv (eqF (ap1 s (ap1 s O)) (ap1 s O))
      pAdSu = ruleTrans (ruleSym (hd_src_cRO (codeC c'))) hyp
  in mp (succEqO_to_anything O _) (ssEqsToSO pAdSu)
certHeadSuM (mRS c1 c2) hyp =
  let pAdSu : Deriv (eqF (ap1 s (ap1 s O)) (ap1 s O))
      pAdSu = ruleTrans (ruleSym (hd_src_cRS (codeC c1) (codeC c2))) hyp
  in mp (succEqO_to_anything O _) (ssEqsToSO pAdSu)
