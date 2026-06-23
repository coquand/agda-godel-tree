{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.WfRedBundle -- bundle the per-tag opaque recovery into records that the
-- course-of-values triangle preservation (triPresObjOpaque) consumes at each
-- node.  Given  wfRedSized p = O  and the tag of  p , a bundle delivers
--
--   * the STRICT child-descent bound(s)  leq (s (dsize child)) (dsize p)
--     -- the  covMeasure(dsize)  descent input -- and
--   * the child VALIDITIES  wfRedSized child = O .
--
-- The binary size-check  leq (s (sigma (dsize pL)(dsize pR))) (dsize p)
-- (extractSizeCheck_Ad/RS) splits into the two per-child bounds by the same
-- leq_sigma + T78 step as T4.SizedDescentOp.descOpaqueL/R, here in the
-- dsize world.  The child validities are the extractChild_* lemmas (the LEFT
-- ones now licensed by T4.TauRowBase.fstLe).
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.WfRedBundle where

open import T4.Base

open import T4.DerCodeS using ( dtag ; pArg ; pL ; pR ; dsize )
open import T4.DerCode  using ( dgSu ; dgAd ; dgRO ; dgRS )
open import T4.WfRedSized using ( wfRedSized )
open import T4.WfRedExtract
  using ( extractSizeCheck_Su ; extractSizeCheck_Ad
        ; extractSizeCheck_RO ; extractSizeCheck_RS
        ; extractChild_Su ; extractChild_RO
        ; extractChild_Ad_L ; extractChild_Ad_R
        ; extractChild_RS_L ; extractChild_RS_R )

open import BRA3.Church    using ( sigma )
open import BRA3.ChurchLeq using ( leq )
open import BRA3.ChurchT78 using ( T78 )
open import BRA3.RuleInst2 using ( ruleInst2 )
open import T4.LeqMono using ( leq_trans ; leq_sigma_left ; leq_sigma_right )

------------------------------------------------------------------------
-- SECTION 1.  Split the binary size-check into per-child descent bounds.

-- from  leq (s (sigma (dsize pL)(dsize pR))) (dsize p)  recover the LEFT bound.
descChildL : (p : Term) ->
  Deriv (leq (ap1 s (ap2 sigma (dsize (pL p)) (dsize (pR p)))) (dsize p)) ->
  Deriv (leq (ap1 s (dsize (pL p))) (dsize p))
descChildL p hsz =
  let l' : Term
      l' = dsize (pL p)
      r' : Term
      r' = dsize (pR p)
      leqS : Deriv (leq (ap1 s l') (ap1 s (ap2 sigma l' r')))
      leqS = mp (ruleInst2 0 l' 1 (ap2 sigma l' r') refl T78)
                (leq_sigma_left l' r')
  in leq_trans (ap1 s l') (ap1 s (ap2 sigma l' r')) (dsize p) leqS hsz

-- ... and the RIGHT bound.
descChildR : (p : Term) ->
  Deriv (leq (ap1 s (ap2 sigma (dsize (pL p)) (dsize (pR p)))) (dsize p)) ->
  Deriv (leq (ap1 s (dsize (pR p))) (dsize p))
descChildR p hsz =
  let l' : Term
      l' = dsize (pL p)
      r' : Term
      r' = dsize (pR p)
      leqS : Deriv (leq (ap1 s r') (ap1 s (ap2 sigma l' r')))
      leqS = mp (ruleInst2 0 r' 1 (ap2 sigma l' r') refl T78)
                (leq_sigma_right l' r')
  in leq_trans (ap1 s r') (ap1 s (ap2 sigma l' r')) (dsize p) leqS hsz

------------------------------------------------------------------------
-- SECTION 2.  The per-arity bundles.

record UnaryBundle (p : Term) : Set where
  constructor mkUnary
  field
    descArg  : Deriv (leq (ap1 s (dsize (pArg p))) (dsize p))
    validArg : Deriv (eqF (ap1 wfRedSized (pArg p)) O)
open UnaryBundle public

record BinaryBundle (p : Term) : Set where
  constructor mkBinary
  field
    descL  : Deriv (leq (ap1 s (dsize (pL p))) (dsize p))
    descR  : Deriv (leq (ap1 s (dsize (pR p))) (dsize p))
    validL : Deriv (eqF (ap1 wfRedSized (pL p)) O)
    validR : Deriv (eqF (ap1 wfRedSized (pR p)) O)
open BinaryBundle public

------------------------------------------------------------------------
-- SECTION 3.  The four tag bundlers (one per derivation constructor).

bundleSu : (p : Term) ->
  Deriv (neg (eqF p O)) -> Deriv (eqF (dtag p) dgSu) ->
  Deriv (eqF (ap1 wfRedSized p) O) -> UnaryBundle p
bundleSu p ne htag hwf =
  mkUnary (extractSizeCheck_Su p ne htag hwf)
          (extractChild_Su p ne htag hwf)

bundleRO : (p : Term) ->
  Deriv (neg (eqF p O)) -> Deriv (eqF (dtag p) dgRO) ->
  Deriv (eqF (ap1 wfRedSized p) O) -> UnaryBundle p
bundleRO p ne htag hwf =
  mkUnary (extractSizeCheck_RO p ne htag hwf)
          (extractChild_RO p ne htag hwf)

bundleAd : (p : Term) ->
  Deriv (neg (eqF p O)) -> Deriv (eqF (dtag p) dgAd) ->
  Deriv (eqF (ap1 wfRedSized p) O) -> BinaryBundle p
bundleAd p ne htag hwf =
  let hsz = extractSizeCheck_Ad p ne htag hwf
  in mkBinary (descChildL p hsz) (descChildR p hsz)
              (extractChild_Ad_L p ne htag hwf)
              (extractChild_Ad_R p ne htag hwf)

bundleRS : (p : Term) ->
  Deriv (neg (eqF p O)) -> Deriv (eqF (dtag p) dgRS) ->
  Deriv (eqF (ap1 wfRedSized p) O) -> BinaryBundle p
bundleRS p ne htag hwf =
  let hsz = extractSizeCheck_RS p ne htag hwf
  in mkBinary (descChildL p hsz) (descChildR p hsz)
              (extractChild_RS_L p ne htag hwf)
              (extractChild_RS_R p ne htag hwf)
