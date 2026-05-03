{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Th14MpProjSmoke
--
-- Smoke test for body_mp_eval_proj / thmTDispMp_proj after the
-- soundification swap to body_mp_v (2026-05-03).
--
-- thmTDispMp_proj used to take only  shape  as its non-trivial
-- hypothesis; the verifying body_mp_v requires the full bundle
-- (d1 + dh) for the projection equation to hold.  This file is
-- standalone (not imported by the godelII chain) and exists purely
-- as a sanity check that the projection-form dispatcher typechecks
-- on a generic Pair-shaped y1T given the load-bearing hypotheses.

module BRA.Th14MpProjSmoke where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv

open import BRA.Thm.ThmT
  using (thmT ; thmTDispMp_proj)
open import BRA.Thm.TagCodes using (tagCode_mp)

----------------------------------------------------------------------
-- mpProjFires : a generic instantiation showing thmTDispMp_proj
-- fires on a Pair-shaped y1T with the verifying-body witnesses.

mpProjFires : (x' y1' rest y2T pT qT : Term) ->
  let y1T : Term
      y1T = ap2 Pair (ap2 Pair x' y1') rest
  in Deriv (atomic (eqn (ap1 thmT y1T)
                         (ap2 Pair (reify tagImp) (ap2 Pair pT qT)))) ->
     Deriv (atomic (eqn (ap1 thmT y2T) pT)) ->
     Deriv (atomic (eqn
       (ap1 thmT (ap2 Pair tagCode_mp
                   (ap2 Pair (ap2 Pair (ap2 Pair x' y1') rest) y2T)))
       (ap1 Snd (ap1 Snd (ap1 thmT (ap2 Pair (ap2 Pair x' y1') rest))))))
mpProjFires x' y1' rest y2T pT qT d1 dh =
  thmTDispMp_proj (ap2 Pair (ap2 Pair x' y1') rest) y2T y1' x'
                  pT qT
                  (axFst (ap2 Pair x' y1') rest)
                  d1 dh
