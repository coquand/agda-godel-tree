{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm12.Param.AxI
--
-- Parametric-Term encoding constants and dispatch lemma for axI.
-- Mirrors BRA2.Thm12.Param.AxZ but for the identity functor.  The actual
-- cascade chain lives inside ThmT.agda's abstract block as
-- thmTDispAxI_param ; this file is a thin wrapper.

module BRA2.Thm12.Param.AxI where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.DerivThreshold
open import BRA2.Thm.ThmT
  using ( thmT ; tagCode_axI ; thmTDispAxI_param )

------------------------------------------------------------------------
-- Parametric encoding constants for axI.
--
--   parEncAxI tT  encodes  axI y  with the y-slot held by  tT.
--   parOutAxI tT  is the parametric encoded conclusion  (I y) = y :
--     Pair (Pair tagAp1 (Pair codeF1I tT)) tT .

parEncAxI : Term -> Term
parEncAxI tT = ap2 Pair tagCode_axI tT

parOutAxI : Term -> Term
parOutAxI tT =
  ap2 Pair (ap2 Pair (reify tagAp1)
                     (ap2 Pair (reify (codeF1 I)) tT))
           tT

------------------------------------------------------------------------
-- Parametric dispatch lemma.

parDispAxI : (tT : Term) ->
  Deriv (atomic (eqn (ap1 thmT (parEncAxI tT)) (parOutAxI tT)))
parDispAxI tT = thmTDispAxI_param tT
