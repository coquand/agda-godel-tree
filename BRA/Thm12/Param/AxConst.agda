{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm12.Param.AxConst
--
-- Parametric-Term encoding constants and dispatch lemma for axConst.
-- Mirrors AxZ / AxI; cascade chain lives inside ThmT.agda's abstract
-- block as thmTDispAxConst_param.

module BRA.Thm12.Param.AxConst where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Thm.ThmT
  using ( thmT ; tagCode_axConst ; thmTDispAxConst_param )

------------------------------------------------------------------------
-- Parametric encoding for axConst:
--   parEncAxConst aT bT  encodes  axConst y z  with y- and z-slots
--   held by  aT  and  bT  respectively.
--   parOutAxConst aT bT  is the parametric encoded conclusion
--   (Const y z) = y :  Pair (Pair tagAp2 (Pair codeF2Const (Pair aT bT))) aT.

parEncAxConst : Term -> Term -> Term
parEncAxConst aT bT = ap2 Pair tagCode_axConst (ap2 Pair aT bT)

parOutAxConst : Term -> Term -> Term
parOutAxConst aT bT =
  ap2 Pair (ap2 Pair (reify tagAp2)
                     (ap2 Pair (reify (codeF2 Const))
                               (ap2 Pair aT bT)))
           aT

parDispAxConst : (aT bT : Term) ->
  Deriv (atomic (eqn (ap1 thmT (parEncAxConst aT bT))
                     (parOutAxConst aT bT)))
parDispAxConst aT bT = thmTDispAxConst_param aT bT
