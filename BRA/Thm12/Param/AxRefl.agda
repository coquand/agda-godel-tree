{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm12.Param.AxRefl
--
-- Parametric-Term encoding constants and dispatch lemma for axRefl.

module BRA.Thm12.Param.AxRefl where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Thm.ThmT
  using ( thmT ; tagCode_axRefl ; thmTDispAxRefl_param )

-- parEncAxRefl tT  encodes  axRefl y  with the y-slot held by  tT.
-- parOutAxRefl tT  is the parametric encoded conclusion  y = y :
--   Pair tT tT  (since  codeFormula (atomic (eqn y y)) = nd (code y) (code y) ).

parEncAxRefl : Term -> Term
parEncAxRefl tT = ap2 Pair tagCode_axRefl tT

parOutAxRefl : Term -> Term
parOutAxRefl tT = ap2 Pair tT tT

parDispAxRefl : (tT : Term) ->
  Deriv (atomic (eqn (ap1 thmT (parEncAxRefl tT)) (parOutAxRefl tT)))
parDispAxRefl tT = thmTDispAxRefl_param tT
