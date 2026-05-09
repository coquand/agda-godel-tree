{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm12.Param.AxZ
--
-- Parametric-Term encoding constants and dispatch lemma for axZ.  Where
-- the closed-Tree thmTDispAxZ in BRA2.Thm.ThmT bakes in  reify (code x)
-- as the payload's xT-slot (meta-recursive on x's structure), this version
-- takes  xT : Term  directly so Theorem 12's asymmetric encoded equation
-- can put  cor x  at that slot (see  codeFTeq1  in NEXT-SESSION-THM12.md).
--
-- The actual cascade chain lives inside ThmT.agda's abstract block as
-- thmTDispAxZ_param ; this file is a thin wrapper providing readable
-- names.

module BRA2.Thm12.Param.AxZ where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.DerivThreshold
open import BRA2.Thm.Tag
open import BRA2.Thm.ThmT
  using ( thmT ; tagCode_axKT ; thmTDispAxZ_param )

------------------------------------------------------------------------
-- Parametric encoding constants for axZ.
--
--   parEncAxZ xT  encodes the proof-tree of  axZ y  with the y-slot
--   filled by the parametric Term  xT  (rather than meta-computing
--   it via  reify (code y) ).
--
--   parOutAxZ xT  is the corresponding parametric output: encoded form
--   of the equation  (Z y) = O  with the y-slot held by  xT.

parEncAxZ : Term -> Term
parEncAxZ xT =
  ap2 Pair tagCode_axKT
    (ap2 Pair (reify (codeF1 Z)) xT)

parOutAxZ : Term -> Term
parOutAxZ xT =
  ap2 Pair (ap2 Pair (reify tagAp1)
                     (ap2 Pair (reify (codeF1 Z)) xT))
           O

------------------------------------------------------------------------
-- Parametric dispatch lemma.

parDispAxZ : (xT : Term) ->
  Deriv (atomic (eqn (ap1 thmT (parEncAxZ xT)) (parOutAxZ xT)))
parDispAxZ xT = thmTDispAxZ_param xT
