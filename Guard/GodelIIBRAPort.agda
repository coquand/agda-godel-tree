{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.GodelIIBRAPort -- Option G port of Guard.GodelIIBRA.
--
-- Gödel's second incompleteness theorem at the BRA layer,
-- parameterised over the chain and the BRA-to-Deriv extractor.
--
-- Structure parallels Guard.GodelIIBRA (Provable version):
--
--   godelII_BRA chain con dCon  =  bridge (mp chain dCon)
--
-- but using BRA as the propositional layer and  braGodelIBridge
-- (Guard.BRAGodelIBridge) as the closure.
--
-- Once a BRA-layer chain  ChainBRA : BRA _ (conBRAEqn ⊃ atomic gsCR)
-- is delivered, and an extractor  BRAExtractTriv  is provided, this
-- module closes Gödel II at the BRA layer for hyp = atomic Triv.
--
-- Current status: the chain (step 4+5+closure) is BLOCKED — see
-- Guard.GodelIIBRAv2 for the full obstruction analysis.  The
-- extractor is also partial (handles ruleSub only at atomic P,
-- which is the sole chain-usage pattern).  This module compiles
-- parametrically in both inputs.
--
-- No postulates, no holes.

module Guard.GodelIIBRAPort where

open import Guard.Base
open import Guard.Step using (Consistent)
open import Guard.SubstTForPrecompClassical using (Triv ; gsCR)
open import Guard.Formula
open import Guard.BRA
open import Guard.ConBRAv2 using (conBRAEqn ; ConBRA)
open import Guard.BRAGodelIBridge using (BRAExtractTriv ; braGodelIBridge)

------------------------------------------------------------------------
-- The chain: ConBRA ⊃ gsCR at the BRA layer.
--
-- Once delivered, godelII_BRAPort below becomes the full BRA-layer
-- Gödel II.

ChainBRAv2 : Set
ChainBRAv2 = BRA (atomic Triv) (ConBRA imp atomic gsCR)

------------------------------------------------------------------------
-- godelII_BRAPort, parameterised over chain and extractor.

godelII_BRAPort :
  BRAExtractTriv ->
  ChainBRAv2 ->
  Consistent Triv ->
  BRA (atomic Triv) (atomic conBRAEqn) ->
  Empty
godelII_BRAPort extract chain con dCon =
  braGodelIBridge extract con (mp chain dCon)
