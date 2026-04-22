{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.ProvableGodelIBridge -- bridge from a Provable proof of gsCR
-- (Ryan's classical Gödel sentence) to Empty, given Consistent Triv.
--
-- This is the *closure step* of the BRA Gödel II argument: once the
-- chain (Th 13 + Guard 1963 chain steps 1-5) produces a Provable
-- derivation of  atomic gsCR  at hyp = atomic Triv, the result
-- follows from godelIClassical via the Provable→Deriv soundness bridge.
--
-- The chain producing  Provable (atomic Triv) (atomic gsCR)  from
-- Provable (atomic Triv) (atomic conBRAEqn)  is the substantial work
-- tracked in NEXT-SESSION-BRA-GODELII.md (chain steps 1-5).  This file
-- delivers the *final hop*:
--
--   provableGodelIBridge :
--     Consistent Triv ->
--     Provable (atomic Triv) (atomic gsCR) ->
--     Empty
--
-- Once the chain is in place, godelII_BRA decomposes as:
--   godelII_BRA con dProv =
--     provableGodelIBridge con (mp chainImpl dProv)
-- where chainImpl : Provable hyp (atomic conBRAEqn imp atomic gsCR) is
-- the chain output.
--
-- Sound per Guard/SOUNDNESS.md: godelIClassical operates at hyp = Triv
-- (closed) so its internal ruleInst calls satisfy the Hilbert-Bernays
-- side condition.
--
-- No postulates, no holes.

module Guard.ProvableGodelIBridge where

open import Guard.Base
open import Guard.Term
open import Guard.Step using (Deriv ; Consistent ; ruleHyp)
open import Guard.SubstTForPrecompClassical using (Triv ; gsCR)
open import Guard.GodelIClassical using (godelIClassical)
open import Guard.Formula
open import Guard.Provable
open import Guard.ProvableSound using (sem ; provSound ; provExtract)

------------------------------------------------------------------------
-- The bridge.

-- Witness for sem (atomic Triv) Triv : a Deriv Triv Triv, discharged
-- by ruleHyp (works since Triv is abstract — we don't need to unfold
-- it to eqn O O).

semTrivAtTriv : sem (atomic Triv) Triv
semTrivAtTriv = ruleHyp {Triv}

provableGodelIBridge :
  Consistent Triv ->
  Provable (atomic Triv) (atomic gsCR) ->
  Empty
provableGodelIBridge con dProv =
  con (godelIClassical (provExtract semTrivAtTriv dProv))

------------------------------------------------------------------------
-- Variant: from any Provable hyp witnessing  atomic gsCR  whose
-- hypothesis interprets to a Deriv at Triv.

provableGodelIBridgeAt :
  {hyp : Formula} ->
  sem hyp Triv ->
  Consistent Triv ->
  Provable hyp (atomic gsCR) ->
  Empty
provableGodelIBridgeAt semHyp con dProv =
  con (godelIClassical (provExtract semHyp dProv))
