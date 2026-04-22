{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.GodelIIBRA -- Gödel's second incompleteness theorem at the
-- BRA Provable layer.
--
-- Following Guard 1963 Theorem 14 (BRA), the BRA-style consistency
-- statement  ConBRA = "for all y, th(y) ≠ '0 = 1'"  (where th is our
--   thmT trivCT  and '0 = 1' is codeBotT) is unprovable in BRA from
-- the trivial hypothesis.
--
-- The result splits naturally into two pieces:
--
--   (A)  CHAIN: a Provable derivation showing
--          atomic conBRAEqn  imp  atomic gsCR
--        i.e. "if BRA proves its own consistency, then BRA proves the
--        Gödel sentence".  This is the substantive work transcribing
--        Guard 1963 chain steps 1-5 (or its meta-level Deriv analog).
--
--   (B)  CLOSURE: from a Provable derivation of  atomic gsCR  at
--        hyp = atomic Triv, derive Empty using godelIClassical
--        (provided already by Guard.ProvableGodelIBridge).
--
-- This module composes (A) + (B) into godelII_BRA, parameterised over
-- the chain (A).  Once a closed Provable derivation of the chain is
-- in hand, godelII_BRA becomes a closed proof of Gödel II.
--
-- The chain is treated as a hypothesis (not a postulate or hole) — it
-- is one of the function's arguments.  The user supplies it; the rest
-- of Gödel II follows.  See NEXT-SESSION-BRA-GODELII.md for the
-- two-route strategy to build the chain itself.
--
-- No postulates, no holes.

module Guard.GodelIIBRA where

open import Guard.Base
open import Guard.Step using (Consistent)
open import Guard.SubstTForPrecompClassical using (Triv ; gsCR)
open import Guard.Formula
open import Guard.Provable
open import Guard.ConBRA using (ConBRA ; conBRAEqn)
open import Guard.ProvableGodelIBridge using (provableGodelIBridge)

------------------------------------------------------------------------
-- The chain: ConBRA ⊃ gsCR at the Provable layer.
--
-- Once supplied as a closed Provable derivation, godelII_BRA below
-- becomes the full Gödel II for BRA.

ChainBRA : Set
ChainBRA = Provable (atomic Triv) (ConBRA imp atomic gsCR)

------------------------------------------------------------------------
-- godelII_BRA, parameterised over the chain.
--
--   Gödel's second incompleteness theorem (BRA form):
--   if Triv is consistent and BRA proves its own consistency, then
--   contradiction.

godelII_BRA :
  ChainBRA ->
  Consistent Triv ->
  Provable (atomic Triv) (atomic conBRAEqn) ->
  Empty
godelII_BRA chain con dCon =
  provableGodelIBridge con (mp chain dCon)

------------------------------------------------------------------------
-- Equivalent contrapositive form:  Consistent Triv ⊢ ¬ Provable ConBRA.
--
-- Same content, different presentation.  Useful when the user has the
-- consistency hypothesis in scope and wants to talk about the
-- impossibility of proving ConBRA.

godelII_BRA_contra :
  ChainBRA ->
  Consistent Triv ->
  Provable (atomic Triv) (atomic conBRAEqn) ->
  Empty
godelII_BRA_contra = godelII_BRA
