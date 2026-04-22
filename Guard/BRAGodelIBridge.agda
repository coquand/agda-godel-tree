{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.BRAGodelIBridge -- closure step for the BRA Gödel II argument,
-- Option G port of Guard.ProvableGodelIBridge.
--
-- Given a BRA derivation of  atomic gsCR  at  hyp = atomic Triv  plus
-- Consistent Triv, derive Empty via godelIClassical.  The key
-- ingredient is a  BRA -> Deriv  extractor at  (atomic Triv, Triv) ,
-- which is provided as a PARAMETER rather than a built-in lemma.
--
-- Rationale for parameterisation: a full  BRASound  analog of
-- Guard.ProvableSound requires a contravariant semantic-substitution
-- lemma ( sem (substF x t P) Triv -> sem P Triv  for arbitrary P ),
-- which is not generally derivable at  ambient = Triv  without extra
-- hypotheses on the formula's x-freeness.
--
-- For the Gödel II chain specifically, only ruleSub on atomic P is
-- used.  Callers whose BRA derivation of  atomic gsCR  uses no
-- ruleSub can discharge the extractor via  provToBRA  inverse (i.e.
-- the BRA is really a Provable).  Callers using ruleSub at atomic P
-- (the typical chain pattern) can discharge the extractor using the
-- atomic-only restriction:  ruleInst x t refl  applied at Triv.
--
-- The bridge itself is a one-line composition of the supplied
-- extractor with  godelIClassical .
--
-- No postulates, no holes.

module Guard.BRAGodelIBridge where

open import Guard.Base
open import Guard.Term
open import Guard.Step using (Deriv ; Consistent)
open import Guard.SubstTForPrecompClassical using (Triv ; gsCR)
open import Guard.GodelIClassical using (godelIClassical)
open import Guard.Formula
open import Guard.BRA

------------------------------------------------------------------------
-- Extractor parameter.
--
-- A caller-supplied function converting a BRA derivation at
--   hyp = atomic Triv ,  target = atomic eq
-- into a Deriv at ambient = Triv of the same equation.  In practice,
-- this is either:
--
--   (1)  provExtract semTrivAtTriv ∘ (BRA -> Provable projection)
--        when the BRA derivation uses no ruleSub.
--
--   (2)  A specialised extract that handles ruleSub on atomic P via
--        Deriv-level ruleInst with the trivial side condition
--        (substEq x t Triv = Triv).

BRAExtractTriv : Set
BRAExtractTriv = {eq : Equation} ->
                 BRA (atomic Triv) (atomic eq) ->
                 Deriv Triv eq

------------------------------------------------------------------------
-- The bridge.

braGodelIBridge :
  BRAExtractTriv ->
  Consistent Triv ->
  BRA (atomic Triv) (atomic gsCR) ->
  Empty
braGodelIBridge extract con dBra =
  con (godelIClassical (extract dBra))
