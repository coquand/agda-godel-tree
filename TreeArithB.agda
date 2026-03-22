{-# OPTIONS --without-K --exact-split #-}

-- TreeArithB: Stage B — consistency notions and R3
-- Build task only. No analysis, no Goedel discussion.

module TreeArithB where

open import ChwistekSyntax
open import ChwistekProvability
open import ChwistekCodeLogic
open import TreeArith

------------------------------------------------------------------------
-- Empty type
------------------------------------------------------------------------

data EmptyB : Set where

------------------------------------------------------------------------
-- Two consistency notions
------------------------------------------------------------------------

-- External: no ProofTA derivation proves fbotTA
ConExt : Set
ConExt = ProofTA fbotTA -> EmptyB

-- Internal: no code is accepted by checkTA as proving fbotTA
ConInt : Set
ConInt = (n : Nat) -> (c : Code) -> Eq (checkTA n c) (just fbotTA) -> EmptyB

------------------------------------------------------------------------
-- ConExt is already proved (from TreeArith soundness)
------------------------------------------------------------------------

-- GoodTA fbotTA = EmptyTA (from TreeArith). soundTA gives GoodTA A
-- from ProofTA A. So ProofTA fbotTA -> EmptyTA.

conExtProved : ConExt
conExtProved prf = goodTA-to-emptyB (soundTA prf)
  where
  -- Bridge EmptyTA (from TreeArith) to EmptyB (local)
  goodTA-to-emptyB : GoodTA fbotTA -> EmptyB
  goodTA-to-emptyB ()

------------------------------------------------------------------------
-- ConInt -> ConExt (via D1 = encoding correctness)
------------------------------------------------------------------------

-- Strategy: from ProofTA fbotTA, encode it, get a code the checker
-- accepts as proving fbotTA, then ConInt gives the contradiction.
--
-- Needs: encodeTA-correct for ALL ProofTA constructors.
-- We have it for axRefl, axK, axS (in TreeArith).
-- Need it for mp, gen, inst.

-- Fuel arithmetic helpers
private
  natMaxB : Nat -> Nat -> Nat
  natMaxB zero m = m
  natMaxB (suc n) zero = suc n
  natMaxB (suc n) (suc m) = suc (natMaxB n m)

-- checkTA monotonicity (same pattern as checkG-mono but for checkTA)
-- We need: checkTA n c = just A -> checkTA (suc n) c = just A
-- This is provable but requires the same 6-tag case analysis as checkG-mono.
-- For brevity, we assume it here and note it can be proved by the same method.

-- ACTUALLY: we can avoid fuel monotonicity entirely by using a SINGLE
-- fuel level for the whole proof. encodeTA-correct returns a Sigma
-- with the fuel, and we lift everything to the max fuel.

-- Simpler approach: prove encodeTA-correct by induction on ProofTA,
-- returning the needed fuel.

-- D1 for axioms (wrapped as Sigma)
encodeTA-correct-axRefl : (c : Code) ->
  Sigma Nat (\ k -> Eq (checkTA k (encProofTA (axReflTA c))) (just (feqTA c c)))
encodeTA-correct-axRefl c = mkSigma (suc zero) (encodeTA-axRefl c)

encodeTA-correct-axK : (A B : FormTA) ->
  Sigma Nat (\ k -> Eq (checkTA k (encProofTA (axKTA A B))) (just (fimpTA A (fimpTA B A))))
encodeTA-correct-axK A B = mkSigma (suc zero) (encodeTA-axK A B)

encodeTA-correct-axS : (A B C : FormTA) ->
  Sigma Nat (\ k -> Eq (checkTA k (encProofTA (axSTA A B C)))
    (just (fimpTA (fimpTA A (fimpTA B C)) (fimpTA (fimpTA A B) (fimpTA A C)))))
encodeTA-correct-axS A B C = mkSigma (suc zero) (encodeTA-axS A B C)

-- Full D1 for ALL constructors (encodeTA-correct : ProofTA A -> Sigma Nat ...)
-- requires checkTA fuel monotonicity for the mp/gen/inst cases.
-- This is ~100 lines of mechanical tag-by-tag case analysis,
-- identical to checkG-mono + encodeBaseG-fuel in ChwistekGodel2Genuine.agda.
-- For Stage B, D1 is proved for axioms. The recursive cases are
-- documented as requiring the same established pattern.

-- What we CAN prove easily: the definitions + the directions that
-- don't need heavy machinery.

------------------------------------------------------------------------
-- R3 analysis (trivial in Hilbert systems)
------------------------------------------------------------------------

-- In TreeArith (Hilbert-style), there is no cut constructor.
-- ALL proofs are "normal" (cut-free).
-- So R3 = "no normal proof proves fbot" = "no proof proves fbot" = ConExt.

-- Define "normal" (no cut = always true in Hilbert):
normalTA : {A : FormTA} -> ProofTA A -> Set
normalTA _ = UnitTA  -- ALL proofs are normal (no cut in Hilbert)

-- R3: no normal proof proves fbot
R3TA : Set
R3TA = (prf : ProofTA fbotTA) -> normalTA prf -> EmptyB

-- Con -> R3 (trivial)
con-to-r3 : ConExt -> R3TA
con-to-r3 con prf _ = con prf

-- R3 -> Con (trivial: every proof is normal)
r3-to-con : R3TA -> ConExt
r3-to-con r3 prf = r3 prf ttTA

-- R3 ↔ Con (both directions)
data PairB (A B : Set) : Set where
  mkPairB : A -> B -> PairB A B

r3-iff-con : PairB (R3TA -> ConExt) (ConExt -> R3TA)
r3-iff-con = mkPairB r3-to-con con-to-r3

------------------------------------------------------------------------
-- Summary of what Stage B establishes
------------------------------------------------------------------------

-- PROVED:
-- 1. ConExt (external consistency): via GoodTA soundness ✓
-- 2. R3 ↔ ConExt: trivial (Hilbert = all normal) ✓
-- 3. D1 for axRefl, axK, axS: in TreeArith ✓
--
-- NOT YET PROVED (needs ~100 lines each):
-- 4. Full D1 for mp/gen/inst: needs checkTA-mono (fuel monotonicity)
-- 5. checkTA-sound: if checkTA accepts, then GoodTA holds
-- 6. ConInt ↔ ConExt: needs either full D1 (for one direction)
--    or checkTA-sound (for the other direction)
--
-- The gap is MECHANICAL (fuel monotonicity + tag-by-tag case analysis),
-- not conceptual. The same pattern exists in ChwistekGodel2Genuine.agda
-- (checkG-mono, encodeBaseG-fuel) and was completed there.
