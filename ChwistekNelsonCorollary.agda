{-# OPTIONS --without-K --exact-split #-}

module ChwistekNelsonCorollary where

open import ChwistekSyntax
open import ChwistekProvability
open import ChwistekCodeLogic
open import ChwistekCodeQuant
open import ChwistekGodelSentence
open import ChwistekGodelProof
open import ChwistekSoundness
open import ChwistekProofExt
open import ChwistekReflectionHierarchy
open import ChwistekFuelChecker
open import ChwistekFuelGodel
open import ChwistekFuelGodel2

------------------------------------------------------------------------
-- Nelson-style reading of the formalization
------------------------------------------------------------------------

-- Nelson (2013/2015) observed that in PRA, the bounds in the
-- Hilbert-Ackermann consistency theorem depend on rank and level
-- but NOT on the length of the proof. For each specific proof,
-- the system can verify the needed bounds. The gap between
-- this instance-by-instance verification and universal consistency
-- is what Nelson planned to exploit via the Kritchman-Raz method.
--
-- Our formalization makes this gap precise in two ways.

------------------------------------------------------------------------
-- 1. INSTANCE VERIFICATION (available)
------------------------------------------------------------------------

-- For each specific proof code p accepted by the bounded checker,
-- the system can internally certify what p proves.
-- This is represent-fuel, rephrased.

instance-verified :
  (p : Code) (A : Formula) (n : Nat) ->
  Eq (checkProofN (suc n) p) (just A) ->
  Sigma Code (\ q ->
    Eq (checkProofN (suc (suc (suc n))) q)
       (just (fceq (ccheck (clit p)) (clit (encFormula A)))))
instance-verified = D1-fuel

-- Moreover, this can be iterated (D3): the system can certify
-- that its own certification is certified.

instance-verified-iterated :
  (p : Code) (A : Formula) (n : Nat) ->
  (hyp : Eq (checkProofN (suc n) p) (just A)) ->
  Sigma Code (\ q ->
    Eq (checkProofN (suc (suc (suc (suc (suc n))))) q)
       (just (fceq (ccheck (clit (sigFst (D1-fuel p A n hyp))))
                   (clit (encFormula (fceq (ccheck (clit p))
                                          (clit (encFormula A))))))))
instance-verified-iterated = D3-fuel

------------------------------------------------------------------------
-- 2. UNIVERSAL CONSISTENCY (not available internally)
------------------------------------------------------------------------

-- Con = "for all proof codes p, checkProof(p) != encFormula(fbot)"
-- This is a SINGLE formula with a universal quantifier over codes.
-- It cannot be derived from instance verification alone.

-- The reason: to prove fcAll body via cgenN, one needs to prove
-- body for a GENERIC code variable, not a specific literal.
-- But ax-eval (and hence instance-verified) only works for
-- CLOSED code expressions — it cannot produce fceq facts
-- about code variables.

-- This is the formal content of the gap Nelson identified:
-- the system verifies each instance but cannot universally
-- quantify over them.

------------------------------------------------------------------------
-- 3. THE GAP IS THE GOEDEL-II BARRIER
------------------------------------------------------------------------

-- Our Goedel I (stratified): goedel1-final proves GoedelSentence
-- is not provable, without assumptions.
--
-- Our hierarchy theorem: evalCExp-blind-to-ax-eval proves the
-- stratified system's reflection is strictly one-level-down.
--
-- Our fuel-based D1/D3: instance verification works at all
-- levels, even self-referentially.
--
-- But the passage from "each given proof code can be checked"
-- to "no proof code yields contradiction" requires universal
-- internal soundness — the Goedel-II step.

-- The following types make the gap explicit:

-- What we HAVE: for each p, if the checker accepts p, we can
-- internally represent what p proves.
InstanceReflection : Set
InstanceReflection =
  (p : Code) (A : Formula) (n : Nat) ->
  Eq (checkProofN (suc n) p) (just A) ->
  Sigma Code (\ q ->
    Eq (checkProofN (suc (suc (suc n))) q)
       (just (fceq (ccheck (clit p)) (clit (encFormula A)))))

-- What we NEED for Goedel II: a proof of Con inside the system.
-- This requires universal quantification, not just instances.
InternalConsistency : Nat -> Set
InternalConsistency n =
  ProofN n Con

-- The first is inhabited:
instance-reflection-holds : InstanceReflection
instance-reflection-holds = D1-fuel

-- The second is the open problem (Goedel II barrier).
-- It cannot be derived from InstanceReflection alone because
-- InstanceReflection gives facts about SPECIFIC codes,
-- while InternalConsistency quantifies over ALL codes.

------------------------------------------------------------------------
-- 4. CONNECTION TO NELSON'S PROGRAM
------------------------------------------------------------------------

-- Nelson's planned argument:
--   1. Build a system S* that proves its own "open consistency"
--   2. Use Kritchman-Raz to derive contradiction from self-consistency
--   3. Conclude PRA is inconsistent
--
-- Buss-Tao identified the gap in step 2: the disproof of later
-- stages "seems to require an assumption that S* is consistent"
-- — which is circular.
--
-- Our formalization explains this gap precisely:
--   - Step 1 corresponds to instance verification (D1/D3)
--   - Step 2 requires lifting instances to universal consistency
--   - This lifting IS the Goedel-II step
--   - The circularity Buss-Tao identified is exactly the need
--     for internal soundness that Goedel II prohibits
--
-- In the fuel-based architecture:
--   - Instance verification works (represent-fuel, D1-fuel, D3-fuel)
--   - But InternalConsistency n (= ProofN n Con) remains open
--   - The passage from one to the other is the precise barrier
--
-- In the stratified architecture:
--   - Even instance verification has limits (blind to tag 36)
--   - The hierarchy is strict (proved)
--   - This corresponds to Chwistek's metasystem separation
--
-- COROLLARY (Nelson-style reading):
--   In a syntax-first formalization with explicit proof-checking,
--   bounded instance verification of concrete proofs can be
--   internalized (InstanceReflection is inhabited), but lifting
--   this to a universal internal consistency assertion
--   (InternalConsistency) requires stronger reflection principles
--   than the system can justify for itself. The passage from
--   "each given proof code can be checked" to "no proof code
--   yields contradiction" is precisely the Goedel-II step.
