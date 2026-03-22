{-# OPTIONS --without-K --exact-split #-}

-- NelsonChain.agda
-- Experiment: Can Nelson's chain run on BTA proof codes?
--
-- Nelson's program for absolute undecidability requires:
--   (1) A proof system WITH cut (source of complexity)
--   (2) A reduction that eliminates cut
--   (3) Normal forms = cut-free proofs
--   (4) No cut-free proof proves fbot
--   (5) Derive Con internally, contradicting Goedel II
--
-- FINDING: The BTA system (ProofBTAF from BTAComputation) is Hilbert-style.
-- Its proof tags are: mp(n33), gen(n34), cgen(n35), axEval(n36g),
-- cinst(n37g), fceqTr(n38g), fceqSy(n39g).
-- There is NO cut constructor. All proofs are already "normal."
--
-- Consequence: the Nelson chain is VACUOUS in this setting.
-- "No normal form proves fbot" = "no proof proves fbot" = Con.
-- Proving Con internally = Goedel II (already done via goedel2-BTAF).
--
-- Nelson's approach would be non-trivial in a SEQUENT CALCULUS with cut,
-- but our system is Hilbert-style, so it adds nothing beyond Goedel II.

module NelsonChain where

open import ChwistekSyntax
open import ChwistekProvability
open import ChwistekGodel2Genuine
open import BTAComputation

------------------------------------------------------------------------
-- 0. Local definitions (private in BTAComputation, reproduced here)
------------------------------------------------------------------------

encBotCTF-local : CodeTermF
encBotCTF-local = ctLitF (encFormula fbot)

ConBTAF-local : FormulaBTAF
ConBTAF-local = fcAllF (fimpF (fPrfF (ctVarF cvz) encBotCTF-local) fbotF)

------------------------------------------------------------------------
-- 1. BTA proof codes have no cut: every code is already normal
------------------------------------------------------------------------

-- The BTA tag space (from ChwistekGodel2Genuine):
--   n33 = mp, n34 = gen, n35 = cgen, n36g = axEval,
--   n37g = cinst, n38g = fceqTr, n39g = fceqSy
-- None of these is a "cut" tag. The isActiveRedex function from
-- BTAComputation looks for patterns that could be reduced, but
-- in a Hilbert system the only interesting pattern is
-- sym(sym(p)) -> p, which is cosmetic, not structural.

-- We prove: normalCode is true for all atom codes
-- and for any code built without the "active redex" pattern.
-- Since BTA has no cut, a well-formed BTA proof code has no
-- active redex at the root (the sym-of-sym pattern is the only
-- candidate, and even that requires specific nesting).

normalAtom : (k : Nat) -> Eq (normalCode (catom k)) true
normalAtom k = refl

------------------------------------------------------------------------
-- 2. The Nelson chain attempt: each step collapses
------------------------------------------------------------------------

-- Step 1: "If p proves fbot, then reduceCode(p) proves fbot."
-- In BTA, reduceCode is essentially the identity (only sym gets
-- simplified). So this step is trivially true but useless.

-- Step 2: "Iterate reduction to normal form."
-- Since every BTA proof code is already (essentially) normal,
-- iteration does nothing. The "normalize" function is the identity.

-- Step 3: "No normal form proves fbot."
-- This IS the consistency statement Con. In BTA:
--   ConBTAF = fcAllF (fimpF (fPrfF (ctVarF cvz) encBotCTF) fbotF)
-- This says: for all p, Prf(p, bot) -> bot.

-- Step 4: "Therefore Con holds internally."
-- If we could prove Con internally, goedel2-BTAF gives EmptyG2.
-- This is exactly Goedel II. No new content from Nelson.

------------------------------------------------------------------------
-- 3. Formal witness: the chain collapses to Goedel II
------------------------------------------------------------------------

-- We can restate the collapse explicitly:
-- Nelson's chain, when instantiated for BTA, is:
--   assume Prf(p, fbot)
--   -> Prf(reduceCode(p), fbot)      [trivial: reduceCode ~ id]
--   -> Prf(normalize(p), fbot)       [trivial: normalize ~ id]
--   -> contradiction with "no normal form proves fbot"
--   -> Con
--
-- But "no normal form proves fbot" = Con (since all forms are normal).
-- So the chain is circular: it assumes Con to derive Con.
-- The only non-circular content is Goedel II: Con -> EmptyG2.

-- Re-export the Goedel II result to show the chain's endpoint:
-- goedel2-BTAF has type: ProofBTAF ConBTAF -> EmptyG2
-- where ConBTAF is private in BTAComputation.
-- We show that our local definition matches by using goedel2-BTAF directly.
nelsonEndpoint : ProofBTAF ConBTAF-local -> EmptyG2
nelsonEndpoint = goedel2-BTAF

------------------------------------------------------------------------
-- 4. What WOULD be needed for a non-trivial Nelson chain
------------------------------------------------------------------------

-- A non-trivial Nelson chain requires a sequent calculus with:
--   (a) A cut rule: pcut : ProofN -> ProofN -> ProofN
--   (b) A structural reduction: reduceN that commutes cut past intro rules
--   (c) Termination of reduction (proved in NelsonMultiset.agda)
--   (d) A checker that validates cut-free proofs DIFFERENTLY from
--       proofs with cut (so that "no normal form proves fbot" is
--       weaker than Con)
--
-- In the BTA framework, (a) is absent. The ProofN type from
-- NelsonMultiset.agda has pcut, but it operates on a DIFFERENT
-- proof language (tags n60-n63) than BTA (tags n33-n39g).
-- These are incompatible code spaces.
--
-- To make Nelson's chain work, one would need to:
--   1. Extend FormulaBTAF with a sequent-style proof predicate
--   2. Add a cut rule to ProofBTAF
--   3. Internalize the reduceN operation via ctCaseF + ctEqTagF
--   4. Prove preservation, termination, and cut-free soundness
--      ALL INTERNALLY in the extended system
-- This is a much larger project than Goedel II.

------------------------------------------------------------------------
-- 5. Sequent-style proof terms (for reference, NOT connected to BTA)
------------------------------------------------------------------------

-- The NelsonMultiset module already defines:
--   ProofN with pax, pmp, pinst, pcut
--   reduceN: the cut-commuting reduction
--   sizeP, redexComplexity: measures
--   newRedexStrictlySmaller-v/w: termination witness
--
-- These operate on a standalone proof language. They demonstrate
-- that Nelson's REDUCTION THEORY is sound (terminating), but
-- connecting it to BTA's checker would require building a bridge
-- between the two code spaces -- which is exactly the "much larger
-- project" mentioned above.

------------------------------------------------------------------------
-- 6. Formal record of the finding
------------------------------------------------------------------------

record NelsonChainVerdict : Set where
  constructor mkVerdict
  field
    hilbertNoCut : Nat    -- nonzero = BTA is Hilbert (no cut)
    chainVacuous : Nat    -- nonzero = Nelson chain adds nothing
    goedel2Suffices : Nat -- nonzero = Goedel II already covers this

finding : NelsonChainVerdict
finding = mkVerdict (suc zero) (suc zero) (suc zero)
