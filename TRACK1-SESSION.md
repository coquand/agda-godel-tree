# Track 1 Session: Complete the Internal Checker and Test D3

## Context

This is a fresh session prompt for completing Track 1 of the
Chwistek/BTA incompleteness project. The full codebase is at
/Users/coquand/CHWISTEK/.

## What exists

- TreeArith.agda (525 lines): FormTA, ProofTA, checkTA (fuel-based,
  6-tag dispatch), encFormTA, decFormTA, encProofTA, GoodTA, soundTA,
  consistencyTA. Compiles clean.

- TreeArithB.agda (572 lines): checkTA-mono (fuel monotonicity),
  encodeTA-correct (full D1 for ALL constructors), checkTA-sound
  (checker soundness), ConInt ↔ ConExt, R3 ↔ ConExt. Compiles clean.

- TreeArithC.agda (123 lines): D3 NOT FORMULABLE in current FormTA
  (no existential quantifier). Compiles clean.

- TreeArithD3.agda (207 lines): Adding existentials alone is NOT
  sufficient for D3. Also needs ctCase + ctFold + representability.
  Compiles clean.

- TRACK1-PLAN.md: Detailed plan for the internal checker.

- BinaryTreeArith.agda (343 lines): Goedel II with 7 compositional
  checker axioms (not derived). goedel2-BTA compiles clean.

- SelfDestruct.agda: sd-meta-correct proved (sdCode is checker-admissible).

## What is NOT done

D3 (self-awareness): ⊢ Prov(A) → Prov(Prov(A))

This requires:
1. Existentials in the formula language
2. ctCase + ctFold for internal computation on code variables
3. Representability: the system proves facts about its own checker

Track 1 builds all three. But it has NOT been shown that Track 1
automatically yields D3. The gap between "internal checker agrees
with checkTA" and "the system proves D3 uniformly" is real.

## The prompt to use

```text
You are working in /Users/coquand/CHWISTEK/. Read these files first:
- TreeArith.agda
- TreeArithB.agda
- TreeArithC.agda
- TreeArithD3.agda
- TRACK1-PLAN.md

Goal: Complete Track 1 and test whether D3 actually follows.
This is a BUILD task. Do not summarize. Do not speculate.

Task A — Internal checker
1. Extend FormTA with:
   - fexTA (existential quantification over codes)
   - ctCase (case analysis: atom vs node)
   - ctFold (primitive recursion on Code)
   in a new formula/term language.

2. Define an internal checker term checkCT using ctCase + ctFold,
   mirroring checkTA's 6-tag dispatch.

3. Prove external correctness:
   for all closed codes c and fuel n,
   eval(checkCT applied to c) = checkTA n c
   (or the closest correct statement).

Task B — Internal provability
4. Define the internal provability formula:
   ProvF(A) = fexTA (fexTA (feqTA (checkCT fuel code) (encFormTA A)))
   (existentially quantified over fuel and code)

5. State D3 exactly:
   D3 = for all A, ProvF(A) → ProvF(ProvF(A))
   (or the closest correct formulation)

Task C — D3 audit
6. Attempt to prove D3 in the extended system.
7. If it fails, identify the EXACT missing lemma.
   Do not say "it needs representability" — say WHICH specific
   representability fact is missing.

Mandatory classification at the end:
Case A: Track 1 completed and D3 proved
Case B: Track 1 completed but D3 needs extra lemma (state it)
Case C: Track 1 cannot be completed as intended
Case D: D3 formulable but unprovable (state why)

Constraints:
- No postulates, no holes
- No endpoint summaries or philosophical discussion
- One compilable file (or minimal set)
- {-# OPTIONS --without-K --exact-split #-}
- Use private blocks liberally for type-checker performance
- No with clauses

The main deliverable is the FORMAL STATUS of D3 after Track 1.
If D3 fails, the deliverable is the exact missing lemma.
```

## Expected outcomes

Case A is unlikely (D3 proved would be very strong).
Case B is most likely (D3 needs a specific representability fact).
Case C would indicate an architectural problem.
Case D would be the deepest finding (D3 formulable but provably
unprovable would essentially be an internalized Goedel II).

## File dependencies

```
ChwistekSyntax.agda
ChwistekProvability.agda
ChwistekCodeLogic.agda
ChwistekSoundness.agda
    |
    v
TreeArith.agda (Stage A: checker, formulas, proofs)
    |
    v
TreeArithB.agda (Stage B: D1, mono, soundness, ConInt ↔ ConExt)
    |
    v
TreeArithC.agda (Stage C: D3 not formulable)
    |
    v
TreeArithD3.agda (Stage C2: existentials not sufficient)
    |
    v
TreeArithTrack1.agda (NEW: the Track 1 file to create)
```
