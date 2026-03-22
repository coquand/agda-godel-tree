# TreeArith Status: Complete Analysis

## Completed Stages

| Stage | File | Lines | Status |
|-------|------|-------|--------|
| A | TreeArith.agda | 525 | Complete: defined checker, formulas, proofs |
| B | TreeArithB.agda | 572 | Complete: full D1, checkTA-mono, checkTA-sound, ConInt ↔ ConExt |
| C | TreeArithC.agda | 123 | Complete: D3 NOT FORMULABLE (no existentials) |

## D3 Obstruction Chain

D3 requires THREE things, each necessary, none alone sufficient:

### Layer 1: Existential quantification
FormTA has only `fallTA` (universal). Need `fexTA` (existential)
to express "there exists a proof code."
STATUS: Not in current FormTA. Easy to add (~20 lines).

### Layer 2: Internal computation on code variables
Need ctCase + ctFold to compute checkTA inside formulas for
VARIABLE codes (not just specific literals).
STATUS: Not in current FormTA. Defined in BTAComputation.agda
for the BTA system. Needs ~80 lines to add to TreeArith.

### Layer 3: Representability of checkTA
Need the system to prove that its own checker computation is
correct — i.e., that the internal checker (defined via ctCase +
ctFold) agrees with the external checkTA.
STATUS: This IS Track 1 (TRACK1-PLAN.md). Estimated 6-10 hours.

## The Open Question

Track 1 is VERY LIKELY sufficient for D3, but this has NOT been
proved. The gap:

1. Track 1 defines an internal checker `checkCT` using ctCase + ctFold.
2. `checkCT` agrees with `checkTA` on closed codes (by construction).
3. But D3 requires the system to PROVE this agreement uniformly —
   not just for closed codes, but as an internal theorem.

"Definitional equality at the meta-level" (checkCT computes the
same thing as checkTA) does NOT automatically give the internal
theorem needed for D3. There are two separate things:

(a) DEFINITION: the internal checker term exists and computes correctly.
(b) PROOF-THEORETIC ADEQUACY: the system proves the right formulas
    about that checker, uniformly enough for D3.

These are close but not identical. The gap between (a) and (b)
might contain a surprise.

## What Remains

The ONLY way to resolve this: complete Track 1 and test D3 directly.

Track 1 tasks:
A. Define internal checker `checkCT` using ctCase + ctFold
B. Prove external correctness: eval(checkCT(c)) = checkTA(c) for closed c
C. Extend FormTA with existentials
D. State D3 exactly for the internal provability predicate
E. Attempt to prove D3
F. If the proof fails, identify the exact missing lemma

Estimated: 6-10 hours (TRACK1-PLAN.md).

Possible outcomes:
- Case A: Track 1 completed and D3 proved → Goedel II applies, Nelson gives Con → Con
- Case B: Track 1 completed but D3 still fails → deeper obstruction discovered
- Case C: Track 1 cannot be completed as intended → architectural issue
- Case D: Track 1 completed but needs an extra representability lemma → precise gap identified

## Remaining Work

Track 1 (TRACK1-PLAN.md): 6-10 hours of implementation.
This would complete the picture by making D3 provable, at which
point ALL standard Goedel II machinery applies.

The work is mechanical (define checkTA as ctCase + ctFold CodeTerm,
prove it agrees with the external checkTA). The architecture is
fully designed. The implementation follows the established patterns
from checkG-mono, encodeBaseG-fuel, sd-meta-correct.
