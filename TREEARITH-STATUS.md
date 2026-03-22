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

## The Definitive Answer

D3 is provable IFF Track 1 is completed.

Track 1 = ctCase + ctFold + defined internal checker. With Track 1:
- D3 is formulable (Layer 1 + Layer 2)
- D3 is provable (Layer 3: internal checker = checkTA by definition)
- Standard Goedel II applies (D1 + D2 + D3 all hold)
- Con is unprovable (Goedel II)
- Nelson's chain gives Con → Con (tautological, not absolute ⊥)

Without Track 1:
- D3 is not formulable (current state)
- Standard Goedel II route blocked
- Con still blocked by model-theoretic route (GoodTA)

## What This Means for Nelson

Nelson's program requires D3 (self-awareness) to have a chance of
proving Con internally. D3 requires representability of the checker.
Representability IS Track 1.

If Track 1 is completed:
- D3 holds
- Goedel II applies
- Nelson's chain gives Con → Con (NOT absolute ⊥)
- Nelson's program does not bypass Goedel II

If Track 1 is NOT completed:
- D3 is not formulable
- Standard Goedel II route doesn't apply
- But Con is STILL blocked (model-theoretic)
- Nelson's program still doesn't give absolute ⊥

Either way: Nelson's program does not produce absolute contradiction.
The only difference is WHETHER Goedel II applies (via D3) or whether
consistency is blocked by a different mechanism (model-theoretic).

## Remaining Work

Track 1 (TRACK1-PLAN.md): 6-10 hours of implementation.
This would complete the picture by making D3 provable, at which
point ALL standard Goedel II machinery applies.

The work is mechanical (define checkTA as ctCase + ctFold CodeTerm,
prove it agrees with the external checkTA). The architecture is
fully designed. The implementation follows the established patterns
from checkG-mono, encodeBaseG-fuel, sd-meta-correct.
