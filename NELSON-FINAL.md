# Nelson Program: Final Analysis

## The Complete Experimental Record

| File | Lines | Finding |
|------|-------|---------|
| NelsonDecomp.agda | 255 | Decomposition axioms work locally; ctCase needed for uniform case |
| BTACtCase.agda | 458 | ctCase necessary but insufficient without ctFold |
| NelsonCutCommute.agda | 259 | Rank CAN increase; cut-commuting is non-trivial |
| NelsonReduction.agda | 261 | Dynamics vs termination split; backtrackP fails at Code level |
| StructuredCode.agda | 236 | backtrackP increases on structured codes (counterexample: 2→3) |
| NelsonMultiset.agda | 275 | **Multiset control WORKS** (Dershowitz-Manna) |
| NelsonContradiction.agda | 238 | Contradiction trivial in weak system; needs semantics in strong system |

## The Three-Layer Structure

### Layer 1: Reduction Dynamics (STRUCTURAL)
- One-step reduction: pattern matching on code structure
- Active redex detection: purely syntactic
- Complexity assignment: sub-tree size
- **Status: completely solved, no semantics needed**

### Layer 2: Termination (STRUCTURAL)
- Multiset ordering on redex complexities (Dershowitz-Manna)
- Count may increase but max complexity strictly decreases
- Under max-first strategy: well-founded descent on Nat
- **Status: completely solved, no semantics needed**

### Layer 3: Contradiction (SEMANTIC)
- Requires connecting proof codes to what they prove
- The minimal bridge: compositional checker axioms (our BTA axioms)
- Or equivalently: a model where fbot = Empty and fPrf = Unit (GoodBTA)
- **Status: requires semantic content; no purely structural alternative**

## The Crucial Asymmetry

Goedel II and Nelson's program need DIFFERENT amounts of semantics:

| Goal | Needs |
|------|-------|
| Goedel II (model-theoretic) | Trivial interpretation (fPrf = Unit, fbot = Empty) |
| Nelson (structural contradiction) | Provability PRESERVED under reduction |

Goedel II works with almost no semantics: GoodBTA assigns UnitG2 to
every fPrf formula. No actual proof checking happens. The contradiction
comes from (Unit -> Empty) being uninhabited.

Nelson's program requires MORE: provesBot(p) -> provesBot(reduceN(p)).
This is a REDUCTION-STABLE notion of provability. And any such notion
necessarily reconstructs a proof checker, because it must track what
each proof rule does to the proved formula through each reduction step.

The boundary is NOT between "no semantics" and "semantics." It is:

```
Level 0: No meaning             → reduction works, contradiction vacuous
Level 1: Trivial interpretation  → Goedel II works (GoodBTA)
Level 2: Reduction-stable provability → Nelson works, but = checker
```

Level 1 suffices for Goedel II. Level 2 is needed for Nelson.
Level 2 collapses to a proof checker.

## The GoodBTA Insight

The GoodBTA valuation is the WEAKEST possible soundness:
- fPrf(p, c) = UnitG2 for ALL p and c
- fbot = EmptyG2
- fimp UnitG2 EmptyG2 = uninhabited

This makes ConBTA = fcAllA (fimpA (fPrf p encBot) fbotA) false:
(c : Code) -> UnitG2 -> EmptyG2 is uninhabited.

No checking happens. The contradiction is purely model-theoretic.
Yet it IS a valid proof of Goedel II (the theorem statement is correct).

## The Definitive Verdict on Nelson

### What Nelson gets right:
1. Proof reductions CAN be controlled structurally (multiset ordering)
2. Termination CAN be proved without a checker
3. Local proof dynamics ARE purely syntactic

### What Nelson cannot avoid:
4. The bridge from reduction to contradiction requires SOME semantic content
5. The minimal semantic content is the compositional checker axioms
6. There is no useful intermediate between "no semantics" and "checker axioms"

### The precise formulation:
Nelson's program fails not because it lacks a reduction theory,
but because it requires a notion of provability that is STABLE
UNDER REDUCTION — and any such notion necessarily reconstructs
a proof checker.

In contrast, Goedel II requires only a TRIVIAL interpretation
of proofs (fPrf = Unit), which is maximally weak and does not
interact with reduction at all.

The obstruction is not "semantics" in general, but specifically
"reduction-stable provability."

## Relationship to Guard

Guard's BRA includes primitive recursive representability, which
gives him both structural reduction AND the semantic bridge. His
system doesn't separate Layers 2 and 3 because representability
provides both.

Our development separates them cleanly:
- Multiset control (Layer 2) without representability
- Checker axioms (Layer 3) without full representability
- The gap between them is the representability work (~500 lines)

## Open Question

Can the compositional checker axioms be DERIVED from tree induction
+ a formula-level computation language (ctCase + ctFold)?

This is Track 1 (TRACK1-PLAN.md). If yes, the entire Goedel II
proof reduces to: tree induction + structural reduction + defined
checker. All three are structural principles. The "semantic content"
is the DEFINITION of the checker inside the formula language.

This would fully close the gap between Nelson's structural program
and Goedel II: the only semantic content needed is the checker
definition itself, expressed as a computable function on codes.
