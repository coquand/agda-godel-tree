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

## Why No Weak Provability Notion Suffices

The remaining open question: is there a predicate P(p) weaker than
"checkG accepts p" but strong enough for Nelson's contradiction?

P would need to be:
1. Weaker than the checker (not replicate checkG)
2. Preserved under reduction: P(p) -> P(reduceN(p))
3. Excludable from normal forms: normal(p) -> not P(p)

Candidates considered:

(a) LOCAL CONTRADICTORY PATTERN: proof codes don't carry formula
    information in their tags — tags encode RULES (mp, cinst, etc.),
    not FORMULAS (fbot, fimp, etc.). No syntactic code property
    correlates with "proves fbot" without computing what the
    checker computes.

(b) FRAGMENT PROVABILITY: even a restricted checker for some tags
    is still a checker — it processes tag structure and sub-proof
    results.

(c) MONOTONE STRUCTURAL PREDICATE: the SHAPE of a code tree does
    not determine what formula it proves. The formula is the
    checker's OUTPUT, computed from the code's CONTENT. Shape and
    content are connected only through the checker.

The fundamental issue: what a proof proves is a SEMANTIC property
(determined by the checker), not a SYNTACTIC one (determined by
code shape). Any reduction-stable approximation of this semantic
property must replicate (some of) the checker's computation.

Therefore: there is no useful intermediate between "no semantics"
and "checker axioms." The compositional checker axioms ARE the
minimal bridge, and they are irreducible.

## Does Track 1 Yield Absolute Contradiction?

If Track 1 succeeds (ctCase + ctFold, internal checker defined),
the Nelson chain becomes:

1. Assume Prf(p, fbot) — some code proves fbot
2. Prf(reduceN(p), fbot) — preservation under reduction
3. Prf(normalize(p), fbot) — iterate to normal form
4. normal(p) → ¬Prf(p, fbot) — no normal form proves fbot
5. Contradiction: ¬Prf(p, fbot) for all p

Step 4 is decisive. Can we prove "no normal form proves fbot"?

A normal form has no active cut-pmp redexes but can still have
pmp/pinst/pax nodes. Whether it proves fbot depends on whether
the AXIOMS and LOGIC allow chaining to fbot.

If the axiom set is CONSISTENT: no normal form proves fbot. But
"the axiom set is consistent" IS the consistency statement Con.

So the chain gives: Con → ¬∃p.Prf(p, fbot) = Con → Con.
This is TAUTOLOGICAL, not an absolute contradiction.

To get an absolute contradiction (⊥ with no assumptions), we
would need step 4 WITHOUT assuming consistency — which requires
the system to be inherently consistent by construction. In our
tiny ProofN this holds trivially (too weak). In a real system
with self-reference, normal forms CAN prove fbot if the system
IS inconsistent.

CONCLUSION: Track 1 gives a clean framework where Nelson's chain
CAN BE RUN, producing Con → Con (Gödel-style), not ⊥ (Nelson-style).
The absolute contradiction only follows if the system is actually
inconsistent — which ours is not (proved via GoodBTA soundness).

This is Case A (Gödel-style conditional), not Case B (Nelson-style
absolute). Track 1 uses Gödel-like machinery and produces
Gödel-like results. Nelson's hope for absolute contradiction
from syntax alone is not realized.

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
