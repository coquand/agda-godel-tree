# Nelson Program Analysis: Structural Dynamics vs Semantic Termination

## Summary of Experiments

| File | What it tests | Result |
|------|--------------|--------|
| NelsonDecomp.agda | Decomposition axioms | Layer 1 of barrier (axioms needed) |
| BTACtCase.agda | ctCase alone | Necessary but insufficient |
| NelsonCutCommute.agda | Cut-commuting reduction | Rank CAN increase; backtrackP preserved (typed level) |
| NelsonReduction.agda | Full reduction theory on Code | backtrackP NOT preserved at Code level |

## The Three-Layer Picture

### Layer 1: Local Dynamics (STRUCTURAL)

- One-step reduction
- Bounded iteration
- Local invariant preservation (on typed proof objects)

This is genuinely structural. No checker, no semantics.
Works with backtrackP on typed ProofN.

### Layer 2: Global Control (INTERMEDIATE)

- Identifying active redexes
- Showing unresolved activity decreases
- Guiding repeated reduction

This is NOT mere syntax-rearrangement, but NOT yet a full checker.
It requires a notion of **operationally meaningful proof structure**.

### Layer 3: Proof Semantics (SEMANTIC)

- Relating code to "is a proof"
- Relating reduction to correctness / contradiction
- Full checker semantics

This is where Goedel II lives.

## The Key Surprise

backtrackP is preserved on typed ProofN (by refl) but CAN INCREASE
on raw Code. The tag-dispatch encoding breaks the structural
correspondence.

This means: **backtrackP is not a Code invariant. It is a typed
interaction invariant.** It lives on structured proof objects,
not on arbitrary syntax trees.

## What This Says About Nelson

Nelson works syntactically, but not on arbitrary syntax. His program
tacitly depends on a structured proof universe. The invariant
(rank/level in his case, backtrackP in the Aschieri-improved version)
is stable only on objects understood as proofs, not on raw encodings.

The failure at raw Code level tells us: the right setting is not
raw tree codes alone, but **codes equipped with enough structure
to recover typed interaction**.

## The Missing Middle Layer

The boundary is not between "structural" and "semantic" but between
three levels:

```
raw Code  <  structured proof code  <  full checker semantics
```

The structured middle layer would be:
- A predicate `Structured : Code -> Set` capturing enough local
  proof shape to interpret backtrackP meaningfully
- Weaker than a full checker (doesn't verify correctness of proofs)
- Stronger than raw Code (recovers the typed interaction structure)
- Enough for reduceCode to preserve backtrackP

## The Precise Verdict on Nelson

**Strong positive**: Nelson's program can support a substantial
structural theory of proof reductions without a checker (Layer 1).

**The gap**: Global convergence requires a theory of active proof
structure (Layer 2), not just code transformation. In the current
encoding, active structure is visible on typed proofs but not on
raw codes.

**The obstacle is not simply "iteration" or "semantics"**: it is
the loss of operational structure under code encoding.

## Relationship to Goedel II

- Layer 1 (local dynamics): works without Goedel considerations
- Layer 2 (global control): this is where Nelson's program must
  confront the question of whether it can avoid reconstructing
  a checker. The structured middle layer is the test.
- Layer 3 (full semantics): this is where Goedel II lives. Our
  BinaryTreeArith.agda proves Goedel II at this level using
  compositional checker axioms.

## Next Experiment

The most informative next test: can we define a `Structured : Code -> Set`
predicate that is:
1. Weaker than full checker acceptance
2. Strong enough to recover backtrackP preservation
3. Preserved by reduceCode
4. Sufficient for termination analysis

If YES: Nelson's program survives with the structured middle layer.
If NO: the structured layer inevitably collapses into full checking.
