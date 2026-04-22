# Soundness notes: `ruleInst` side condition

## Issue

`Guard.Step.ruleInst` as declared:

```agda
ruleInst : (x : Nat) (t : Term) {eq : Equation} ->
           Deriv hyp eq -> Deriv hyp (substEq x t eq)
```

has **no side condition** preventing substitution of a variable `x` that is
free in the hypothesis `hyp`. Under a semantic interpretation of
`Deriv hyp eq` as "for all values of free variables, hyp implies eq",
`ruleInst` is **unsound** when `x ∈ free(hyp)`:

- From `∀x. hyp(x) → eq(x)`, `ruleInst x t` gives `∀x. hyp(x) → eq(x)[x:=t]`.
- The conclusion's `x` binding is replaced with `t`, but hyp's `x` still ranges
  universally. This is not a valid consequence of the original.

Standard Hilbert-style systems (including Guard 1963 BRA, page 10-11,
Exercise 19) require the substitution rule to satisfy the side condition
**x not free in the hypothesis**.

## Audit of existing `ruleInst` call sites

Scanning all non-comment uses of `ruleInst` in `Guard/`:

### SOUND (side condition satisfied)

| File | Line | hyp | Notes |
|---|---|---|---|
| `Guard/GodelIClassical.agda` | 158 | `Triv = eqn O O` | Closed, no free var. ✓ |
| `Guard/GodelITriv.agda` | 131, 135, 140 | `Triv` | Closed. ✓ |

### CONDITIONAL (polymorphic-hyp wrapper functions)

These wrap `ruleInst` in a function that takes `hyp : Equation` as parameter.
Soundness depends on *caller's* choice of hyp.

| File | Function | Side condition |
|---|---|---|
| `Guard/TreeEqSelf.agda` | `treeEqSelf` | Caller must ensure `var 0 ∉ free(hyp)` |
| `Guard/ImpTSchemaF.agda` | `impTSelf`, `impTAnyTrueT` | Caller must ensure `var 0 ∉ free(hyp)` |

When called at `hyp = Triv` (as `godelIClassical` does internally via
`treeEqSelf (reify cGSCR)`): **sound**.

When called at `hyp = gsCR` or similar hyp with var 0 free: **unsound**.

### UNSOUND by side condition (hyp has free x)

| File | Line | hyp | Substituted var | Notes |
|---|---|---|---|---|
| `Guard/GodelIIRose.agda` | 83 | `godelSentenceV3` (has var 0) | 0 | Called in `conToBotRose`. |
| `Guard/GodelIIV3.agda` | 53 | similar | 0 | Called in `conToBotV3`. |
| `Guard/GodelIV3.agda` | 145, 148, 152, 158 | generic hyp parameter | v2, v11', v12', 0 | Called in `godelIDerivV3`. |
| `Guard/GodelIIClassicalSkel.agda` | 99 | generic `hyp` | 0 | Skeleton (abandoned). |
| `Guard/EncCorrPfAnalysis.agda` | 134 | generic | 0 | Analysis scratch. |

### Infrastructure (structural recursion on ruleInst)

| File | Line | Role |
|---|---|---|
| `Guard/Step.agda` | 136 | Definition. |
| `Guard/DerivLift.agda` | 72 | Preserves hyp; inherits soundness. |
| `Guard/RoseLemma1.agda` | 662 | Pattern match in induction. |
| `Guard/RoseLemma1T.agda` | 617 | Pattern match. |
| `Guard/Thm14EV3.agda` | 2471 | Pattern match. |

These don't *use* ruleInst unsoundly per se — they preserve or pattern-match it.

## Consequence for Gödel II (this session)

For the **meta-level Gödel II proof** (following Guard 1963 Th 14), we use
`godelIClassical` at its native type `Deriv Triv gsCR → Deriv Triv bot`. All
internal `ruleInst` calls are at `hyp = Triv`, which is sound. **No
polymorphic lift of `godelIClassical` is used.**

The Provable layer's `fromDeriv` embedding accepts only polymorphic Derivs.
For our Gödel II chain, the polymorphic Derivs we lift are axiom applications
(`axRefl`, `axGoodstein`, `axI`, etc.) and `treeEqRefl` (which doesn't use
ruleInst). These are sound.

**We do not lift or rely on** `GodelIIRose`/`GodelIIV3` (which exhibit the
unsound-side-condition pattern). Those modules are historical / alternative
approaches not used in the current Gödel II path.

## Recommended follow-up (separate project)

1. **Option A**: modify `ruleInst` signature to require proof
   `Eq (substEq x t hyp) hyp` (propositional equality). Every existing
   sound callsite gets `refl` trivially (for closed hyps); every unsound
   callsite fails to typecheck, surfacing the unsoundness.
   Cascade through polymorphic wrappers (`treeEqSelf`, `impTSelf`, etc.)
   by threading the proof through their signatures.
   Estimate: 3-5 sessions.

2. **Option B**: add `ruleInstSafe` as a second constructor with the side
   condition; existing `ruleInst` remains permissive but is flagged as
   deprecated for new work. Less disruptive; partial safety.
   Estimate: 1 session + migration of new work to `ruleInstSafe`.

3. **Option C** (current): audit + document. No code change. This file.

## Status

- Audit: complete.
- Documentation: this file.
- Gödel II at meta level: proceeds using sound-hyp uses only.
