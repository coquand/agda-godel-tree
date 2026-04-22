# UNIFIED-DESIGN Rev 1: Thm14EV3 stays on old Deriv

## Problem surfaced in [unify-3b]

Porting `Guard.Thm14EV3` (the thm14EV3 recursor that takes a Deriv proof
and produces an encoded ProofE3 record) to the hyp-less `Guard.DerivF`
hit a fundamental Agda-splitting issue:

The top-level recursor signature would be
```agda
thm14EV3 : {H eq : Equation} -> Deriv (atomic eq) -> ProofE3 H eq
```
with pattern-matching on each `Deriv` constructor.  The
`ruleInst` constructor in `DerivF` has type
```agda
ruleInst : (x : Nat) (t : Term) {P : Formula} ->
           Deriv P -> Deriv (substF x t P)
```
Pattern-matching on `ruleInst x t {P} d` against an outer target
`Deriv (atomic eq)` requires Agda to unify
`substF x t P ≟ atomic eq` — which is stuck under `--without-K`
because `P` is unbound and `substF` doesn't reduce without it.  Even
specifying `{P = atomic eq'}` in the pattern doesn't help: Agda tries
the index unification before looking at the nested constructor.

Error: `SplitError.UnificationStuck`.

`--without-K` is a project-wide invariant (required by CLAUDE.md), so
enabling K isn't an option.  Nested views / DerivE-style wrappers
would require redoing the full Deriv data type.

## Revision

**`Guard.Thm14EV3` stays on old `Guard.Step.Deriv` (hyp-carrying).**

- The unified `Guard.DerivF` is correct for user-facing reasoning
  (Gödel I, Gödel II, BRA chain steps).
- The `Guard.Thm14EV3` recursor is an internal "encoding" helper.
  Its users (godelIIV3 in the V3 track; Thm 14's chain analog in
  the unified track) CONSTRUCT their proof in old `Deriv` form (or
  at least a polymorphic-hyp form suitable for the old data type),
  pass it through `thm14EV3` to get an encoded proof term, then
  embed the encoded result into DerivF via a trivial atomic
  embedding.

## Bridge

Define:
```agda
atomicEmbed : {eq : Equation} ->
              ({h : Equation} -> OldDeriv h eq) ->
              DerivF.Deriv (atomic eq)
```

This is trivial (one case per old-Deriv constructor → new-DerivF
constructor).  It works fine without pattern-matching subtleties
because we're going FROM old `Deriv` TO new `Deriv`, and the old
Deriv's `ruleInst` just maps to the new `ruleInst` (no index
unification issue — we're constructing, not destructing).

Users who need the encoded form of a Deriv proof:
1. Build the proof in old `Deriv` (polymorphic in hyp).
2. Apply `thm14EV3` to get `ProofE3 H eq`.
3. Use the encoded components in `DerivF`-level reasoning.

## What remains single-layered

Everything that isn't thm14EV3 / ProofE3:
- Gödel II chain steps: DerivF.
- Gödel I proof (`godelIClassical`): DerivF.
- Propositional axioms, mp, ruleInst, ruleIndBT: DerivF.
- Encoder correctness lemmas (encMpCorr, encRuleInstCorr, ...):
  DerivF.

## What stays on old Deriv

- `Thm14EV3.thm14EV3` itself.
- `ProofE3` record (for encoded proofs).
- The `Deriv`-parameterised helpers inside `Thm14EV3` (~80 local
  lemmas; too tightly coupled to port individually).

## Impact

- Plan's "delete Guard.Step / old Deriv in [unify-6]" becomes
  "keep Guard.Step and old Deriv indefinitely, but only as an
  internal encoding vehicle."
- Estimated line counts revise downward: we don't port ~2500 lines
  of Thm14EV3.
- Correctness: unchanged.  Both layers remain sound.

## Status of [unify-3]

- **[unify-3a] (shipped)**: ThFunTForV3Unify, ThFunTForCorrectDefsUnify,
  ThFunTForV3DefsUnify, ThFunTForV3PassUnify, PairPassthroughUnify.
- **[unify-3b] (shipped, this commit)**: ProofEncUnify (2674 lines,
  typechecks).
- **Thm14EV3**: intentionally NOT ported.  Stays on old Deriv.

## Next: [unify-4]

Migrate the Gödel I infrastructure at the DerivF layer:
- SubstTForPrecompClassical → SubstTForPrecompClassicalUnify.
- GodelIClassical → GodelIClassicalUnify.

These don't depend on thm14EV3's recursor structure; they reason
equationally and should port cleanly via the same sed approach used
in [unify-2] and [unify-3a].
