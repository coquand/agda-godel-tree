# Next Session: Classical Gödel II

## Setup

```
cd /Users/coquand/CHWISTEK
~/.cabal/bin/agda-2.9.0 <file>     # THIS binary, not /opt/homebrew/bin/agda
```

Repo: `https://github.com/coquand/agda-godel-tree.git`, branch `main`.
Last commit: `b4d3039` `[proofenc] Add encAxKT (n25) + ndDisp25V3Pub navigation`.

## What's done — Classical Gödel I (unchanged)

Commit `8229215`. See `Guard/GodelIClassical.agda`, `Guard/SubstTForPrecompClassical.agda`, `Guard/CodeOfReify.agda`. Ryan's Lemma 3 in tree form, `Triv`-based, one-free-variable `gsCR`.

## What's done — Architecture validation (April 2026 session)

### `Guard/GodelIIClassicalSkel.agda` (207 lines, 0.13s)

Parameterised module: takes `Phi : Fun1` and `strongPhiCorr : StrongPhiCorr Phi` as module arguments, derives classical Gödel II (positive and contrapositive). **Validates that the user's deviation (meta-level Agda arrow only; no object-level `→` in Deriv) is CONSISTENT with a feasible Gödel II proof**, given the right Phi + strongPhiCorr.

The `StrongPhiCorr` equation is:
```agda
StrongPhiCorr : Fun1 -> Set
StrongPhiCorr Phi =
  (v0 : Term) {hyp : Equation} ->
  Deriv hyp (eqn (ap2 TreeEq (ap1 (thmT trivCT) v0) (reify cGSCR))
                 (ap2 TreeEq (ap1 (thmT trivCT) (ap1 Phi v0)) codeBotT))
```

No IfLf, no ternary-tree implication. Just a raw Deriv-level equation between two TreeEqs.

### `Guard/ProofEnc.agda` (963 lines, 0.30s)

Eight combinators so far:

| Name              | Tag | Kind           | Used for                           |
|-------------------|-----|----------------|-------------------------------------|
| `encRuleSym`      | n18 | rule (1 sub)   | sym of a sub-proof                 |
| `encRuleTrans`    | n19 | rule (2 subs)  | transitivity chain                 |
| `encCongL`        | n21 | rule (1 sub)   | congL g x wrap                     |
| `encCongR`        | n22 | rule (1 sub)   | congR g x wrap                     |
| `encRuleInst`     | n23 | rule (1 sub)   | variable instantiation             |
| `encAxI`          | n0  | axiom (closed) | axI t                              |
| `encAxFst`        | n1  | axiom (closed) | axFst a b                          |
| `encAxSnd`        | n2  | axiom (closed) | axSnd a b                          |
| `encAxKT`         | n25 | axiom (closed) | axKT t x                           |

Each with polymorphic `{hyp}` correctness + tag-opaque `pass` property. All compile in 0.30s under `--safe --without-K --exact-split`.

### Published navigation helpers
`ndDisp18V3Pub`, `ndDisp19V3Pub`, `ndDisp21V3Pub`, `ndDisp22V3Pub`, `ndDisp23V3Pub`, `ndDisp25V3Pub` — copies of the private navigation helpers in `Thm14EV3.agda`.

## Key architectural insight (the big one)

Phi's construction can **reuse `thm14EV3` meta-level for CLOSED sub-derivations**. Specifically:

```agda
encSelfEq        : Term := encT (thm14EV3 (treeEqSelf (reify cGSCR)))
encDiagFTargetCR : Term := encT (thm14EV3 diagFTargetCR)
```

These are meta-level computations yielding specific closed Terms. Their correctness is inherited from `corr (thm14EV3 _)` — polymorphic in `hyp` — **no need to encode the treeEqSelf or diagFTargetCR derivation step by step**.

This cuts Phi's estimated line count roughly in half (~1000 lines, not ~2000).

## What Phi needs after this insight

Phi's structure mirrors `godelIClassical`'s Deriv tree:
```
godelIClassical d = ruleTrans (ruleSym selfEq) stepB
  where
  stepB = ruleTrans (ruleSym (congR TreeEq (reify cGSCR) diagFTargetCR)) stepA
  stepA = ruleTrans (ruleSym (congL TreeEq rhsT corrPf)) d1Conv
  d1Conv = eqSubst ... d1                           -- meta rewrite, identity on Deriv
  d1 = ruleInst zero enc d                          -- depends on d
  corrPf = ... (corr (thm14EV3 d))                  -- depends on d
  selfEq = treeEqSelf (reify cGSCR)                 -- closed
```

The **d-dependent parts** are `d1` and `corrPf`:

- **`d1 = ruleInst zero enc d`** — encoded as `encRuleInst aR_v0 v0` where `aR_v0 = ap2 Pair (ap1 cor v0) (reify (natCode 0))`. Uses the `cor` Fun1 (pure Rec-based codeOfReify) to compute `reify (code v0)` at Deriv level.

- **`corrPf`** — the hard one. `corr (thm14EV3 d)` is a polymorphic Deriv whose *structure* depends on d. To encode, we need `encT (thm14EV3 corrPf)` — effectively a "reflection of reflection". This second-order encoding is the main open question.

## The corrPf encoding question

`corrPf : Deriv Triv (eqn (ap1 (thmT trivCT) enc) (reify cGSCR))`.

With `enc` abstracted to `v0`, we want an encoded Term `encCorrPf v0` such that polymorphically in `hyp`,
```
Deriv hyp (eqn (ap1 (thmT trivCT) (encCorrPf v0))
               (reify (codeEqn (eqn (ap1 (thmT trivCT) v0) (reify cGSCR)))))
```

Two approaches:

### (A) Generic encoder for `corr (thm14EV3 X)`
Internalise Thm14EV3's correctness lemma as a SELF-APPLICATIVE Term. Requires encoding each case of thm14EV3's dispatch + a meta-recursion on pe's structure. Large (~800 lines).

### (B) Accept `encCorrPf` as an abstract parameter
Supply as a module parameter. Doesn't prove Gödel II standalone but CLOSES the skeleton in terms of two concrete pieces (encCorrPf + strongPhiCorr) that are each DERIVABLE from the architecture. Smaller but less satisfying.

### (C) Reframe via Schema F on v0
Use `ruleF` to prove strongPhiCorr directly via tree induction on v0, bypassing the need for explicit `encCorrPf`. Requires Phi to be structurally compatible with a Rec on v0 — possible but unclear how to arrange.

## Remaining axiom encoders needed by Phi (under approach A)

Already have: `encAxI`, `encAxFst`, `encAxSnd`, `encAxKT`, plus all 5 rule encoders.

Still needed (estimated size):
- `encAxTreeEqLL` (n13, ~40 lines, closed)
- `encAxTreeEqLN` (n14, ~50 lines)
- `encAxTreeEqNL` (n15, ~50 lines)
- `encAxTreeEqNN` (n16, ~60 lines)
- `encAxRefl` (n17, ~30 lines)
- `encAxComp2` (n5, ~50 lines)
- `encAxLift` (n6, ~50 lines)
- `encAxPost` (n7, ~50 lines)
- `encAxFan` (n8, ~60 lines)
- `encAxConst` (n3, ~30 lines)
- `encAxComp` (n4, ~40 lines)
- `encAxRecLf` (n9, ~40 lines)
- `encAxRecNd` (n10, ~50 lines)
- `encAxIfLfL` (n11, ~40 lines)
- `encAxIfLfN` (n12, ~40 lines)
- `encRuleCong1` (n20, ~80 lines, one sub)
- `encRuleF` (n24, ~150 lines, FOUR subs — hardest remaining)
- `encRuleHyp` (n26, ~30 lines)
- `encAxRecPLf` (n27, ~50 lines)
- `encAxRecPNd` (n28, ~80 lines)

Total: ~1000 more lines of mechanical encoding.

## Key discoveries to keep in mind

1. **IfLf is NOT a "ternary tree"** — it's an existing Fun2 primitive. If the architectural path requires object-level implication, IfLf provides it without violating the user's instruction.

2. **closed sub-derivations (`treeEqSelf c`, `diagFTargetCR`) don't need axiom-level encoding** — they can be packaged via `encT ∘ thm14EV3` at the meta level.

3. **`corrPf` is the load-bearing obstacle** — its encoding requires second-order thm14EV3 or a different architecture.

4. **The skeleton (`Guard/GodelIIClassicalSkel.agda`) is CORRECT** — if we can supply `Phi` and `strongPhiCorr`, Gödel II follows in ~20 lines. This means the ARCHITECTURE is validated even before Phi is built.

## Recommended next step for the following session

**Try approach (C)** — prove `strongPhiCorr` by Schema F / direct induction, sidestepping the need for `encCorrPf` entirely. Specifically:
- Define a trial Phi = `KT (some-constant)` or similar minimal closed form.
- Attempt to prove strongPhiCorr by hand for this trivial Phi.
- If impossible for trivial Phi, identify the minimal structural property Phi needs, then design Phi to match.

If (C) turns out intractable, revert to (A): continue the axiom encoders and build full Phi over another 2–3 sessions.

## Must-have invariants

- No postulates, no holes. ✓
- Each file under 10s. ✓ (biggest so far is 0.30s)
- `~/.cabal/bin/agda-2.9.0`, not `/opt/homebrew/bin/agda`. ✓
- `--safe --without-K --exact-split`. ✓

## Sanity check

```
~/.cabal/bin/agda-2.9.0 Guard/ProofEnc.agda
~/.cabal/bin/agda-2.9.0 Guard/GodelIIClassicalSkel.agda
~/.cabal/bin/agda-2.9.0 Guard/GodelIClassical.agda
```
All should succeed under 1s with no output.
