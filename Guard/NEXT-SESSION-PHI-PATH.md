# Next Session: Phi Construction Path Forward

## Outcome of approach (C) exploration

**Approach (C) (Schema F / direct equational reasoning) is intractable.**

See `Guard/StrongPhiCorrAnalysis.agda` (compiled, no postulates) for the
formal documentation.  The file proves **conditional** versions of
`StrongPhiCorr Phi` for three minimal Phi candidates:

| Trial         | Conditional lemma                          | Missing fact                                        |
|---------------|--------------------------------------------|-----------------------------------------------------|
| `Phi = I`     | `phiCorrIFromMissingFact`                  | `reify cGSCR = codeBotT` (FALSE — distinct closed terms) |
| `Phi = KT C`  | `phiCorrKTFromMissingFact`                 | constant RHS cannot match v0-dependent LHS         |
| `Phi = Comp I I` | `phiCorrCompIIFromMissingFact`          | same as Phi = I (operationally equivalent)         |

The fundamental obstruction: `StrongPhiCorr Phi` is an equation between
two `TreeEq` applications whose **right-hand TreeEq slots** are distinct
closed terms (`reify cGSCR` vs `codeBotT`).  No congruence chain or
Schema F application can bridge two distinct closed terms without a
separate equation between them — and no such equation is derivable from
`Triv` (it would mean Triv is inconsistent).

Schema F (`ruleF`) cannot help either: while we can express LHS and RHS
as `ap1 _ v0` for some Fun1, the recursive scheme that LHS satisfies
(via TreeEq decomposition) is not invertible — we cannot recover the
underlying `thmT trivCT var_i` from `TreeEq (thmT trivCT var_i) (reify cGSCR)`.
See the comment block in `StrongPhiCorrAnalysis.agda` for details.

## Recommendation: approach (A)

Continue the axiom-encoder build-out as listed in
`NEXT-SESSION-GODELII-CLASSICAL.md`.  Estimated ~1000 more lines of
mechanical encoding (~20 axiom encoders + `encRuleCong1`, `encRuleF`,
`encRuleHyp`).

The hardest remaining piece is **`encCorrPf`**: encoding `corr (thm14EV3 d)`
as a self-applicative Term.  The April-2026 session already validated
that `encT ∘ thm14EV3` packages closed sub-derivations cleanly (see
`Guard/EncSelfEq.agda`); the open question is whether the same trick
extends to derivations that depend on `d`.

## Suggested order for the next session

1. ~~**Write `encAxRefl` (n17)**~~ — DONE (commit `0e30100`).
2. ~~**Write `encRuleCong1` (n20)**~~ — DONE (commit `12b3f24`).
3. ~~**Write `encAxTreeEq*` (n13–n16)**~~ — DONE
   (commits `d92b40a`, `144143a`).
4. ~~**Write `encRuleHyp` (n26)**~~ — DONE (commit `a54f0f5`).
5. ~~**Write remaining axiom encoders**~~ — DONE (commits `790ae1c`,
   `97946e9`, `13344a9`, `64761d7`).  All 12 axiom encoders ported.
6. **Write `encRuleF` (n24)** — FOUR sub-proofs.  Hardest remaining.
   Pattern from `Guard.Thm14EV3.thm14EV3RuleF` (around line 2050+).
   Likely needs its own session (~200+ lines).
7. **Tackle `encCorrPf`**: investigate whether the meta-reflection
   pattern from `EncSelfEq.agda` extends to d-dependent cases by
   parameterising thm14EV3 over a hypothetical `d`.  Load-bearing
   second-order reflection question; potentially the longest piece.

## Current encoder roster (post-session)

| Tag | Combinator                    | Kind              |
|-----|-------------------------------|-------------------|
| n0  | `encAxI`                      | axiom (1 arg)     |
| n1  | `encAxFst`                    | axiom (2 args)    |
| n2  | `encAxSnd`                    | axiom (2 args)    |
| n3  | `encAxConst`                  | axiom (2 args)    |
| n4  | `encAxComp`                   | axiom (3 args)    |
| n5  | `encAxComp2`                  | axiom (4 args)    |
| n6  | `encAxLift`                   | axiom (3 args)    |
| n7  | `encAxPost`                   | axiom (4 args)    |
| n8  | `encAxFan`                    | axiom (5 args)    |
| n9  | `encAxRecLf`                  | axiom (2 args)    |
| n10 | `encAxRecNd`                  | axiom (4 args)    |
| n11 | `encAxIfLfL`                  | axiom (2 args)    |
| n12 | `encAxIfLfN`                  | axiom (4 args)    |
| n13 | `encAxTreeEqLL`               | axiom (closed)    |
| n14 | `encAxTreeEqLN`               | axiom (2 args)    |
| n15 | `encAxTreeEqNL`               | axiom (2 args)    |
| n16 | `encAxTreeEqNN`               | axiom (4 args)    |
| n17 | `encAxRefl`                   | axiom (1 arg)     |
| n18 | `encRuleSym`                  | rule  (1 sub)     |
| n19 | `encRuleTrans`                | rule  (2 subs)    |
| n20 | `encRuleCong1`                | rule  (1 sub)     |
| n21 | `encCongL`                    | rule  (1 sub)     |
| n22 | `encCongR`                    | rule  (1 sub)     |
| n23 | `encRuleInst`                 | rule  (1 sub)     |
| n25 | `encAxKT`                     | axiom (2 args)    |
| n26 | `encRuleHyp`                  | hypothesis        |
| n27 | `encAxRecPLf`                 | axiom (2 args)    |
| n28 | `encAxRecPNd`                 | axiom (4 args)    |

**26 / 28 encoders done.**  Remaining: n24 (`encRuleF`) + `encCorrPf`.

ProofEnc.agda is 2390 lines, compiles in ~0.17s.  No postulates,
no holes anywhere.

Each combinator has the same skeleton as `encRuleSym` and `encRuleTrans`
in `Guard/ProofEnc.agda` — the work is mechanical once the navigation
helper (`ndDispNV3Pub`) and case-N proof (in `ThFunTForCases*`) are in
hand.

## Files already in place

- `Guard/GodelIIClassicalSkel.agda` (207 lines, 0.13s) — parametric
  Gödel II given Phi + strongPhiCorr.
- `Guard/ProofEnc.agda` (963 lines, 0.30s) — 9 combinators (encRuleSym,
  encRuleTrans, encCongL/R, encRuleInst, encAxI/Fst/Snd/KT).
- `Guard/EncSelfEq.agda` (105 lines, 0.12s) — meta-reflection POC.
- `Guard/StrongPhiCorrAnalysis.agda` (NEW, ~125 lines, 0.4s) — approach
  (C) intractability.

## Sanity check

```
~/.cabal/bin/agda-2.9.0 Guard/StrongPhiCorrAnalysis.agda
~/.cabal/bin/agda-2.9.0 Guard/EncSelfEq.agda
~/.cabal/bin/agda-2.9.0 Guard/GodelIIClassicalSkel.agda
~/.cabal/bin/agda-2.9.0 Guard/ProofEnc.agda
```

All under 1s.

## Invariants

- Use `~/.cabal/bin/agda-2.9.0` (not `/opt/homebrew/bin/agda`).
- `--safe --without-K --exact-split`.
- No postulates, no holes.
- Object-level implication is FORBIDDEN (only meta-level Agda arrow
  `Deriv hyp A → Deriv hyp B`).  IfLf is permitted as it is an existing
  Fun2 primitive.
