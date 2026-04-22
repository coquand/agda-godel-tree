# Next session: Gödel II at the Provable (BRA) layer

## Context

This session (2026-04-21) established the propositional Provable layer
above our equational Deriv, following Guard 1963 BRA. The layer is ready;
the Gödel II chain transcription remains.

## What's delivered (committed)

### Guard/Formula.agda (~65 lines)

`Formula` data type: `atomic | not_ | _imp_`, plus formula-level
substitution `substF`.

### Guard/Provable.agda (~85 lines)

```agda
data Provable (hyp : Formula) : Formula -> Set where
  fromDeriv  : {eq : Equation} ->
               ({h : Equation} -> Deriv h eq) ->
               Provable hyp (atomic eq)
  ruleHypP   : Provable hyp hyp
  axK, axS, axNeg         -- Guard 1963 ax 11, 12, 13
  axEqTrans, axEqCong1,
  axEqCongL, axEqCongR    -- Guard 1963 ax 4, 5, 6, 7
  mp                      -- modus ponens
```

No `ruleSubP` (substitution at Formula level is available via the meta-
function `substF`; a Provable-level rule would require deduction-theorem
side conditions that we deferred).

### Guard/ProvableLemmas.agda (~105 lines)

```agda
provI        : (P : Formula) -> Provable hyp (P imp P)   -- I = SKK
deductionThm : Provable P Q -> Provable hyp (P imp Q)    -- Guard Ex 19
```

Deduction theorem proved by structural induction over all Provable
constructors. One acknowledged `CoverageNoExactSplit` warning on the
`mp` case (intrinsic to index unification; function is correct).

### Guard/ProvableEqLifts.agda (~85 lines)

```agda
hypSyll'     : rule form of hypothetical syllogism
prRefl       : a = a via fromDeriv (axRefl a)
prSym        : a = b -> b = a
prTrans      : a = b -> b = c -> a = c
prCong1/L/R  : congruences for unary / binary-left / binary-right functors
```

### Guard/SOUNDNESS.md

Audit of `ruleInst` call sites against the Hilbert-Bernays side condition
"x not free in hyp". `godelIClassical` and related sound uses identified;
`GodelIIRose` / `GodelIIV3` / scaffolding modules are unsound by the
side condition and will not be used for the new Gödel II chain.

### Guard/GUARD-BRA-TEMPLATE.md

The original template for this refactor; steps 1-5 marked done; steps 6-8
(Th 12-13, Th 11, Th 14) remain.

## What remains: Gödel II chain transcription

### The target

Guard 1963 Th 14: `th(y) ≠ '0 = 1'` is valid but unprovable in BRA.

In our system, stated at the Provable layer:

```agda
ConBRA : Formula
ConBRA = atomic (eqn (ap2 TreeEq (ap1 (thmT trivCT) (var zero)) codeBotT)
                     falseT)

godelII_BRA :
  Consistent Triv ->
  Provable hyp_BRA (atomic ConBRA) ->        -- "ConBRA is provable"
  Empty
```

### The chain (from guard15.pdf page 17)

```
1) th(x) = j ⊃ th(Dth(x)) = "th(x) = j"            [Th 13]
2) th(Dsub(i, i)) = "sub(i, i) = j"                 [Th 13]
3) th(x) = j ⊃ th(gx) = "th(x) = sub(i, i)"         [1, 2]
4) th(x) = j ⊃ th(Y...) = "th(x) ≠ sub(i, i)"       [defn of j]
5) th(x) = j ⊃ th(combined) = "0 = 1"               [3, 4]
reductio: assume ConBRA provable; by substitution + 5,
  th(x) ≠ sub(i, i) would be provable, contradicting Gödel I.
```

### Open pieces

1. **Th 12-13 lift at Provable level**. Given a Provable equation
   `f(x) = y`, encode as `th(Df(x)) = "f(x) = y"`. Requires:
   - `Df : Fun1 -> Term -> Term` combinator (exists in Guard/ProofEnc).
   - A helper that takes a `Provable hyp (atomic (eqn (ap1 f x) y))` and
     produces `Provable hyp (atomic (eqn (ap1 (thmT trivCT) (Df f x y))
     (reify (codeEqn (eqn (ap1 f x) y)))))`.
   - Internally uses thm14EV3 (axRefl + substitution) + fromDeriv at
     specific instances.
   ~150-200 lines.

2. **Chain steps 1-5** at the Provable level, using Th 13 applications
   chained via `mp` and `deductionThm`. ~100-200 lines.

3. **Gödel II reductio**: bridge the Provable chain result to Gödel I
   via `godelIClassical`. The key meta-step is extracting a
   `Deriv Triv gsCR` from the Provable chain's conclusion, which
   requires either:
   - A `fromDerivImp` / `derivToProv` utility (see this session's
     earlier design discussions).
   - OR a direct meta-level pattern match on the specific Provable
     structure.
   ~80-150 lines.

**Total estimate: 400-600 lines, 1-2 sessions.**

### Design decisions to be revisited

- Whether to add `fromDerivImp` as a primitive Provable constructor
  (option i) or build `derivToProv` via `ruleSubP` + `ruleFP`
  (option ii). This session: deferred. See discussion in
  SOUNDNESS.md context and GUARD-BRA-TEMPLATE.md.

- Whether to formalize `ruleInst`'s side condition (Options A/B in
  SOUNDNESS.md) as a precursor or leave as audit-only. Cascading
  refactor if A; additive if B; C (current) ships current work.

## Command for next session

```
Read Guard/NEXT-SESSION-BRA-GODELII.md, Guard/GUARD-BRA-TEMPLATE.md,
Guard/SOUNDNESS.md.  Also read guard15.pdf pages 13-17 for the
Gödel I/II proof details.

Goal: transcribe Guard 1963 Theorem 14 (Gödel II) at our Provable
layer, producing
  godelII_BRA : Consistent Triv -> Provable hyp (atomic ConBRA) -> Empty

Use the delivered Provable infrastructure (Formula, Provable,
ProvableLemmas, ProvableEqLifts).  Do NOT use GodelIIRose or
GodelIIV3 (unsound per Guard/SOUNDNESS.md).  Use godelIClassical at
its native type hyp = Triv.

Conventions: --safe --without-K --exact-split, no postulates, no
holes.  Use ~/.cabal/bin/agda-2.9.0.  Commit after each of: Th 12-13
lift, chain steps 1-5, reductio closure.

Proceed autonomously.
```

## Session ledger

| # | Step | Status | Commit |
|---|---|---|---|
| 1 | Formula + Provable core | ✅ | `[bra-step1]` |
| 2 | Formula substitution | ✅ | `[bra-step2]`/`-fix` |
| 3 | provI + deductionThm | ✅ | `[bra-step3]` |
| 4-5 | Equality axioms + derived rules | ✅ | `[bra-step4-5]` |
| 6 | Audit ruleInst; SOUNDNESS.md | ✅ | `[doc]` |
| 7 | Th 12-13 at Provable | ⏳ | — |
| 8 | Gödel II chain | ⏳ | — |
| 9 | Gödel II closure | ⏳ | — |

This session delivered the propositional layer and the soundness audit
in 6 commits, 345 lines of Agda + 110 lines of documentation. No
postulates, no holes, one acknowledged exact-split warning.
