# BRA-DESIGN: Option G — Guard-close single-layer BRA over the Deriv kernel

## Goal

Complete Guard 1963 Gödel II (guard15.pdf Theorem 14) in a formalization
that faithfully mirrors Guard's BRA: a single-layer formal system
over BRA-terms, with formulas (equations, implications, negations),
axioms Ax 0–13, rules (mp, sub, ind), and a Gödel-encoding /
enumerator `th`.

## Why a new layer?

Our current architecture has three layers that don't map cleanly
onto Guard's setup:

- **`Deriv`** (Guard/Step.agda): equational derivations, single-
  hypothesis Equation, Agda inductive.
- **`Provable`** (Guard/Provable.agda): propositional layer above
  Deriv, with axK/axS/axNeg + mp + `fromDeriv`.
- **`thmT`** (Guard/ThFunTForV3.agda): validator of encoded
  `Deriv`-proofs (i.e. encoded proofs of *equations*).

This split creates several friction points that have surfaced in
every attempt at Gödel II:

1. **Rose Lemma 1's polymorphic-tCorr obstruction.** `roseLemma1T`
   demands an encoded proof of H that validates polymorphically in
   ambient hyp. For H ≠ Triv this is unsatisfiable — see
   Guard/ROSE-CHAIN-DESIGN.md.

2. **`thmT` is equation-only.** Guard's Th 14 step 5 uses
   formula-level `mp` (Def 12, `th(4n+2) = mp(...)`). We have no
   formula-level dispatches in `thmT`.

3. **Provable ↔ Deriv bridge.** `fromDeriv` requires polymorphic
   Derivs; `provExtract` exists but adds translation overhead.

4. **Concepts live in 4 files.** Adding a propositional feature
   (e.g. encoded mp) requires touching `ThFunTForV3`, `ProofEnc`,
   `Provable`, and whichever downstream module wants it.

The user's diagnosis, which this plan adopts: the architectural split
itself is the root cause. Guard's own system has **one** layer. We
realign to that.

## Design

### One BRA layer, kernel reused

**Keep**: the equational kernel (`Deriv`, `Step`, `Term`, `Base`,
`ThFun`, `ThFunTForV3` and its helpers, `ProofEnc` for equations,
`CodeOfReify`, `Thm14EV3`, `SubstOp`, `SubstTForCorrect`,
`SubstTForPrecompClassical`, `GodelIClassical`). Gödel I stays where
it is. Equational encoders and their correctness lemmas stay
unchanged.

**Replace** `Provable` with `BRA` — a data type matching Guard 1963's
formal system exactly:

```agda
data BRA (hyp : Formula) : Formula -> Set where
  fromDeriv    : ({h : Equation} -> Deriv h eq) ->
                 BRA hyp (atomic eq)                  -- Ax 0-7 subsumed
  ruleHypB     : BRA hyp hyp
  axK          : (P Q : Formula) -> BRA hyp (P imp (Q imp P))       -- Ax 11
  axS          : (P Q R : Formula) -> BRA hyp ((P imp Q imp R)
                                                 imp (P imp Q)
                                                 imp (P imp R))      -- Ax 12
  axNeg        : (P Q : Formula) -> BRA hyp ((not P)
                                              imp (not Q)
                                              imp (Q imp P))          -- Ax 13
  axEqTrans    : -- Ax 4 at Formula level
  axEqCong1    : -- Ax 5
  axEqCongL    : -- Ax 6
  axEqCongR    : -- Ax 7
  mp           : BRA hyp (P imp Q) -> BRA hyp P -> BRA hyp Q          -- rule mp
  ruleSub      : (x : Nat) (t : Term) {P : Formula} ->
                 Eq (substF x t hyp) hyp ->                           -- side cond
                 BRA hyp P -> BRA hyp (substF x t P)                  -- rule sub
  ruleInd      : (P : Formula) ->
                 BRA hyp (substF zero O P) ->
                 BRA hyp (P imp substF zero (ap1 succF (var zero)) P) ->
                 BRA hyp P                                            -- rule ind (later if needed)
```

(Ax 0–3, 8–10 are equational and subsumed via `fromDeriv`.)

Note: the new rules relative to `Provable` are `ruleSub` (with an
explicit Eq side condition, matching Option A's soundness discipline
on `ruleInst`) and `ruleInd` (induction on var zero).

### What `Provable` becomes

`Provable.agda` is deprecated in favor of `BRA.agda`. Downstream
modules currently using `Provable` (`ProvableLemmas`,
`ProvableEqLifts`, `ProvableTh13`, `ProvableGodelIBridge`, `ConBRA`,
`GodelIIBRA`) are ported to `BRA` — the constructor names are
compatible enough that most changes are mechanical s/Provable/BRA/ +
adjusting imports. The `ruleSub` addition is new functionality, not a
breaking change.

The **existing RouteADf.agda / RouteAChain.agda** Provable-layer
constructions stay; they become lemmas at the BRA layer.

### Gödel-code extensions

`ThFun.codeEqn : Equation -> Tree` becomes supplemented by
`codeFormula : Formula -> Tree`:

```agda
codeFormula (atomic eq)  = codeEqn eq
codeFormula (P imp Q)    = nd (codeFormula P) (codeFormula Q)   -- + tag
codeFormula (not P)      = nd (codeFormula P) lf                 -- + tag
```

Two new tags (`tagImp`, `tagNeg`) are added to the tag scheme,
adjusting existing tag indices if needed or slotting in at the top of
the tag space.

`SubstOp.substOp` is extended with dispatches for the new
formula-tagged structures.

`ThFunTForV3.thmTStep` is extended with dispatches for 5 new
encoder tags:
  - n26: `encAxK` (encoding of axK applied)
  - n27: `encAxS`
  - n28: `encAxNeg`
  - n29: `encMp` (formula-level modus ponens)
  - n30: `encSub` (formula-level substitution; or subsume into ruleInst via tag n23)

### Formula-level encoders

New in `ProofEnc.agda`:
  - `encAxK, encAxKCorr, encAxKPass`
  - `encAxS, encAxSCorr, encAxSPass`
  - `encAxNeg, encAxNegCorr, encAxNegPass`
  - `encMp, encMpCorr, encMpPass`
  - `encSub, encSubCorr, encSubPass` (optional; may reuse encRuleInst
    machinery for equational sub)

Pattern is mechanical, mirroring existing `encAxI/encAxICorr/encAxIPass`.

### Chain transcription

Guard Th 14 p.17 five-step chain transcribes at the BRA layer:

```
Step 1: BRA hyp (atomic (th(x) = j) imp atomic (th(Dth(x)) = "th(x) = j"))
Step 2: BRA hyp (atomic (th(Dsub(i,i)) = "sub(i,i) = j"))
Step 3: BRA hyp (atomic (th(x) = j) imp atomic (th(gx) = "th(x) = sub(i,i)"))
Step 4: BRA hyp (atomic (th(x) = j) imp atomic (th(Y) = "th(x) ≠ sub(i,i)"))
Step 5: BRA hyp (atomic (th(x) = j) imp atomic (th(combined) = "0 = 1"))
```

`combined` is Guard's `4J[...]+2` nested-MP term, encoded via `encMp`.

Closure:
  - `dCon : BRA (atomic Triv) (atomic conBRAEqn)`.
  - `ruleSub` on `dCon` with `y := combined` at hyp = `atomic Triv`
    (side cond trivial: Triv is closed): obtains
    `BRA (atomic Triv) (atomic (th(combined) ≠ "0=1"))`.
  - Contrapositive of step 5 via `axNeg` + `mp`: `atomic (th(x) ≠ j)`.
  - Rewrite `j = rhsT` via `axEqCongR` + `diagFTargetCR`: obtain
    `atomic gsCR`.
  - Feed to `provableGodelIBridge` (ported) + `Consistent Triv` ⇒ Empty.

### What this avoids

- **Rose Lemma 1** is not used. The chain uses Guard's own `encMp`
  at the `thmT` dispatch level.
- **Polymorphic-tCorr** is not an issue. The BRA `ruleSub` operates
  at the BRA layer; no hypothesis-encoding polymorphism needed.
- **Provable/Deriv translation friction** is gone. A BRA derivation
  is the proof; `fromDeriv` embeds equational facts when needed.

## Plan

Commit after each step.

1. **Architecture doc** — this file. [bra-g-plan]
2. **Guard/BRA.agda** — data type + axioms + rules. ~400 lines.
   Includes `ruleSub` with Eq side condition. [bra-g-core]
3. **Bridge + port** — `provBraExtract` analog; port
   `ProvableLemmas`, `ProvableEqLifts`, `ProvableTh13`,
   `ProvableGodelIBridge`, `ConBRA`, `GodelIIBRA` to BRA.  Keep old
   `Provable.agda` as deprecated. [bra-g-port]
4. **codeFormula + substOp + thmTStep extensions** — imp, neg tags.
   ~400 lines. [bra-g-codes]
5. **Formula-level encoders** — encAxK, encAxS, encAxNeg, encMp,
   encSub + correctness + passes. ~500 lines. [bra-g-encoders]
6. **Guard Th 14 transcription** — in a new `Guard/GodelIIBRAv2.agda`
   or similar. ~200 lines. [bra-g-chain]

Total estimate: ~1500 new lines + ~150-200 lines modified.

## Stop and reassess

If any step surfaces an unexpected obstruction (similar in character
to the Rose polymorphic-tCorr issue), pause, document, and report
back. The design anticipates straight-line extension of the existing
encoder pattern; a surprise deeper than that indicates a deeper
problem and warrants stepping back.

## What this is NOT

- It's **not** a rewrite of the equational kernel. `Deriv`,
  `GodelIClassical`, `Thm14EV3`, `ProofEnc` (for equations) stay
  verbatim.
- It's **not** abandoning Option A's soundness refactor. `ruleSub`
  uses the same Eq-side-condition discipline as `ruleInst`.
- It's **not** introducing a new term grammar. Terms, functors,
  trees all stay.

## Deprecation of prior attempts

Path                                  | Status
---                                   | ---
Guard 5-step chain at Provable        | Superseded by BRA
Schema F + Rose Lemma 1               | Superseded (polymorphic-tCorr avoided)
GodelIIClassicalTriv(Strong).agda     | Archived; content absorbed into BRA chain
RouteAChain.agda                      | Absorbed; chain-step-3 lives in BRA chain
RouteADf.agda (thm13 lemmas)          | Retained; lemmas used by BRA chain

No prior work is lost; the valuable parts migrate into the BRA layer.
