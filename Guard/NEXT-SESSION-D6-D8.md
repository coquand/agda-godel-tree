# Next Session: Complete the V3 Redesign (Phases D6–D8)

## Setup

```
cd /Users/coquand/CHWISTEK
~/.cabal/bin/agda-2.9.0 <file>    # use THIS binary (not /opt/homebrew/bin/agda)
```

Last commit: `9fbca6f [redesign/phase-D5] Complete V3 theorem 14: thm14EV3 total dispatcher`.

## State of play

**D1–D5 done.** Summary:

- **D1:** `RecP : Fun2 -> Fun2` added to `Guard/Term.agda`, with `axRecPLf`/`axRecPNd` axioms in `Guard/Step.agda`. All downstream substitution / code-of / passthrough predicates extended.
- **D2:** `Guard/SubstOp.agda` — `substOp = RecP stepSubstP`. Correctness: `substOpEquiv` (= `closedSubstTFor tC xC` on reified trees) and `substOpCorrect` (Term→code→subst full picture). No postulates.
- **D3:** `case23V3 = Fan (Fan origA recsBL substOp) (Fan origA recsBR substOp) Pair` defined in `Guard/ThFunTForV3.agda`. `case23V3Match` proved in `ThFunTForV3Defs.agda`.
- **D4:** `thm14EV3Inst` fully proved in `Guard/Thm14EV3.agda`. Uses `case23V3Match` + `substOpCorrect` per equation side. Includes `aRPassV3` helper for `ndDispatchV3` passthrough at the `aR = Pair tCt xCt` tag.
- **D5:** Full V3 dispatch chain extended with `n27` (`case27` for `axRecPLf`) and `n28` (`case28` for `axRecPNd`). `thm14EV3 : {H eq : Equation} -> Deriv H eq -> ProofE3 H eq` covers all 29 Deriv constructors recursively.

The full file set — `Guard/*.agda` — typechecks under `--safe --without-K --exact-split` with the Cabal Agda 2.9.0 binary.

## What's left (D6–D8)

### D6 — Gödel I on V3 (the hard part)

**Goal:** `godelIDeriv : Deriv godelSentence_V3 (eqn trueT falseT)`.

**THE REAL obstacle, uncovered while attempting this session.**  V2's `godelSentence` (in `Guard/SubstTForPrecomp.agda`) works because `thFunTFor` is *hCode-agnostic* — a single closed `Fun1`.  V3's `thmT` is *hCode-specific* — the case26 check inside `thmT hCode` on an `encHyp(body)` encoding returns `hCode` only when `body = hCode`, else sentinel `O`.

The V2 diagonal trick (substitute `var v1 ↦ reify templateCode`) gives a sentence whose `thmT`'s `hCode` becomes `reify templateCode_V3`.  But `thm14EV3Hyp H` produces a proof-encoding `enc = encHyp (reify (codeEqn H)) = encHyp (reify cGS_V3)`.  Its `corr` witness is

```
corr pe : thmT (reify cGS_V3) enc = reify cGS_V3
```

with `hCode = reify cGS_V3`, NOT `reify templateCode_V3`.  Since `cGS_V3 ≠ templateCode_V3` (they differ by the diagonal substitution), these two `thmT` applications *disagree* on `enc`:

```
thmT (reify cGS_V3)        enc = reify cGS_V3      -- case26 matches
thmT (reify templateCode_V3) enc = O               -- case26 mismatches → sentinel
```

So the sentence's instantiated form can't be directly rewritten via `corr pe` — there is no bridge.

**Design question for next session.**  Three options to explore:

1. **Change the diagonal.**  Design `templateCode_V3` so that `reify cGS_V3 = reify templateCode_V3` — requires `cGS_V3 = templateCode_V3`, i.e., no substitution, i.e., the template has no `var v1` — but then the template is just the sentence itself, and the fixed-point construction collapses.  Likely unworkable.

2. **Use a different ambient hypothesis.**  Pick `H' = template_V3` (the un-substituted, open equation) as ambient; then `reify (codeEqn H') = reify templateCode_V3` matches the sentence's `thmT` hCode.  But then we need `Deriv H' (eqn trueT falseT)` instead of `Deriv godelSentence_V3 (eqn trueT falseT)`.  The Gödel-II direction from there is different from the V2 template, and it's unclear what the negative soundness statement should look like.

3. **Externalise hCode from the sentence.**  Let `godelSentence_V3` have `var v1` *unbound* (not substituted) — an open equation with a free `v1`.  Instantiate it at `var v1 ↦ reify cGS_V3` at the Deriv level via `ruleInst`.  But then proofs need to know `cGS_V3` as a specific closed tree, which still requires solving the fixed point.

**Recommended approach for next session:** attempt option 2 carefully, with `H' = template_V3`.  This shifts the Gödel II statement from "no consistent H proves Con_H" to a slightly stronger form "no consistent extension of `template_V3` proves Con_{extension}".  The argument may close cleanly because corr's `hCode` and the sentence's embedded `hCode` both become `reify templateCode_V3`.

Alternatively, revisit what "V3 Gödel II" should mean in the first place.  The cleanest statement may require redesigning `thmT` to be hCode-agnostic *for sub-proofs* while still enforcing hCode at the ruleHyp level.  E.g., make `case26` permissive: it always returns body (thus behaves like V2's missing-case path), and enforce the hypothesis discipline via an *external* check on the final encoding rather than inside the evaluator.  That would let V3 reuse V2's diagonal directly.

**Bottom line.** D6 is a design-level problem, not a mechanical port.  The existing `Guard/archive/v2/GodelIIFull.agda` is NOT a template — the V3 mechanism diverges structurally at the sentence layer.

### D7 — Gödel II on V3 + negative test

Once `godelIDeriv` exists:

```agda
-- Guard/GodelIIV3.agda
provBot : Prov3 godelSentence_V3 (eqn trueT falseT)
provBot = necessitation (thm14EV3 godelIDeriv)

conToBot : {hyp : Equation} ->
           Deriv hyp conSentenceV3 ->
           Deriv hyp (eqn trueT falseT)
conToBot dCon = diagContradict codeBotT
  (ruleTrans (ruleSym (congL TreeEq codeBotT (corr provBot)))
             (ruleInst zero (enc provBot) dCon))
```

Note: V3 `conSentenceV3` = `eqn (ap2 TreeEq (ap1 (thmT hCodeH) (var zero)) codeBotT) falseT` is **H-dependent** (hCodeH = reify (codeEqn H)).  In V2 it was H-independent.

**Negative acceptance test** — `Guard/GodelIITestV3.agda`:

```agda
fakeTrans : ProofE3 whatever (eqn trueT falseT)
fakeTrans = thm14EV3Trans (thm14EV3Refl _ trueT) (thm14EV3Refl _ falseT)
```

MUST not typecheck — `case19V3` rejects `trans(refl trueT, refl falseT)` because the middle terms (`trueT` vs `falseT`) disagree.  If it DOES typecheck, the V3 redesign has a hole.

Actually the check may fail at a different layer — `thm14EV3Trans`'s type signature requires `ProofE3 H (eqn t u)` and `ProofE3 H (eqn u v)` with the same `u`.  Since `u = trueT` from the first and `u = falseT` from the second, the types don't unify.  This is the static guard.

### D8 — Prov refactor, LaTeX, cleanup

- `Guard/ProvV3.agda` with `Prov3 H eq := Σ enc, corr` over the new `thmT ⌜H⌝`.
- Update `Guard/guard-godelII.tex` (currently in `archive/`) — restore, add a new section on the RecP extension and substOp, re-derive Section 6 using `case19V3` + `substOp` + `case23V3`.
- Rename `*V3.agda` files to drop the suffix (or leave as V3 for clarity).

## Key files (updated set)

- `Guard/SubstOp.agda` — substOp + correctness (D2 complete).
- `Guard/Term.agda`, `Guard/Step.agda` — RecP primitive + axioms (D1).
- `Guard/ThFunTForV3.agda` — case23V3, case27, case28, extended chain to ndT29V3.
- `Guard/ThFunTForV3Pass.agda` — 29-branch miss chains.
- `Guard/ThFunTForV3Defs.agda` — case23V3Match.
- `Guard/Thm14EV3.agda` — all 29 thm14EV3* functions + top-level dispatcher.
- `Guard/archive/v2/GodelII.agda`, `Guard/archive/v2/GodelIIFull.agda` — V2 reference to port.
- `Guard/SubstTForPrecomp.agda` — V2 diagonal machinery to mirror for V3.

## Anticipated session count (updated)

| Phase | Estimate |
|---|---|
| D6    | 2 sessions (SubstTForPrecompV3 + GodelIV3) |
| D7    | 1 session (mostly mechanical port) |
| D8    | 2 sessions (LaTeX + rename) |
| Slippage | 1 session |

**Total remaining: ~6 sessions.**

## Opening move for the next session

1. `cd /Users/coquand/CHWISTEK && git pull`
2. Read this doc + `Guard/archive/v2/GodelIIFull.agda` for reference.
3. Start by copying `SubstTForPrecomp.agda` to `SubstTForPrecompV3.agda`, then do the three substitutions (thFunTFor → thmT(var v1), substTFor → substOp, drop v11/v12).  Work through compilation errors one at a time.
4. Commit each sub-lemma that typechecks. Don't accumulate untested chains longer than ~20 lines.
