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

**The obstacle.** V2's `godelSentence` (in `Guard/SubstTForPrecomp.agda`) uses `thFunTFor` as its evaluator. V3's `thm14EV3` produces `ProofE3 H eq` whose `corr` field is a `Deriv` about `thmT (reify (codeEqn H))`, **not** about `thFunTFor`. These two evaluators agree on encodings that do **not** use `encHyp` (the `n26` tag), but `thm14EV3Hyp H` emits exactly such an `encHyp` encoding. So for the Gödel I argument to close, the sentence itself must use `thmT hCode` where `hCode = reify (codeEqn godelSentence_V3)` (self-referential).

**Plan.** Create `Guard/SubstTForPrecompV3.agda` that mirrors `SubstTForPrecomp.agda` with three substitutions:

1. Replace `(ap1 thFunTFor (var zero))` with `(ap1 (thmT (var v1)) (var zero))` inside the template.
2. Replace `(ap1 substTFor (var v1))` with `(ap2 substOp (ap2 Pair (var v1) (reify (natCode v1))) (var v1))`.
3. Everything else (`templateCode`, `crTC`, `cGS`, `codeEqn` decomposition) restructured around the new template.

Key identity to re-prove in V3 form:

```agda
diagFTargetV3 :
  Deriv hyp (eqn (ap2 substOp (ap2 Pair (reify crTC_V3) (reify (natCode v1)))
                              (reify templateCode_V3))
                 (reify cGS_V3))
```

Strategy: use `substOpEquiv` to reduce to `closedSubstTFor` on the tree, then reuse V2's `closedSTFNd` machinery (`codedSubstNd`, `csCorrect`, etc.) — these operate purely on trees and don't care whether the original template used `thFunTFor` or `thmT`.

Also: the `substGodelSentence` and `instForm2` lemmas need V3 analogues. Since `substOp` doesn't have internal `var 11 / var 12`, **`instForm2` is unnecessary** — the substitution parameters are embedded in the `Pair` argument to `substOp`, not in free variables. That simplifies the chain.

Sketch of `godelIDeriv`:

```agda
godelIDeriv : Deriv godelSentence_V3 (eqn trueT falseT)
godelIDeriv =
  let hyp = godelSentence_V3
      dG = ruleHyp {godelSentence_V3}
      pe = thm14EV3Hyp godelSentence_V3       -- ProofE3 GS GS ; no loophole
      enc = encT pe
      hCodeV3 = reify cGS_V3                   -- = reify (codeEqn godelSentence_V3)

      corrPf : Deriv hyp (eqn (ap1 (thmT hCodeV3) enc) (reify cGS_V3))
      corrPf = corr pe

      -- thmT hCodeV3 (enc) == substOp(P,tgt)(reify templateCode_V3) == reify cGS_V3
      chain = ruleTrans corrPf (ruleSym diagFTargetV3)

      -- Instantiate godelSentence_V3 at var 0 = enc.
      instD = eqSubst _ (substGodelSentenceV3 enc) (ruleInst zero enc dG)
      -- Now instD : ap2 TreeEq (ap1 (thmT hCodeV3) enc) (ap2 substOp _ _) = poo.
      -- Rewrite ap1 (thmT hCodeV3) enc to substOp(..) using chain.

      step = ruleTrans (ruleSym (congL TreeEq _ chain)) instD
      -- step : ap2 TreeEq (substOp(..)) (substOp(..)) = poo

      selfEq = treeEqSelf (ap2 substOp _ _)   -- = O

  in ruleTrans (ruleSym selfEq) step
```

The heavy machinery is getting `SubstTForPrecompV3.agda` right.  Estimated: one full session (maybe two). The V2 structure is a close template.

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
