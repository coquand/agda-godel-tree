# Next Session: Complete the V3 Redesign (Phases D2–D8)

## Setup

```
cd /Users/coquand/CHWISTEK
~/.cabal/bin/agda-2.9.0 <file>    # use THIS binary (not /opt/homebrew/bin/agda)
```

The repo is at `https://github.com/coquand/agda-godel-tree.git`, branch `main`, last commit `d6aa737` (`[redesign/phase-D2-partial] Define substOp and stepSubstP`). Everything in `Guard/` typechecks under `--safe --without-K --exact-split` except the incomplete step-equivalence lemma described below (intentionally absent).

## The big picture

The goal is a **genuine proof of Gödel II in Agda** using the Guard/Rose equational system, extended with a single new primitive `RecP : Fun2 → Fun2`. The existing V2 Gödel II (`Guard/archive/v2/GodelIIFull.agda`) proves a strictly weaker theorem (`conSentence` is refutable by pure computation — the `mkProofEAny`-for-ruleHyp loophole and the non-validating `case19` trans loophole). The redesign closes both loopholes:

1. **`case19V3`** (already in `Guard/ThFunTForV3.agda`) validates middle-term matching in trans via a `TreeEq` check, rejecting fake `trans(refl t, refl f)` encodings.
2. **`n26` tag + `case26Match`** (already in `ThFunTForV3.agda` + `ThFunTForV3Defs.agda`) require explicit hypothesis-use encoding via `encHyp ⌜H⌝` rather than the `mkProofEAny` splice.
3. **`RecP` + `substOp`** (this session's work) give `case23V3` the ability to apply closed substitution dynamically — needed for the `ruleInst` case.

Once (3) is wired up, the recursive `thm14EV3` handles all 27 Deriv constructors, Gödel I reflects to a genuine `enc_⊥` proof encoding, and Gödel II follows as `conToBot` + `diagContradict`.

## What's done (D1 + partial D2)

- **D1 complete.** `Guard/Term.agda` now has `RecP : Fun2 → Fun2`. `Guard/Step.agda` has `axRecPLf`/`axRecPNd`. Downstream pattern matches extended: `codeF2`/`substF2` (Term.agda), `codeF2NotVar`/`csF2Correct` (SubstCorrect.agda), `codeF2NeqTagVar`/`closedSTFF2` (SubstTForCorrect.agda), `f2xDispMissV3` (Thm14EV3.agda). V2 files that became non-exhaustive (ThFunCorrect, Thm14E, the whole V2 Gödel chain, and 22 Nelson files) are archived under `Guard/archive/v2/` and `Guard/archive/v2-nelson/`. Commit `84227e5`.
- **Partial D2.** `Guard/SubstOp.agda` defines `substOp = RecP stepSubstP` with `stepSubstP` accessing `tC`/`xC` from the `RecP`-param. `substOpLf` and `substOpNd` are the two trivial reductions. Commit `d6aa737`.

## What's left (D2 completion + D3–D8)

### D2 completion — prove `substOp` correctness

**The load-bearing lemma**, stated over tree inputs so it composes with V2's `closedSTFCode`:

```agda
substOpEquiv : (tC xC : Term) (c : Tree) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 substOp (ap2 Pair tC xC) (reify c))
                 (ap1 (closedSubstTFor tC xC) (reify c)))
```

**Proof strategy** (induction on `c : Tree`):

- `c = lf`: `reify lf = O`. LHS via `substOpLf tC xC = axRecPLf stepSubstP (Pair tC xC)` gives `O`. RHS via `closedSubstTForLf tC xC = axRecLf O cStep` gives `O`. Chain with `ruleTrans + ruleSym`.
- `c = nd a b`: `reify (nd a b) = ap2 Pair (reify a) (reify b)`. Both sides reduce via their Nd axioms. Use IHs on a and b. Then the **step-equivalence lemma** (see next) closes the chain.

**Step-equivalence lemma** (the 200-line piece I hit a bug on):

```agda
stepSubstPAtPair : (tC xC aT bT recs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 stepSubstP (ap2 Pair (ap2 Pair tC xC) (ap2 Pair aT bT)) recs)
                 (ap2 cStepOf (ap2 Pair aT bT) recs))
```

where `cStepOf` is the step function inside `closedSubstTFor tC xC` (private in `SubstTForCorrect.agda`). One approach to make `cStepOf` accessible: promote it from `where` to a top-level `private` definition in a new file, then import it.

**Easier approach** (recommended): prove `stepSubstPAtPair` goes to a canonical IfLf-of-IfLf form directly (without referencing `cStepOf`), and separately show `closedSubstTFor tC xC`'s step reduces to the same form. Then combine.

Canonical form: `IfLf (TreeEq aT (reify tagVar)) (Pair (IfLf (TreeEq bT xC) (Pair tC (Pair aT bT))) recs)`.

**My failed attempt** (in the removed part of an earlier commit to `SubstOp.agda` — see `git log --all -p Guard/SubstOp.agda` for the full text): used `congL TreeEq` with an `x` argument that had the wrong Fun2 shape. The fix is to carefully separate the left-rewrite and right-rewrite phases:

1. `fanRed` to expose the outer `IfLf`.
2. `congL IfLf (2nd arg)` to rewrite the check.
3. Within that, another `fanRed + congL TreeEq + congR TreeEq` chain.
4. `congR IfLf (check result)` to rewrite the Pair.
5. Within that, `fanRed + congL Pair + congR Pair` with their own sub-chains.

Each `congL` takes `(f : Fun2) (x : Term)` — the X is the FIXED side, so use the literal Term of what the other side will become. Getting these types right is the gotcha.

**Then** state the main correctness:

```agda
substOpCorrect : (t : Term) (x : Nat) (l : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 substOp (ap2 Pair (reify (code t)) (reify (natCode x))) (reify (code l)))
                 (reify (code (subst x t l))))
substOpCorrect t x l =
  ruleTrans (substOpEquiv (reify (code t)) (reify (natCode x)) (code l))
            (eqSubst (\c' -> Deriv _ (eqn _ (reify c')))
                     (csCorrect t x l)
                     (closedSTFCode (code t) (natCode x) l))
```

where `csCorrect` and `closedSTFCode` are the existing V2 lemmas.

### D3 — `case23V3` and the ruleInst reduction

Modify `Guard/ThFunTForV3.agda`:

```agda
case23V3 : Fun2
case23V3 = Fan (Fan origA recsBL substOp) (Fan origA recsBR substOp) Pair
```

Update `ndT23V3 hCode = branch (tc n23) case23V3 (ndT24V3 hCode)`.

In `Guard/ThFunTForV3Pass.agda`: update the two `pairBranchMiss` invocations at index n23 from `case23` to `case23V3`. Similarly in `Guard/Thm14EV3.agda`'s `ndDispKV3` helpers (k = 24, 25, 26) that skip past n23.

Prove `case23V3Match : Deriv hyp (eqn (ap2 case23V3 orig recs) ...)` — the reduction lemma.

### D4 — port `thm14EV3Inst`

In `Guard/Thm14EV3.agda`, add the case for `ruleInst x t pe`:

```agda
thm14EV3Inst : {H : Equation} {l r' : Term} (x : Nat) (t : Term) ->
               ProofE3 H (eqn l r') ->
               ProofE3 H (eqn (subst x t l) (subst x t r'))
thm14EV3Inst {H} {l} {r'} x t pe =
  mkProofE3 (natCode n23)
            (nd (nd (code t) (natCode x)) (nd pa-of-pe pb-of-pe))
            correct
            passF
```

The correctness chain uses `case23V3Match` + `substOpCorrect` + `pe.corr`.

### D5 — recursive `thm14EV3`

Top-level dispatch:

```agda
thm14EV3 : {H eq : Equation} -> Deriv H eq -> ProofE3 H eq
thm14EV3 (axI t) = thm14EV3AxI _ t
thm14EV3 (axFst a b) = thm14EV3AxFst _ a b
...  -- all 27 cases
thm14EV3 ruleHyp = thm14EV3Hyp _
thm14EV3 (ruleInst x t d) = thm14EV3Inst x t (thm14EV3 d)
thm14EV3 (axRecPLf s p) = ???   -- new V3 case; must provide encoding
thm14EV3 (axRecPNd s p a b) = ???
```

For the new `axRecPLf`/`axRecPNd` Deriv constructors, add cases to `thm14EV3` that emit appropriate encodings. These are unused by any natural derivation (they're the new axioms we added) but must be covered for totality.

### D6 — Gödel I on V3

Copy `Guard/archive/v2/GodelII.agda`'s diagonal construction (templateCode, `diagFTarget`, `cGS`, `cstf`) into a new file `Guard/GodelIV3.agda`. These parts don't change structurally — just redirect imports. Prove:

```agda
godelIDeriv : Deriv godelSentence (eqn trueT falseT)
```

This is the direct analog of V2's `botDeriv0` from `GodelIIFull.agda:73`.

### D7 — Gödel II on V3 + negative test

```agda
-- Guard/GodelIIV3.agda
provBot : Prov3 godelSentence (eqn trueT falseT)
provBot = necessitation (thm14EV3 godelIDeriv)

conToBot : {hyp : Equation} ->
           Deriv hyp conSentence ->
           Deriv hyp (eqn trueT falseT)
conToBot dCon = diagContradict codeBotT
  (ruleTrans (ruleSym (congL TreeEq codeBotT (corr provBot)))
             (ruleInst zero (enc provBot) dCon))
```

**Negative acceptance test** — `Guard/GodelIITestV3.agda`:

```agda
-- Attempt the V2-style attack: construct ProofE3 H (eqn trueT falseT)
-- from trans of two refls.  This MUST FAIL to typecheck under case19V3.
fakeTrans : ProofE3 whatever (eqn trueT falseT)
fakeTrans = thm14EV3Trans (thm14EV3Refl _ trueT) (thm14EV3Refl _ falseT)
--          ^^^ Agda must reject: trans requires middle to match.
```

If this file TYPECHECKS, the V3 redesign failed to close the loophole.

### D8 — Prov refactor, LaTeX, cleanup

- `Guard/ProvV3.agda` with `Prov3 H eq := Σ enc, corr` over the new `thmT ⌜H⌝`.
- Update `Guard/guard-godelII.tex` (currently in `archive/`) — restore, add a new section on the RecP extension and substOp, re-derive Section 6 using `case19V3` + `substOp` + `case23V3`.
- Rename `*V3.agda` files to drop the suffix (or leave as V3 for clarity).

## Anticipated session count (realistic)

| Phase | Estimate |
|---|---|
| D2 completion | 2 sessions (step-eq 1, main cor 1) |
| D3            | 1 session  |
| D4            | 1 session  |
| D5            | 1 session  |
| D6            | 2 sessions (diagonal port) |
| D7            | 1 session  |
| D8            | 2 sessions |
| Slippage      | 2 sessions |

**Total remaining: ~12 sessions.**

## Key files for orientation

- `Guard/GODEL-II-REDESIGN.md` — the original plan doc.
- `Guard/Term.agda`, `Guard/Step.agda` — grammar and axiom base, now with `RecP`.
- `Guard/SubstOp.agda` — this session's contribution; `substOp` defined, correctness TODO.
- `Guard/SubstTForCorrect.agda` — V2's closedSubstTFor correctness (`closedSTFCode`, `closedSTFF1`, `closedSTFF2`), reused.
- `Guard/SubstCorrect.agda` — V2's metalevel `csCorrect` lemma, reused.
- `Guard/TreeEqSelf.agda` — standalone `treeEqSelf` (split from GodelII.agda so V3 doesn't transitively depend on the archived Thm14E).
- `Guard/ThFunV3.agda`, `Guard/ThFunTForV3.agda`, `Guard/ThFunTForV3Defs.agda`, `Guard/ThFunTForV3Pass.agda` — V3 infrastructure.
- `Guard/Thm14EV3.agda` — V3 Theorem 14, 27 cases (26 done + ruleHyp), ruleInst pending.

## One-command sanity check

```
for f in Guard/*.agda Guard/Nelson/*.agda; do
  ~/.cabal/bin/agda-2.9.0 $f 2>&1 | grep -qE "error" && echo "BROKEN: $f"
done
```

Should print nothing if everything is green.

## Opening move for the next session

1. `cd /Users/coquand/CHWISTEK && git pull`
2. Read this doc.
3. Start with D2 step-equivalence. Attempt: write `stepSubstPAtPair` carefully, using the canonical-form strategy (not the cStep-reference strategy) described above. Target the lemma's LHS → canonical form first, then RHS → canonical form, then trans.
4. Commit each sub-lemma that typechecks. Don't accumulate untested chains longer than ~20 lines.
