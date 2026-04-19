# Gödel II Redesign: two-argument `thmT` on the Fast chain

**Status.** The current `Guard/GodelIIFull.agda` proves a theorem (`conToBot`) that is formally correct but does **not** express classical Gödel II. The sentence `Con(x) ≡ TreeEq(thFunTFor(x), ⌜t=f⌝) = f` is refutable using only Schema-F computation axioms — see `Guard/GodelIITest.agda` for a 5-line proof of `conToBot` that uses no Gödel I at all. The redesign below replaces the conclusion-extracting `thFunTFor` with a validating, hypothesis-aware `thmT` so that `Con` becomes a real consistency statement.

The redesign is scoped to the **Fast chain** (`SubstTForPrecompFast.agda`, `ProofEAnyFast.agda`, `GodelIIFast.agda`, `GodelIIFullFast.agda`). The 108-second slow chain (`SubstTForPrecomp.agda`) is archived together with the current Gödel II writeup.

---

## 1. Core change

### Old shape
```
thFunTFor : Term -> Term
-- specification: thFunTFor(enc(d)) = reify(codeEqn(concl(d)))
```

`ruleHyp` is encoded by splicing in the reflexivity-based `mkProofEAny` tree for `H`. This erases the hypothesis at the syntactic level, which is why `mkProofEAny t f` produces a tree with `thFunTFor` value `⌜t=f⌝` unconditionally.

### New shape
```
thmT : Term -> Term -> Term      -- thmT(⌜H⌝, p)
-- specification:
--   thmT(⌜H⌝, enc(d)) = reify(codeEqn(concl(d)))     if d : H ⊢ concl(d)
--   thmT(⌜H⌝, p)      = sentinel                     otherwise
```

The encoding `enc` grows a new tag **`n26` = `tagHyp`** with `⌜H⌝` as its data, replacing the old `mkProofEAny`-splice at `ruleHyp` sites. The `thmT` case for `n26` compares the node's `⌜H⌝` against the first argument and returns it if they match, sentinel otherwise. Every composition rule (`trans`, `cong*`, `ruleF`, `ruleInst`) threads `⌜H⌝` unchanged to its recursive calls.

### Consequences
- `mkProofEAny A B` can no longer produce a valid `ProofE (eqn A B)` for arbitrary `A, B` — it contains no `n26` node, so `thmT(⌜H⌝, mkProofEAny A B) = sentinel` for every `H`. Restrict `mkProofEAny` to `(A := B)` cases (genuine reflexivity) and `(H := eqn A B)` cases (genuine hypothesis).
- `Con_H(x) ≡ TreeEq(thmT(⌜H⌝, x), ⌜t=f⌝) = f` is now a real consistency statement: refuting it at any `x` requires `x = enc(d)` for some genuine `d : H ⊢ t=f`.
- Gödel II's `conToBot` becomes non-trivial: it instantiates `Con_H` at `enc(d_⊥)` where `d_⊥ : G ⊢ t=f` comes from Gödel I.
- `Guard/GodelIITest.agda` must stop typechecking. This is the **negative acceptance test** for the redesign.

### Invariants preserved
- `thmT(⌜H⌝, p)`'s output shape is still `reify(codeEqn eq)` (a 2-child tree). Therefore **`codedSubst`, `substTFor`, `SubstTForPrecompFast`, `SubstTForPrecomp2Fast`, and all `Nelson/SubstTFor*.agda` files are untouched**. This is the point of the two-argument route: the downstream substitution chain survives.

---

## 2. Phases

Each phase is a landable commit. The build stays green between phases.

### Phase A — scaffolding (1 session)
- Add `n26` tag to `Guard/ThFun.agda` (new natCode offset).
- Add `tagHyp` encoding constructor: `encHyp : Tree -> Tree`, `encHyp hC = nd (natCode n26) hC`.
- Extend `thFun` (metalevel) with the `n26` case: compare ambient `⌜H⌝` (now a second argument) against node data; return ambient on match, sentinel on mismatch.
- Open question resolved here: which sentinel? Use `lf` (single leaf); this is disjoint from `codeEqn eq = nd _ _` for every `eq`, so the `TreeEq` check in `Con_H` naturally yields `falseT`.

**Deliverable.** `Guard/ThFunV3.agda` (new file; old `ThFun.agda` stays). Typechecks standalone; no consumers yet.

### Phase B — object-level `thmT` (2 sessions)
- Write `Guard/ThFunTForV3.agda` as a two-argument object-level functor:
  `thmT : Term -> Term -> Term` (or as an `ap2`-applicable encoding).
- Port the 25 existing per-tag cases from `Guard/ThFunTForCases0–3.agda`, updating each to thread `⌜H⌝` through recursive sub-dispatches. No behavioural change for `n1–n25`.
- Add the new `n26` case with its `TreeEq`-based check.
- Prove the per-tag reduction lemmas (`thmTAx*`) polymorphic in `⌜H⌝`.

**Deliverable.** `Guard/ThFunTForV3.agda` + companion case files. No change to `Thm14E.agda` yet.

### Phase C — new `thm14E` (3 sessions, highest risk)
- Write `Guard/Thm14EV3.agda` with a two-argument correctness:
  `thm14EV3 : {H eq : Equation} -> Deriv H eq -> ProofE3 eq`
  where `ProofE3 eq` has `corr : Deriv H' (thmT(⌜H⌝, enc) = reify(codeEqn eq))` for some (fixed) `H` bound in `thm14EV3`'s outer context.
- Port the 25 non-`ruleHyp` cases mechanically (each gets `⌜H⌝` threaded to recursive calls).
- The `ruleHyp` case now produces `encHyp ⌜H⌝` (the new `n26` encoding), not `ph`. This is the one-line change with the largest semantic impact.
- Restrict `mkProofEAny A B` in `Guard/ProofEAnyFast.agda` to a form that only builds genuine reflexivity witnesses; the old "fake trans(refl, refl)" construction is deleted.

**Deliverable.** `Guard/Thm14EV3.agda` + `Guard/ProofEAnyFastV3.agda`. Old `Thm14E.agda` untouched.

### Phase D — Gödel I on the new chain (2 sessions)
- Port `Guard/GodelIIFast.agda` (which actually contains Gödel I) to `Guard/GodelIFastV3.agda`, using `thm14EV3` and the new `ProofE3`.
- The diagonal construction (`templateCode`, `diagFTarget`, `cGS`, `cstf`) is unchanged in structure; only the `corr`-field access pattern changes.
- Reprove `treeEqSelf` polymorphic in `⌜H⌝` (trivial — its derivation uses no hypothesis rule).

**Deliverable.** `Guard/GodelIFastV3.agda` exporting `godelIDeriv : Deriv godelSentence (eqn trueT falseT)`.

### Phase E — Gödel II on the new chain (1 session)
- `Guard/GodelIIFullV3.agda`:
  - `conSentenceV3 ≡ eqn (ap2 TreeEq (ap2 thmT ⌜H⌝ (var zero)) codeBotT) falseT` (parameterised by `H`).
  - `conToBotV3` instantiates `Con_H` at `enc(d_⊥)` where `d_⊥` comes from `godelIDeriv`.
- Write `Guard/GodelIITestV3.agda` — the negative acceptance test. It attempts the old `mkProofEAny`-based proof. **This file must fail to typecheck**.

**Deliverable.** Real Gödel II, with `GodelIITestV3.agda` demonstrably not typechecking.

### Phase F — Prov refactor (1 session)
- Rewrite `Guard/Prov.agda` so `Prov e H` carries both the encoding and the required hypothesis:
  ```
  Prov : Equation -> Equation -> Set
  Prov H e = Σ (enc : Term). ⊢ thmT(⌜H⌝, enc) = reify(codeEqn e)
  ```
- `necessitation : Deriv H e → Prov H e`.
- `diagContradict` is unchanged.
- Update `Guard/GodelIIProv.agda` to match.

### Phase G — LaTeX + PDF (1 session)
- Bring `guard-godelII.tex` out of `Guard/archive/` and rewrite Sections 2, 6 to reflect the new `thmT`.
- Delete the "Remark on the strength of `Con`" that would otherwise be required.
- Rebuild PDF.

### Phase H — cleanup + final push (1 session)
- Archive `Guard/GodelIIFull.agda`, `Guard/GodelIIFullFast.agda`, `Guard/GodelII.agda` (actually Gödel I), `Guard/GodelIIFast.agda`, `Guard/Prov.agda`, `Guard/GodelIIProv.agda`, old `Thm14E.agda`, old `ThFunTFor*.agda`, old `ProofEAny*.agda` under `Guard/archive/v2-slow/` (or similar).
- Rename `*V3.agda` files to drop the `V3` suffix (promote them to the canonical names).
- Update `Guard/GODEL-II-REDESIGN.md` to a retrospective.

### Phase I — slippage buffer (2–3 sessions)
Realistic estimate for unexpected unification errors, especially in Phase C (the 26 cases of `thm14EV3`) and Phase D (the diagonal construction interacting with the new `n26` tag in `codedSubst`).

---

## 3. Session budget

| Phase | Sessions | Cumulative |
|---|---|---|
| A. Scaffolding (`ThFunV3.agda`) | 1 | 1 |
| B. Object-level `thmT` + 25 cases ported | 2 | 3 |
| C. `thm14EV3` + restricted `mkProofEAny` | 3 | 6 |
| D. Gödel I on new chain | 2 | 8 |
| E. Gödel II + negative acceptance test | 1 | 9 |
| F. Prov refactor | 1 | 10 |
| G. LaTeX + PDF | 1 | 11 |
| H. Cleanup | 1 | 12 |
| I. Slippage buffer | 2–3 | 14–15 |

**Total: ~12–15 sessions.** Lower bound 10 if Phase C goes mechanically; upper bound 17 if the `codedSubst` chain turns out to need `n26`-awareness after all.

---

## 4. Rollback strategy

Every phase is additive (`*V3.agda` files alongside old ones). Any phase can be abandoned by deleting the new files and reverting the commit — no existing code is touched until Phase H (cleanup). The "branch or not to branch" decision: keep everything on `main`, one commit per phase, with commit messages tagged `[redesign/phase-X]` so a range revert is straightforward.

## 5. Negative acceptance test

Phase E is not complete until `Guard/GodelIITestV3.agda` — the direct port of `GodelIITest.agda` to the V3 API — **fails to typecheck with a clear error** along the lines of "`mkProofEAnyV3` does not admit arbitrary `A B`" or "`thmT` with ambient `⌜H⌝` does not yield `⌜t=f⌝` for this fake encoding".

If this negative test still succeeds after Phase E, the redesign has failed and must be redone: some part of the validity check is still too lax.

## 6. What stays

- `Guard/Base.agda`, `Guard/Term.agda`, `Guard/Step.agda`, `Guard/StepReduce.agda`: unchanged.
- Schema F infrastructure (`axRefl`, `axI`, `axFst`, ..., `ruleF`): unchanged.
- `codedSubst`, `substTFor`, `SubstTForPrecompFast.agda`, `SubstTForPrecomp2Fast.agda`, all `Nelson/SubstTFor*.agda`: unchanged. This is the key safety property.
- `treeEqSelf`, `diagFTarget`: unchanged (but re-imported in V3 modules).
