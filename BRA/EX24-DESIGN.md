# BRA Ex 24 design — post-mpF

Written after [BRA-ex24-mp] (commit 41e1021) validated the approach.
`mpF : Fun2` + its defining equation typecheck in 0.065s and 87
lines.  This doc plans the remaining Ex 24 work so that coding
proceeds by clear contract, not by-the-seat.

## Status

**Foundation** (`BRA/`, 6 files, commit 78de300): `Base`, `Term`,
`Formula`, `Deriv`, `StepReduce`, `Cor`.  All typecheck < 0.15s.

**Ex 24 so far:**

| Guard name | BRA name | File | Status |
|------------|----------|------|--------|
| `num`      | `cor`    | `BRA/Cor.agda` (via `corOfReify`) | ✓ done |
| `mp`       | `mpF`    | `BRA/Mp.agda` | ✓ done |
| `ind`      | `indF`   | `BRA/Ind.agda` (planned) | — |
| `ax`       | `ax`     | `BRA/Ax.agda` (planned) | — |
| `sbt`      | —        | **skipped** (trees pair for free) | — |
| `sbf`      | —        | **skipped** (trees pair for free) | — |
| `sb`       | `subT`   | `BRA/SubT.agda` (planned) | — |
| `sub`      | `sub`    | `BRA/Sub.agda` (planned) | — |

Six functors total (Guard has eight; `sbt`/`sbf` dissolve under
tree-pairing since they existed only to decode prime-product lists
in Guard's natural-number encoding).

## Naming convention

DerivF rule `mp` (the modus-ponens inference rule) clashes with
Guard's Ex 24 `mp` (the functor).  Resolution: suffix Ex 24
functors with `F` (for "functor") **only when the bare name clashes
with a DerivF constructor**.  `mp` clashes → `mpF`; `ind` doesn't
(rule is `ruleIndBT`) → `indF` still for parallel naming; `ax`
doesn't → `ax`; `subT`, `sub`, `cor` are unique.

## File convention: definition + `*Def` correctness lemma per file

Each `BRA/<Name>.agda` file carries **both** the Ex 24 functor and
its defining-equation lemma:

| File | Functor | Correctness lemma |
|---|---|---|
| `BRA/Cor.agda` | `cor` | `corOfReify` |
| `BRA/Mp.agda`  | `mpF` | `mpFDef` |
| `BRA/Ind.agda` (planned) | `indF` | `indFDef` |
| `BRA/SubT.agda` (planned) | `subT` | `subTDef` |
| `BRA/Sub.agda` (planned) | `sub` | `subDef` |
| `BRA/Ax.agda` (planned) | `ax` | `axDef*` (likely one per schema) |

The `*Def` lemma is what downstream Thm 12 / Thm 13 / Gödel II work
*actually consumes*.  `mpF` the Fun2 value is just a combinator;
`mpFDef : (P Q : Formula) -> Deriv (atomic (eqn (ap2 mpF …) (reify
(codeFormula Q))))` is the load-bearing theorem that lets a proof
*use* `mpF` to reduce `ap2 mpF (…) (…imp…)` to the code of `Q`.
Same pattern for every Ex 24 functor.

## Remaining functors — sketches

Each sketch gives the Guard spec, the intended Fun1/Fun2 expression,
and a very rough size estimate.  Definitions and derivations are
**not written**; design only.

### indF (Ex 24 [5])

**Guard spec (p.14).** `ind("P(0)", "P(x₀) ⊃ P(sx₀)") = "P(x₀)"`.
One variable `x₀` throughout, because Guard's successor is unary.

**User's rephrasing.**
`ind(code (substF v0 0 P), code (imp P (substF v0 (S v0) P))) = code P`.

**Tree analog — and the new question.** Our tree induction (see
`ruleIndBT` in `BRA/Deriv.agda`) needs TWO subtree variables `v1`,
`v2` because `Pair` is binary.  The step code has the shape

    codeFormula ((substF 0 (var v1) P) imp
                 ((substF 0 (var v2) P) imp
                  (substF 0 (ap2 Pair (var v1) (var v2)) P)))

The question Guard doesn't face: what is `v1` here?  Four options:

**Option A — fix `v1 = zero` by convention.**  `substF 0 (var 0) P`
is the identity on `P` (substituting `v₀` for itself).  The
outer-imp LHS is `codeFormula P` directly, so `indF` is a pure
projection parallel to `mpF`:

    indF = Post (Comp Fst Snd) (Post Snd Pair)

~40 lines total (def + def-equation).  BRA proofs that use
induction must pick `v1 = zero` when they hand a step to the
`th(4y+3)` slot.  Renaming is always available via `ruleInst`, so
this is a convention on the *enumeration*, not a weakness of BRA.

**Option B — pass `v1` explicitly as part of the argument.**
`indF` takes a packed triple `Pair (Pair base step) v1_code` or
similar.  `th(4y+3)`'s encoding of `y` then has to embed `v1`
somewhere (probably via `K`/`L`-style projections).  ~80 lines
for indF + more for th-integration.  More faithful to "any
induction step works"; costs complexity in `th`.

**Option C — recover `v1` via `subT`.**  Accept the step in fully
general shape and use `subT` to rename `v1` back to `v₀` in
whatever `Fst (Snd step)` returns.  Maximally general; depends on
`subT` existing first; ~150 lines.

**Option D — diagonal step `P(v₀) imp P(Pair v₀ v₀)`.**  One
variable but the induction hypothesis is weaker: you don't get IHs
for both subtrees independently.  **Dead** — insufficient for
Thm 11's diagonal construction.

**Pending user decision.** Leaning toward Option A as a starting
point (matches `mpF`'s clean projection style; convention cost is
cheap; renaming via `ruleInst` recovers generality).  Upgrade to C
only if some Thm 12 case forces it.  User is thinking about which
way `v'` should work.  **Do not code `indF` until this is resolved.**

### ax (Ex 24 [6])

**Spec.** `ax(i) = "<the i-th BRA axiom>"` for `i = 0..N`.

In our DerivF we have ~30 axioms (axI, axFst, axSnd, axConst,
axComp, axComp2, axLift, axPost, axFan, axKT, axRecLf, axRecNd,
axRecPLf, axRecPNd, axIfLfL, axIfLfN, axTreeEqLL, axTreeEqLN,
axTreeEqNL, axTreeEqNN, axGoodstein, axRefl, axEqTrans, axEqCong1,
axEqCongL, axEqCongR, axK, axS, axNeg, axExFalso — 30).

Guard's `th(4y) = ax(y)` feeds an enumeration index; `ax` returns
the code of the y-th axiom.  Since some of our axioms take
parameters (e.g. `axI (t : Term)`), each *parameterised* axiom
needs an encoding that treats `t` / `f` / etc. as additional inputs
in the index.  Two honest options:

**Option A.** `ax : Fun1` takes a single tree index and produces a
specific axiom code by numerical case-split.  Works for axioms
without parameters; for parametric axioms, fold the parameters into
the index tree via `Pair`.  ~200 lines.

**Option B.** Separate `ax` into a bundle of Fun1/Fun2 — one per
axiom schema — and let `th`'s mod-4 dispatch branch on which
schema applies.  Larger but flat structure.  ~400 lines.

**Open question:** Guard's `ax` is conceptually one functor indexed
by natural number.  Our parametric axioms don't fit that shape
directly; Option A is closer to Guard but trickier to encode.
Settle this before coding `ax`.

### subT (Ex 24 [4])

**Spec.**

    subT (reify (nd (code(var n)) codeA)) (reify codeB)
      = reify (codedSubst codeA (code(var n)) codeB)

(where `codedSubst` is our meta-level substitution on Tree, defined
in `BRA/Term.agda`).  Argument 1 is the packed substitution data
`Pair (code(var n)) codeA`; argument 2 is the target code.

**Definition sketch.**

    stepSubT : Fun2
    stepSubT = Fan checkEq continuation IfLf
      where
        checkEq      = Fan (Lift (Comp Fst Fst)) (Lift Snd) TreeEq
        continuation = Fan (Lift (Comp Snd Fst)) (Post Snd Pair) Pair

    subT : Fun2
    subT = RecP stepSubT

**Proof outline.** Meta-induction on the tree `codeB`:
- `codeB = lf`: `reify = O`; `axRecPLf stepSubT _`.  ~3 lines.
- `codeB = nd a b`: `axRecPNd stepSubT _ _ _`, unfold `stepSubT`,
  split on `TreeEq (reify codeVarN) (reify (nd a b))`:
  - match (`O`): `axIfLfL` returns `codeA`.  Meta-level
    `codedSubst` at a matching node also returns `repl = codeA`.
    ~10 lines.
  - no-match (`Pair O O`): `axIfLfN` returns `recs`.  Meta-level
    `codedSubst` recurses into children.  IH on both.  ~20 lines.

Estimate ~100 lines total.  This is the first real test of whether
the combinator style scales past trivial projections.

### sub (Ex 24 [8])

**Spec.** `sub(z, "P") = "S^{x₀}_{ss…s0_z} P"` — substitute the
numeral of z for `x₀` in `P`.

**Definition.** With `cor` and `subT` in hand:

    sub : Fun2
    sub (z , reify codeP)
      = ap2 subT (ap2 Pair (reify (code (var 0))) (ap1 cor z))
                 (reify codeP)

Implemented as a Fun2 using `Fan`, `Post`, and a few constants for
`reify (code (var 0))`:

    sub = Post subTFixedVar0 ...   -- ~one line combinator

Derivation uses `subT`'s defining equation + `cor`'s behavior on
numerals (= reified trees).  ~30 lines.

## Thm 12 — target signature

**See `BRA/THM12-NOTES.md` for the full interpretation** (Def 12 as
meta-level `codeT`/`codeFT`, `cor` appearing symbolically on both
sides of the equation, base-cases-per-primitive proof structure).
This section states only the target signature and the downstream
consumers of each `*Def` lemma.

Guard Thm 12 (p.16): for every 1-ary BRA functor `f`, there exists
`D_f` such that

    th(D_f(x)) = "f(x) = f(x)"    (underlined, per Def 12)

In BRA form, with `codeFT` the underlined-code function from
`BRA/THM12-NOTES.md`:

    thm12Sing : (f : Fun1) ->
      Sigma Fun1 (\ Df ->
        Deriv (atomic (eqn (ap1 th (ap1 Df (var zero)))
                           (codeFT (atomic (eqn (ap1 f (var zero))
                                                (ap1 f (var zero))))))))

**Downstream consumers of `mpFDef` / `indFDef` / `subTDef` / `axDef`
inside the Thm 12 proof:**

- Primitive base cases (`f = I`, `Fst`, `Snd`, `KT t`): close by
  `axDef` at the matching axRefl schema index.  `mpFDef` /
  `indFDef` / `subTDef` not used.
- Step case `Comp p q`: given IH for `p` and `q`, produce `D_{Comp
  p q}` such that `th(D_{Comp p q}(x))` reduces through th's
  dispatch to the code of "Comp p q (x) = Comp p q (x)".  Uses
  `mpFDef` to splice the two sub-proofs (each coded as a `"f(x) =
  f(x)"` in implication form) and `axDef` for `axComp`.
- Step case `Comp2 h p q`: same shape with the binary `axComp2`
  schema.
- Step case `Rec z s`: uses `indFDef` to close a tree-induction
  step (requires the `v1 = zero` convention from the indF
  decision) and `subTDef` to substitute the recursive result for
  the Rec argument.

Proof by **meta-induction on the definition of `f`** (Guard p.16:
"a meta-induction on the length of the definition of a functor").

Estimate ~400-600 lines total, ~100 of which is `*Def`-consumption
plumbing in the step cases.

## Thm 13 — corollary

Given `f(x) = y`, derive `th(D_f(x)) = "f(_x_) = y"` (Guard p.16).
Transport Thm 12's RHS via `axEqCong1 cor + mpF` on the hypothesis.

**`mpFDef` consumed here** to close the transport: after
`axEqCong1 cor` gives `cor(f(x)) = cor(y)` in implication form
and we have the hypothesis, `mpF`'s defining equation is invoked
to reduce `ap2 mpF (hypothesis-code) (implication-code)` to the
conclusion code.

~50-100 lines once Thm 12 exists.

## Thm 14 and Gödel II — closing

Thm 11 (first incompleteness, p.15): construct `j = "th(x₁) ≠
sub(x₀, x₀)"` and prove `j = sub(j, j)` is valid but unprovable.

Thm 14 (Gödel II, p.16): formalise Thm 11's proof inside BRA.
Uses Thm 13 at both `th` and `sub`.

**Downstream consumers in the Thm 14 chain:**

- `subDef` (the Ex 24 [8] lemma) is used to evaluate
  `sub(j, j)` inside the coded chain — specifically where the
  diagonal step requires substituting the numeral of `j` for `x₀`
  in `j` itself.
- `mpFDef` is used repeatedly to splice the multiple `"a ⊃ b"`
  codes produced by Thm 13 into a single chain of coded modus
  ponens applications.
- Thm 13 at `th` handles the `th(j) = …` half of the diagonal.
- Thm 13 at `sub` handles the `sub(j, j) = …` half.

Estimate ~300-500 lines for Gödel II once Thm 12/13 are in place.

## `th` — the 4-case enumerator (Def 12 p.15)

    th(4y)   = ax(y)
    th(4y+1) = sb(KKy, LKy)(th(Ly))
    th(4y+2) = mp(th(Ky), th(Ly))
    th(4y+3) = ind(th(Ky), th(Ly))

In our tree setting, the mod-4 dispatch becomes a tag-nd nesting
(four tree shapes at the top level: `lf`, `nd lf lf`, `nd (nd lf lf)
lf`, `nd lf (nd lf lf)` say, or whatever encoding we pick).  `th =
Rec fallback stepTh` where stepTh dispatches on the input shape.
~100 lines.

## Proposed commit order

1. `[BRA-ex24-ind]`    — indF, parallel to mpF.
2. `[BRA-ex24-subT]`   — subT, first real RecP proof.
3. `[BRA-ex24-sub]`    — sub built on subT + cor.
4. `[BRA-ex24-ax]`     — ax; decide Option A vs. B first.
5. `[BRA-th]`          — th as the mod-4 dispatcher.
6. `[BRA-thm12-base]`  — Thm 12 base cases (D_I, D_Fst, etc.).
7. `[BRA-thm12-step]`  — Thm 12 step cases (Comp, Comp2, Rec).
8. `[BRA-thm12-binary]` — Thm 12 for Fun2.
9. `[BRA-thm13]`       — Thm 13 corollary.
10. `[BRA-godelI]`     — Gödel I via Thm 12 + th's fixed-point.
11. `[BRA-godelII]`    — Gödel II via Thm 14.

Expected total: 1500-2500 lines of Agda across ~15 files, each
file typecheck < 10s.  Consistent with Session G's estimate.

## Hard constraints (unchanged)

- `~/.cabal/bin/agda-2.9.0 --safe --without-K --exact-split`
- No postulates, no holes
- Per-file typecheck < 10 s
- One named lemma per paper step
- No with-abstraction (`eqCong` / `eqSubst` instead)
- No new Deriv constructors for things definable from existing
  axioms + Rec/RecP combinators

## Open questions to resolve before coding

1. **indF's `v'` convention.** Options A / B / C / D above.  Leaning
   A (fix `v1 = zero`, pure projection parallel to `mpF`), but user
   is thinking.  Blocks indF.
2. **ax's encoding.** Option A (one indexed Fun1) vs. Option B
   (per-schema bundle).  Depends on how `th` uses `ax` in the mod-4
   dispatch and whether the parametric axioms matter at Thm 12.
   Blocks ax.
3. **Gödel pairing encoding.**  `th` uses `K`/`L` to decompose its
   input index.  In trees these are `Fst`/`Snd`.  Confirm that
   Guard's `J(KKy, LKy)` style composes cleanly to `Fst (Fst y)`,
   `Snd (Fst y)`, etc.  If yes, no extra work; if no, we need a
   tree-level J/K/L wrapper.  Blocks `th`.
4. **Def 12 / Thm 12 interpretation** (from `BRA/THM12-NOTES.md`).
   Four sub-questions listed there for user review before any Thm
   12 code is written.
