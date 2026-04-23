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

## Remaining functors — sketches

Each sketch gives the Guard spec, the intended Fun1/Fun2 expression,
and a very rough size estimate.  Definitions and derivations are
**not written**; design only.

### indF (Ex 24 [5])

**Spec.** `ind("P(0)", "P(x₀) ⊃ P(sx₀)") = "P(x₀)"`.

In tree form (Guard's `s(x₀)` is our `Pair a b`, but the specific
induction format uses only `sx₀` as a node):

    indF (reify (codeFormula P0)) (reify (codeFormula pxImpPsx))
      = reify (codeFormula Px₀)

where `pxImpPsx = P(x₀) imp P(Pair a b)` in our naming.  The
extraction is **structural** exactly like `mpF`: pull apart the
second argument's imp-encoding and return its first half (the
hypothesis `P(x₀)`), i.e. `Fst (Snd b)`.  So:

    indF = Post (Comp Fst Snd) (Post Snd Pair)

Same shape as `mpF`, same style of derivation.  ~20 lines each of
def + proof.

*(Flag: the Guard spec delivers "P(x₀)" as the *conclusion* of the
inference, not a projection of one of the inputs.  If actually
`ind` is meant to build the code of P(x₀) from the code of P(0)
alone (not the induction step), the combinator is just
`Lift (something)` stripping the leading `s…` marker from arg 1.
Verify the exact spec against p.14 before coding.)*

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

Guard Thm 12 (p.16): for every 1-ary BRA functor `f`, there exists
`D_f` such that

    th(D_f(x)) = "f(_x_) = f(_x_)"

where `_x_` is the underlined notation meaning "in the code, `x` is
replaced by `num(x)`" (Guard Def 12, p.16).  Similarly for binary
functors.

In BRA form:

    thm12 : (f : Fun1) -> Sigma (Fun1) (\ Df ->
      (x : Term) ->
        Deriv (atomic
          (eqn (ap1 th (ap1 Df (reify (code x))))
               (reify (codeFormula
                 (atomic (eqn (ap1 f (<underlined x>))
                              (ap1 f (<underlined x>)))))))))

The precise meaning of "<underlined x>" is: `reify (codedSubst
(ap1 cor x) (code (var 0)) (code (f (var 0))))`, i.e. the code
obtained by substituting `cor(x)` for `x₀` inside the code of
`f(x₀)`.  This is exactly where `subT` earns its keep.

Proof is by **meta-induction on the definition of `f`** (Guard
proves this by induction on functor length).  Base cases for each
primitive Fun1 (`I`, `Fst`, `Snd`, `KT t`); step cases for `Comp`,
`Comp2`, `Rec`.  Each base case gives a specific `D_I`, `D_Fst`,
etc., mostly built from `axRefl`-style functors + subT/sub
plumbing.

Estimate ~400-600 lines.

## Thm 13 — corollary

Given `f(x) = y`, derive `th(D_f(x)) = "f(_x_) = y"`.  Transport
Thm 12's RHS via `axEqCong1 cor + mp` on the hypothesis.  ~50-100
lines once Thm 12 exists.

## Thm 14 and Gödel II — closing

Thm 11 (first incompleteness, p.15): construct `j = "th(x₁) ≠
sub(x₀, x₀)"` and prove `j = sub(j, j)` is valid but unprovable.

Thm 14 (Gödel II, p.16): formalise Thm 11's proof inside BRA.
Uses Thm 13 at both `th` and `sub`.

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

1. **indF's exact spec.** Is it a projection (extracting P(x₀) from
   `P(x₀) imp P(sx₀)`) or a construction (building P(x₀) from
   P(0) + induction hypothesis)?  Read guard15 p.14 item [5] again
   with fresh eyes.
2. **ax's encoding.** Option A (one indexed Fun1) vs. Option B
   (per-schema bundle).  Depends on how th uses ax in the mod-4
   dispatch and whether the parametric axioms matter at Thm 12.
3. **Gödel pairing encoding.**  `th` uses `K`/`L` to decompose its
   input index.  In trees these are `Fst`/`Snd`.  Confirm that
   Guard's `J(KKy, LKy)` style composes cleanly to `Fst (Fst y)`,
   `Snd (Fst y)`, etc.  If yes, no extra work; if no, we need a
   tree-level J/K/L wrapper.
