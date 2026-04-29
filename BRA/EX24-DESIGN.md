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
| `sb`       | `subT`   | `BRA/SubT.agda` | ✓ done |
| `sub`      | `sub`    | `BRA/Sub.agda` | ✓ done |

Six functors total (Guard has eight; `sbt`/`sbf` dissolve under
tree-pairing since they existed only to decode prime-product lists
in Guard's natural-number encoding).

## Milestone driving the open questions: Thm 11 (Gödel I)

The four open questions below are judged by **what Thm 11 actually
needs**, not by what would be nice for an eventual Thm 14.

Thm 11 (Guard p.15): construct `j = "th(x_1) ≠ sub(x_0, x_0)"` and
prove `sub(j, j)` is unprovable.  Unprovability is a meta-Agda
argument:

- assume `pf : Deriv (sub(j, j))` with derivation-encoding `y_d`,
- by `ruleInst` on `pf` with `x_1 := numeral y_d`:
  `Deriv (th(numeral y_d) ≠ sub(numeral(code j), numeral(code j)))`,
- combine with a Deriv of `th(numeral y_d) = numeral(code(sub(j,j)))`
  (call this `enc`, see below) and a Deriv of
  `sub(numeral(code j), numeral(code j)) = numeral(code(sub(j,j)))`
  (subDef + corOfReify),
- get Deriv inconsistency; contradict meta-level Consistent.

So Thm 11 needs:

- `th` defined and dispatching correctly (Q1, Q2, Q3 below),
- `subDef` (✓), `corOfReify` (✓),
- `enc` -- a **Thm 12-lite for derivations only** (new, see
  `## enc` section), built by induction over `Deriv` constructors
  using `mpFDef` / `subTDef` / `axDef` / `indFDef` for splice steps.

Thm 11 does **not** need:

- Full Thm 12 (`∀f : Fun1. ∃D_f. th(D_f x) = code(f x = f x))`),
  which is for general primitive recursive functors -- needed for
  Thm 13 → Thm 14 (Gödel II), not Thm 11.

This narrows the path: resolve Q1/Q2/Q3 with the **cheapest option
that suffices for Thm 11**, defer Q4 to the Gödel II phase.

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

**Decision: Option A** (locked, judged against Thm 11).

`enc` (the Thm 12-lite for Gödel I) needs to handle the
`ruleIndBT P v1 v2 base step` constructor case via th's mod-4 ind
branch.  When *we* construct derivations for `enc` and Thm 11, we
choose `v1 = zero` freely.  Option A's projection-style indF
suffices.  Option C's full generality (handling arbitrary v1 in
user-supplied derivations) is not required by Thm 11.  If a Thm 12
case in the eventual Gödel II work forces wider v1, upgrade to C
then; for now A is the cheapest sufficient choice.

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

**Decision: Option A** (locked, judged against Thm 11).

`enc` walks Deriv constructor-by-constructor; for each axiom case
(axI, axFst, ..., axExFalso) it builds a tree-index `i_ax` and
relies on `axDef` at that index.  A single Fun1 indexed by a tree
(with parameters folded in via Pair) is sufficient and ~2× smaller
than Option B's per-schema bundle.  No Thm 11 case forces the flat
structure of B.  Pick A.

### subT (Ex 24 [4])  -- done

**Spec (built).**

    ap2 subT (ap2 Pair (reify (code (var n))) (reify codeA))
             (reify codeB)
      = reify (codedSubst codeA (code (var n)) codeB)

**`codedSubst` adjustment.**  The original asymmetric definition in
`BRA/Term.agda` (split test `treeEq a tagVar` / `treeEq b tgt`,
keeping `nd a b` unchanged when only the first matched) was replaced
with the symmetric whole-node form

    codedSubst repl varCode (nd a b) =
      boolCase (treeEq varCode (nd a b))
        repl
        (nd (codedSubst repl varCode a) (codedSubst repl varCode b))

This (a) matches `stepSubT`'s `TreeEq codeVarN orig` test exactly
and (b) takes `varCode = code (var n)` (the whole variable code) as
its target, matching the design spec.  Equivalent to the original
on well-formed term codes -- the only place `nd tagVar X` appears in
a code is at variable nodes, so the whole-node test reproduces the
asymmetric one.  No downstream consumers existed yet, so the change
was safe.

**Definition (built).**

    checkEqSubT : Fun2
    checkEqSubT = Fan (Lift (Comp Fst Fst)) (Lift Snd) TreeEq

    contSubT : Fun2
    contSubT = Fan (Lift (Comp Snd Fst)) (Post Snd Pair) Pair

    stepSubT : Fun2
    stepSubT = Fan checkEqSubT contSubT IfLf

    subT : Fun2
    subT = RecP stepSubT

**Proof structure (built).**  Meta-induction on the tree `codeB`:
- `codeB = lf`: 1 line via `axRecPLf`.
- `codeB = nd a b`: ~80 lines.  `axRecPNd`, then `axFan` on
  `stepSubT`.  `checkEqSubT` reduces to `TreeEq varT orig` (helper
  `checkEqAt`) then to `boolCase (treeEq varCode (nd a b)) O falseT`
  (helper `treeEqRed`, by meta-induction on two trees).  `contSubT`
  reduces to `Pair codeAT recs` (helper `contAt`).  Combine into a
  clean `IfLf`, dispatch via `ifLfDispatch`.  A `where`-bound
  `finishCase : (b : Bool) -> Deriv ...` case-splits on the boolean
  to align with `codedSubst`'s definitional unfolding.

**Actual size.**  268 lines, 0.086 s.  Larger than the ~100-line
estimate, mostly from typed-`let` bookkeeping in `checkEqAt`/
`contAt` (~30 lines each), `treeEqRed` + helpers (~40 lines), and
the `subTDef nd` body (~120 lines).  Confirmed: the combinator
style scales past trivial projections.  First real `RecP` proof.

### sub (Ex 24 [8])  -- done

**Spec (built).**  For any tree zTree and codeP:

    ap2 sub (reify zTree) (reify codeP)
      = reify (codedSubst (code (reify zTree)) (code (var 0)) codeP)

**Definition (built).**  Fixed `varCode0T = reify (code (var 0))`:

    leftSub  : Fun2
    leftSub  = Fan (Lift (KT varCode0T)) (Lift cor) Pair
    rightSub : Fun2
    rightSub = Post Snd Pair
    sub : Fun2
    sub = Fan leftSub rightSub subT

`leftSub a b = Pair varCode0T (cor a)` (subst data); `rightSub a b
= b` (target passes through); outer Fan applies `subT` to them.

**Proof structure (built).**  Linear chain: axFan unfold sub,
reduce leftSub via axFan + constF2Red + axLift, reduce rightSub via
axPost + axSnd, rewrite `ap1 cor z` via `corOfReify`, then close
with `subTDef zero corCode codeP`.

**Actual size.**  138 lines, 0.04 s.  In line with the ~30-line
estimate plus the typed-`let` overhead.

## `enc` — Thm 12-lite for Deriv (gating Thm 11)

Thm 11 needs an internalisation of *the proof relation itself*,
not of arbitrary primitive recursive functors.  This is strictly
weaker than Thm 12 and is a finite case-split, not a meta-induction
over functor definitions.

**Signature.**

    enc : (P : Formula) -> Deriv P ->
      Sigma Tree (\ y ->
        Deriv (atomic (eqn (ap1 th (reify y))
                           (reify (codeFormula P)))))

**Structure.**  One case per `Deriv` constructor (~30 cases):

- **Computation axioms** (axI, axFst, ..., axRecPNd, axIfLf*,
  axTreeEq*, axGoodstein, axRefl, axEqTrans, axEqCong*, axK,
  axS, axNeg, axExFalso): build `y = nd <ax-tag-shape> <param-encoding>`,
  Deriv from `axDef <encoded-index>`, then `th` reduces via the
  ax branch.  ~1-3 lines per case.
- **Structural rules** (ruleSym, ruleTrans, cong1, congL, congR):
  recurse via IH, splice with appropriate eq-axiom encodings.  These
  are derived in BRA but `enc` must still encode them: ruleTrans
  uses axEqTrans + 2 mp; cong1 uses axEqCong1 + 1 mp; etc.  Each
  ~5-10 lines using `mpFDef` to splice.
- **`mp`**: IH gives `(y_1, eq_1)` for `Deriv (P imp Q)` and
  `(y_2, eq_2)` for `Deriv P`.  Build `y = nd <mp-tag-shape> (Pair
  y_1 y_2)`.  `th(y)` reduces via mp branch to `mpF(th(y_1),
  th(y_2)) = mpF(code(P imp Q), code(P)) = code Q` by `mpFDef`.
- **`ruleInst x t`**: IH gives `(y_0, eq_0)` for `Deriv P`.  Build
  `y = nd <sb-tag-shape> (Pair (Pair (encode-x) (encode-t)) y_0)`.
  `th(y)` reduces via sb branch to `subT(...)(th(y_0))`, then
  `subTDef` finishes.
- **`ruleIndBT P v1 v2 base step`**: as discussed (Q1), choose
  v1 = zero in our usage.  IH gives encodings for `base` and
  `step`; build `y = nd <ind-tag-shape> (Pair y_base y_step)` and
  close via `indFDef`.
- **`ruleF`**: Schema F.  Most complex case -- gives uniqueness of
  Rec.  May need to be encoded via a sequence of axRefl + axRec*
  steps, or added to `ax` as a parametric axiom schema.  Decide
  when reaching this case.

**Estimate.** ~400-600 lines across one or two files.  Each Deriv
constructor case is small (1-10 lines) once `th`'s defining
equations exist.  The volume is in the case-count, not depth.

**Files.** `BRA/Enc.agda` (the lemma).  Possibly a small companion
`BRA/EncTags.agda` if the tag-shape constants need their own
namespace.

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

**Decision: tag-by-tree-shape, dispatch via Rec + IfLf** (locked,
judged against Thm 11).

The mod-4 trick doesn't translate directly to trees: there's no
arithmetic mod on `Tree`.  Instead, encode the four cases as four
distinguishable top-level tree shapes and dispatch via the Rec /
IfLf machinery we already have.  Concrete encoding (proposed):

    th(lf)               = ax(O)         -- degenerate base
    th(nd lf payload)    = ax(payload)              -- "tag 0" = ax
    th(nd (nd lf lf) p)  = sb(K1 p, K2 p)(th(L p))  -- "tag 1" = sb
    th(nd (nd lf (nd lf lf)) p) = mp(th(K p), th(L p))  -- "tag 2" = mp
    th(nd (nd (nd lf lf) lf) p) = ind(th(K p), th(L p)) -- "tag 3" = ind

(Exact tags TBD when coding -- shapes must be distinguishable by
nested IfLf on `Fst` of the input, and avoid collision with the
existing tag space in `BRA/Term.agda`.)

Built as `th = Rec th_lf_case stepTh` where `stepTh` is a Fun2
that on `(orig, recs)` does:
  1. `IfLf` on `Fst orig` to split "tag 0" from "tags 1-3";
  2. nested `IfLf` to refine within tags 1-3;
  3. each branch invokes the appropriate Ex 24 functor (`ax` /
     `subT` / `mpF` / `indF`) on the appropriate sub-trees of
     `Snd orig` and on the recursive results from `recs`.

J/K/L become `Fst`, `Snd`, `Comp Fst Snd`, etc. -- pure tree
projections.  No new tree-level J/K/L wrapper needed.

~100-150 lines.  This is the second real `RecP`/`Rec`-heavy file
(after `subT`); same combinator hygiene applies.

## Proposed commit order

**Phase 1 — Thm 11 (Gödel I).**

1. `[BRA-ex24-ind]`    — indF, Option A, parallel to mpF.
2. `[BRA-ex24-subT]`   — subT, first real RecP proof.  ✓ DONE
3. `[BRA-ex24-sub]`    — sub built on subT + cor.  ✓ DONE
4. `[BRA-ex24-ax]`     — ax, Option A (single Fun1 with Pair-folded params).
5. `[BRA-th]`          — th: tag-by-tree-shape, Rec + IfLf dispatch.
6. `[BRA-enc]`         — Thm 12-lite: enc walks Deriv constructors.
7. `[BRA-godelI]`      — Thm 11: diagonal `j` + meta-Agda unprovability.

**Phase 2 — Thm 14 (Gödel II), gated on Q4.**

8. `[BRA-thm12-base]`  — Thm 12 base cases (D_I, D_Fst, etc.).
9. `[BRA-thm12-step]`  — Thm 12 step cases (Comp, Comp2, Rec).
10. `[BRA-thm12-binary]` — Thm 12 for Fun2.
11. `[BRA-thm13]`       — Thm 13 corollary.
12. `[BRA-godelII]`     — Gödel II via Thm 14.

Expected total: 1500-2500 lines of Agda across ~15 files, each
file typecheck < 10s.  Phase 1 estimate: 800-1200 lines.

## Hard constraints (unchanged)

- `~/.cabal/bin/agda-2.9.0 --safe --without-K --exact-split`
- No postulates, no holes
- Per-file typecheck < 10 s
- One named lemma per paper step
- No with-abstraction (`eqCong` / `eqSubst` instead)
- No new Deriv constructors for things definable from existing
  axioms + Rec/RecP combinators

## Open questions — resolution status

All four questions above are judged against **what Thm 11 needs**
(see `## Milestone` section).

1. **indF's `v'` convention.**  ✓ RESOLVED.  Option A (fix
   `v1 = zero`, pure projection parallel to `mpF`).  Sufficient for
   `enc`'s ruleIndBT case in Thm 11.  Upgrade to C only if a Thm 12
   case in Phase 2 forces it.
2. **ax's encoding.**  ✓ RESOLVED.  Option A (single Fun1 indexed
   by tree, parametric axioms fold params via Pair).  ~2× smaller
   than Option B; Thm 11's `enc` only needs the dispatch to fire
   correctly per case, not flat structure.
3. **Gödel pairing encoding for `th`.**  ✓ RESOLVED.
   Tag-by-tree-shape with Rec + nested IfLf dispatch (see `## th`
   section).  J/K/L become `Fst`/`Snd`/`Comp Fst Snd` etc. -- no
   tree-level J/K/L wrapper needed.
4. **Def 12 / Thm 12 interpretation** (from `BRA/THM12-NOTES.md`).
   DEFERRED to Phase 2.  Thm 11 uses `enc` (Thm 12-lite for Deriv
   only), not full Thm 12 over arbitrary functors.  Resolve Q4
   before commit 8 (`[BRA-thm12-base]`).

## Open questions — Phase 2 only

A. **`ruleF` (Schema F) inside `enc`.**  The most awkward Deriv
   constructor for `enc`.  Two routes:  (a) encode it as a sequence
   of axRefl + axRec* steps inside `enc`'s ruleF case; (b) add a
   parametric `ruleF` schema to `ax` so `enc` closes via `axDef`.
   Decide when reaching that case in `[BRA-enc]`.
