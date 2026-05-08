# BRA — Goedel's Incompleteness Theorems in Basic Recursive Arithmetic

An Agda formalization of Goedel's First and Second Incompleteness
Theorems for **Basic Recursive Arithmetic** (BRA), a Guard-style
equational system on binary trees with explicit substitution and
primitive recursion (Guard, *Lecture notes on recursive arithmetic*,
Argonne, 1963).

The headline results, in `BRA2/GoedelIIFull.agda` (and
`BRA2/Thm11.agda`):

```agda
thm11   : Deriv G   -> Deriv bot   -- Goedel I
godelII : Deriv Con -> Deriv bot   -- Goedel II
```

If the diagonal sentence `G` is provable in BRA, BRA is inconsistent;
likewise if BRA's encoding of its own consistency `Con` is provable in
BRA, BRA is inconsistent.  Constructive, Agda-checked, no postulates.

A crucial ingredient (easy to miss in the source) is the asymmetric
role of the numeral function `num` / `cor` (= Guard's underline
`x_`): for a primitive `f` of arity 1, `f(num x)` IS the code of a
BRA term (the term "`f` applied to the numeral of `x`"), but
`num(f x)` is the numeral of the *value* `f x` and in general is
\*not\* the code of any such syntactic term.  Theorem 12 internalises
the equation between these two trees inside BRA, and that bridge is
what makes the whole Goedel II chain go through.  See
`BRA2/godelI-II-summary.tex`, section "Numerals: the asymmetry…".

A further conceptual point is that intermediate steps of Theorem 14
prove `Deriv (atomic (eqn (thmT t) u))` where `u` is *not*
`codeFormula P` for any formula `P` — the chain manipulates
substituted-codes (with `cor x` placed in variable slots) through
ordinary BRA equational reasoning, only collapsing to a literal
`codeFormula bot` at the closure.  See `BRA2/godelI-II-summary.tex`,
section "What is going on at the encoded layer: a remarkable internal
proof".

For the mathematical write-up see `BRA2/godelI-II-summary.tex` (compile
to `godelI-II-summary.pdf`).

## Edition

This repository tracks the **BRA2 edition** of the development.  BRA2
collapses the prior Layer-1 / Layer-2 split (separate `Term` and
`Tree` datatypes) into a single `Term` datatype with an
`IsValue : Term -> Set` predicate certifying value-shape (codes are
exactly value-shaped Terms).  The map `reify : Tree -> Term` of the
prior edition is now the identity; substantive math is unchanged.

The legacy BRA edition is preserved on disk under `BRA/` for
reference but is not tracked in git.

## Discipline

- `--safe --without-K --exact-split` on every file.
- ASCII only.
- Zero postulates, zero holes, no `with`-abstraction, no dot patterns
  (one exception: `.O` / `.a .b` in `IsValue` pattern matches, the
  canonical syntax for matching against an indexed family's index).
- camelCase for every let-binding (mid-identifier `_` collides with
  Agda's mixfix grammar).

## What's in `BRA2/`

The Agda development sits entirely under `BRA2/`.  Headline modules:

| File                                    | Role                                                          |
|-----------------------------------------|---------------------------------------------------------------|
| `BRA2/GoedelIIFull.agda`                | Top-level `godelII : Deriv Con -> Deriv bot` (unconditional). |
| `BRA2/GoedelII.agda`                    | Compose module: takes the Theorem 14 contract, produces godelII. |
| `BRA2/Thm14Abstract.agda`               | Abstract Theorem 14 tower (Guard's section 3.5).              |
| `BRA2/Th14Step5.agda`                   | Concrete `constr5_final` + `step5_l`.                         |
| `BRA2/Thm12.agda`, `BRA2/Thm12/…`       | Theorem 12 closure (15 Param + Parts pairs).                  |
| `BRA2/Thm/ThmT.agda`                    | The proof checker `thmT` and all `thmTDispX` dispatchers.     |
| `BRA2/Sound*VProof.agda`                | Verifying bodies + eval-pass lemmas (sound `thmT`).           |
| `BRA2/Base.agda`, `Term.agda`, `Formula.agda`, `Deriv.agda` | Base system: terms, formulas, derivability, the `IsValue` predicate. |

### Sound `thmT`

The verifying-body cascade in `BRA2/Sound*` ensures that for every
inductive premise-consuming dispatcher `X` (`mp`, `ruleInst`,
`ruleSym`, `cong1`, `congL`, `congR`, `ruleTrans`, `ruleInst2`,
`ruleIndBT`), the body `body_X` is a verifying variant `body_X_v` of
the form

```
body_X_v = Post verifierX Pair
verifierX = Comp2 IfLf <discriminant> (Comp2 Pair (KT codeTriv) <assembly>)
```

On a malformed input the discriminant is a leaf and the body outputs
`codeTriv = falseT = code(0=0)`; on a Pair-shaped (well-formed) input
the body assembles the conclusion code as before.  Consequence:
`thmT(y)` is provably either `codeFormula(P)` for some formula `P`, or
the explicit safe default `codeTriv`.  In particular `thmT(y) ≠
codeFormula(bot)` for any `y` unless BRA is actually inconsistent, so
`Con` carries its intended meaning.

## Build

Requires Agda 2.7+ (the development is checked under both 2.7 and
2.9.0).

```sh
agda --safe BRA2/GoedelIIFull.agda
```

Cold rebuild takes ~30 s on a recent laptop; cached typechecks of the
headline file are under 1 s.  No postulates, no holes:

```sh
$ grep -rn '^postulate' BRA2/   # empty
$ ls BRA2/GoedelIIFull.agdai    # exists after build
```

## Repository layout

| Path                              | Status                                                             |
|-----------------------------------|--------------------------------------------------------------------|
| `BRA2/`                           | The active codebase (tracked).                                     |
| `BRA2/godelI-II-summary.tex`      | Project paper (tracked).                                           |
| `README.md`                       | This file (tracked).                                               |
| `BRA/`                            | Legacy BRA edition (untracked, kept on disk for reference).        |
| `old/`                            | Legacy Agda, tex, notes, scratch — not tracked, kept on disk only. |

The reference PDFs (Rose, Ryan, Simmons, guard15, Guard 1963 lecture
notes, Chwistek 1939) sit at the repository root but are not tracked
in git; they are expected to be present locally for cross-reference.
