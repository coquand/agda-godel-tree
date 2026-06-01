# BRA — Goedel's Incompleteness Theorems in Basic Recursive Arithmetic

An Agda formalization of Goedel's First and Second Incompleteness
Theorems for **Basic Recursive Arithmetic** (BRA), a Guard-style
equational system on binary trees with explicit substitution and
primitive recursion (Guard, *Lecture notes on recursive arithmetic*,
Argonne, 1963).

The headline results sit in `BRA4/GoedelI.agda` and
`BRA4/Thm/Thm14GodelII.agda`:

```agda
godelI  : Deriv G          -> Deriv P_false   -- Goedel I
godelII : Deriv ConSchema  -> Deriv falseF    -- Goedel II
```

If the diagonal sentence `G` is provable in BRA, BRA is inconsistent;
likewise if BRA's encoding of its own consistency `ConSchema` is
provable in BRA, BRA is inconsistent.  Constructive, Agda-checked, no
postulates.

## Papers

- [**Gödel II** — A formalisation of Gödel's Second Incompleteness
  Theorem for the Basic Recursive Arithmetic of Church and
  Guard](goedelII-summary.pdf) (source: `BRA4/goedelII-summary.tex`).
- [**Chaitin–Gödel I** — an object-level diagonal program and an
  internal implication](cgfun-cgfalse-note.pdf) (source:
  `BRA4/cgfun-cgfalse-note.tex`).

A crucial ingredient (easy to miss in the source) is the asymmetric
role of the numeral function `num` / `cor` (= Guard's underline
`x_`): for a primitive `f` of arity 1, `f(num x)` IS the code of a
BRA term (the term "`f` applied to the numeral of `x`"), but
`num(f x)` is the numeral of the *value* `f x` and in general is
\*not\* the code of any such syntactic term.  Theorem 12 internalises
the equation between these two trees inside BRA, and that bridge is
what makes the whole Goedel II chain go through.  See
`BRA4/goedelII-summary.tex`, section "Numerals: the asymmetry…".

A further conceptual point is that intermediate steps of Theorem 14
prove `Deriv (atomic (eqn (thmT t) u))` where `u` is *not*
`codeFormula P` for any formula `P` — the chain manipulates
substituted-codes (with `cor x` placed in variable slots) through
ordinary BRA equational reasoning, only collapsing to a literal
`codeFormula falseF` at the closure.  See `BRA4/goedelII-summary.tex`,
section "What is going on at the encoded layer: a remarkable internal
proof".

For the mathematical write-up see `BRA4/goedelII-summary.tex` (compile
to `goedelII-summary.pdf`).

## Edition

This repository tracks the **BRA4 edition** of the development.  BRA4
keeps the single-`Term` setup of the prior BRA2 edition (codes are
exactly value-shaped Terms via an `IsValue : Term -> Set` predicate,
with `reify : Tree -> Term` collapsed to the identity) and adds, on
top of the diagonal G2 chain, the infrastructure for the Chaitin /
Kritchman–Raz route to a second proof of G2: a universal step-
interpreter `evalU` with its mu-loop, the open Π₁ Kolmogorov formula
`Kgt`, the object-N pigeonhole engine `CountingObj`, and the
Parsons-Skolemised Σ₁-induction skeleton (`SpikeParsons`, `SpikeD`).
The diagonal `godelII` ships unconditionally; the Chaitin/KR route is
an independent, second-pass enrichment.

Earlier editions (`BRA/`, `BRA2/`) are preserved on disk under their
own directories for reference but are not tracked in git.

## Discipline

- `--safe --without-K --exact-split` on every file.
- ASCII only.
- Zero postulates, zero holes, no `with`-abstraction, no dot patterns
  (one exception: `.O` / `.a .b` in `IsValue` pattern matches, the
  canonical syntax for matching against an indexed family's index).
- camelCase for every let-binding (mid-identifier `_` collides with
  Agda's mixfix grammar).

## What's in `BRA4/`

The Agda development sits entirely under `BRA4/`.  Headline modules:

| File                                    | Role                                                          |
|-----------------------------------------|---------------------------------------------------------------|
| `BRA4/GoedelI.agda`                     | Goedel I: `godelI : Deriv G -> Deriv P_false`.                |
| `BRA4/Thm/Thm14GodelII.agda`            | Goedel II: `godelII : Deriv ConSchema -> Deriv falseF`.       |
| `BRA4/Thm/Thm14.agda`, `Thm14F.agda`, `Thm14Step1..5.agda` | The Theorem 14 cascade (Guard's section 3.5).  |
| `BRA4/Thm12.agda`, `BRA4/Thm12/…`       | Theorem 12 closure (15 Param + Parts pairs).                  |
| `BRA4/ThmT.agda`, `BRA4/ThmTAt*.agda`   | The proof checker `thmT` and the per-rule dispatchers.        |
| `BRA4/Base.agda`, `Code.agda`, `Tags.agda` | Base re-exports, formula/term codes, dispatcher tags.      |
| `BRA4/EvalU.agda`, `EvalUStep.agda`, `EvalUCorrect.agda`, `EvalUMu.agda` | Universal step-interpreter + mu-loop (Chaitin route). |
| `BRA4/KFormula.agda`, `KRecog.agda`, `KOut.agda`, `KSearch.agda`, `KClash.agda`, `KGodel1.agda`, `KDiag.agda` | The open Π₁ Kolmogorov formula `Kgt` and the conditional Chaitin G1 barrier. |
| `BRA4/CountingObj.agda`                 | The object-`N` pigeonhole engine (KR-C/KR-D counting).        |
| `BRA4/goedelII-summary.tex`             | Mathematical write-up.                                        |

### Sound `thmT`

The verifier `BRA4/ThmT.agda` together with its per-rule dispatchers
(`BRA4/ThmTAt*.agda`) is a validating decoder: on any input it returns
either `codeFormula(P)` for some derivable formula `P`, or the
explicit safe default `codeTriv = code(0=0)`.  Each premise-consuming
dispatcher (`mp`, `ruleInst`, `ruleSym`, `cong1`, `congL`, `congR`,
`ruleTrans`, `ruleInst2`, `ruleIndNat`, …) discriminates the input
shape, returns `codeTriv` on a malformed cell, and only otherwise
assembles the conclusion code.  Consequence: `thmT(y) ≠
codeFormula(falseF)` for any `y` unless BRA is actually inconsistent,
so `ConSchema` carries its intended meaning.

## Build

Requires Agda 2.7+ (the development is checked under both 2.7 and
2.9.0).

```sh
agda --safe BRA4/Thm/Thm14GodelII.agda    # Goedel II (the headline)
agda --safe BRA4/GoedelI.agda             # Goedel I
```

Cold rebuild of the headline chain takes ~30 s on a recent laptop;
cached typechecks are under 1 s.  No postulates, no holes:

```sh
$ grep -rn '^postulate' BRA4/   # empty
$ ls BRA4/Thm/Thm14GodelII.agdai # exists after build
```

## Repository layout

| Path                              | Status                                                             |
|-----------------------------------|--------------------------------------------------------------------|
| `BRA4/`                           | The active codebase (tracked).                                     |
| `BRA4/goedelII-summary.tex`       | Project paper (tracked).                                           |
| `bra-godelII.tex`                 | Top-level project writeup (tracked).                               |
| `README.md`                       | This file (tracked).                                               |
| `BRA/`, `BRA2/`                   | Legacy editions (untracked, kept on disk for reference).           |
| `old/`                            | Legacy Agda, tex, notes, scratch — not tracked, kept on disk only. |

The reference PDFs (Rose, Ryan, Simmons, guard15, Guard 1963 lecture
notes, Chwistek 1939) sit at the repository root but are not tracked
in git; they are expected to be present locally for cross-reference.
