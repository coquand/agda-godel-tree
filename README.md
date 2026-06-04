# Goedel's Incompleteness Theorems in Basic Recursive Arithmetic

An Agda formalization of Goedel's First and Second Incompleteness
Theorems for **Basic Recursive Arithmetic** (T) — Church's basic
recursive arithmetic in the formulation of Guard ([*Lecture Notes on
Recursive Arithmetic*](Guard-Recursive-Arithmetic.pdf), Princeton,
1962–63): a Skolem-style equational
calculus of recursive functions on the natural numbers, presented in
Hilbert style (axiom schemas + rules) — numerals built from `O`
and the successor `s`, with the combinators `o, u, v, C, R`.

The headline results sit in `T4/GoedelI.agda` and
`T4/Thm/Thm14GodelII.agda`, and both conclude the **same** false
formula `falseF = (O = s O)` (i.e. `0 = 1`):

```agda
godelI  : Deriv G          -> Deriv falseF   -- Goedel I
godelII : Deriv ConSchema  -> Deriv falseF   -- Goedel II
```

If the diagonal sentence `G` is provable in T, T is inconsistent;
likewise if T's encoding of its own consistency `ConSchema` is
provable in T, T is inconsistent.  Constructive, Agda-checked, no
postulates.

## Papers

- [**Gödel II** — A formalisation of Gödel's Second Incompleteness
  Theorem for the Basic Recursive Arithmetic of Church and
  Guard](goedelII-summary.pdf) (source: `T4/goedelII-summary.tex`).
- [**Chaitin–Gödel I** — an object-level diagonal program and an
  internal implication](ChaitinGodel.pdf) (source:
  `T4/cgfun-cgfalse-note.tex`).
- [**Surprise–Gödel II** — a surprise-examination (sorites) proof of
  Gödel's Second Incompleteness Theorem, via Chaitin–Gödel I and the
  Kritchman–Raz descent](SurpriseGodelII.pdf) (source:
  `T4/surprise-gii.tex`).

## Source notes

The calculus T being formalised is Church's basic recursive arithmetic
as presented in J. R. Guard's [**Lecture Notes on Recursive
Arithmetic**](Guard-Recursive-Arithmetic.pdf) (Recursive Arithmetic
Seminar, Princeton, 1962–63).  These are the lecture notes the
development follows; the write-up `T4/goedelII-summary.tex` cites them
by page (e.g. Def. 14, p. 19).

A crucial ingredient (easy to miss in the source) is the asymmetric
role of the numeral function `num` / `cor` (= Guard's underline
`x_`): for a primitive `f` of arity 1, `f(num x)` IS the code of a
T term (the term "`f` applied to the numeral of `x`"), but
`num(f x)` is the numeral of the *value* `f x` and in general is
\*not\* the code of any such syntactic term.  Theorem 12 internalises
the equation between these two terms inside T, and that bridge is
what makes the whole Goedel II chain go through.  See
`T4/goedelII-summary.tex`, section "Numerals: the asymmetry…".

A further conceptual point is that intermediate steps of Theorem 14
prove `Deriv (atomic (eqn (thmT t) u))` where `u` is *not*
`codeFormula P` for any formula `P` — the chain manipulates
substituted-codes (with `cor x` placed in variable slots) through
ordinary T equational reasoning, only collapsing to a literal
`codeFormula falseF` at the closure.  See `T4/goedelII-summary.tex`,
section "What is going on at the encoded layer: a remarkable internal
proof".

For the mathematical write-up see `T4/goedelII-summary.tex` (compile
to `goedelII-summary.pdf`).

## Edition

This repository tracks the **T4 edition** of the development.  T4
uses a single-`Term` syntax in which codes (Gödel numbers) are
themselves Terms, so the proof predicate `thmT`, the diagonal, and the
formula it codes all live in one type, and adds, on
top of the diagonal G2 chain, the infrastructure for the Chaitin /
Kritchman–Raz route to a second proof of G2: a universal step-
interpreter `evalU` with its mu-loop, the open Π₁ Kolmogorov formula
`Kgt`, the object-N pigeonhole engine `CountingObj`, and the
Parsons-Skolemised Σ₁-induction skeleton (`SpikeParsons`, `SpikeD`).
The diagonal `godelII` ships unconditionally; the Chaitin/KR route is
an independent, second-pass enrichment.

## Discipline

- `--safe --without-K --exact-split` on every file.
- ASCII only.
- Zero postulates, zero holes, no `with`-abstraction, no dot patterns.
- camelCase for every let-binding (mid-identifier `_` collides with
  Agda's mixfix grammar).

## What's in `T4/`

The Agda development sits entirely under `T4/`.  Headline modules:

| File                                    | Role                                                          |
|-----------------------------------------|---------------------------------------------------------------|
| `T4/GoedelI.agda`                     | Goedel I: `godelI : Deriv G -> Deriv falseF`.                 |
| `T4/Thm/Thm14GodelII.agda`            | Goedel II: `godelII : Deriv ConSchema -> Deriv falseF`.       |
| `T4/Thm/Thm14.agda`, `Thm14F.agda`, `Thm14Step1..5.agda` | The Theorem 14 cascade (Guard's section 3.5).  |
| `T4/Thm12.agda`, `T4/Thm12/…`       | Theorem 12 closure (15 Param + Parts pairs).                  |
| `T4/ThmT.agda`, `T4/ThmTAt*.agda`   | The proof checker `thmT` and the per-rule dispatchers.        |
| `T4/Base.agda`, `Code.agda`, `Tags.agda` | Base re-exports, formula/term codes, dispatcher tags.      |
| `T4/EvalU.agda`, `EvalUStep.agda`, `EvalUCorrect.agda`, `EvalUMu.agda` | Universal step-interpreter + mu-loop (Chaitin route). |
| `T4/KFormula.agda`, `KRecog.agda`, `KOut.agda`, `KSearch.agda`, `KClash.agda`, `KGodel1.agda`, `KDiag.agda` | The open Π₁ Kolmogorov formula `Kgt` and the conditional Chaitin G1 barrier. |
| `T4/CountingObj.agda`                 | The object-`N` pigeonhole engine (KR-C/KR-D counting).        |
| `T4/goedelII-summary.tex`             | Mathematical write-up.                                        |

### Sound `thmT`

The verifier `T4/ThmT.agda` together with its per-rule dispatchers
(`T4/ThmTAt*.agda`) is a validating decoder: on any input it returns
either `codeFormula(P)` for some derivable formula `P`, or the
explicit safe default `codeTriv = code(0=0)`.  Each premise-consuming
dispatcher (`mp`, `ruleInst`, `ruleSym`, `cong1`, `congL`, `congR`,
`ruleTrans`, `ruleInst2`, `ruleIndNat`, …) discriminates the input
shape, returns `codeTriv` on a malformed cell, and only otherwise
assembles the conclusion code.  Consequence: `thmT(y) ≠
codeFormula(falseF)` for any `y` unless T is actually inconsistent,
so `ConSchema` carries its intended meaning.

## Build

Requires Agda 2.7+ (the development is checked under both 2.7 and
2.9.0).

```sh
agda --safe T4/Thm/Thm14GodelII.agda    # Goedel II (the headline)
agda --safe T4/GoedelI.agda             # Goedel I
```

Cold rebuild of the headline chain takes ~30 s on a recent laptop;
cached typechecks are under 1 s.  No postulates, no holes:

```sh
$ grep -rn '^postulate' T4/   # empty
$ ls T4/Thm/Thm14GodelII.agdai # exists after build
```

## Repository layout

| Path                              | Status                                                             |
|-----------------------------------|--------------------------------------------------------------------|
| `T4/`                           | The active codebase (tracked).                                     |
| `T4/goedelII-summary.tex`       | Project paper (tracked).                                           |
| `Guard-Recursive-Arithmetic.pdf`  | Guard's lecture notes — the formalised source (tracked).           |
| `README.md`                       | This file (tracked).                                               |

The other reference PDFs (Rose, Ryan, Simmons, guard15, Chwistek 1939)
sit at the repository root but are not tracked in git; they are
expected to be present locally for cross-reference.
