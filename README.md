# BRA — Goedel's Incompleteness Theorems in Basic Recursive Arithmetic

An Agda formalization of Goedel's First and Second Incompleteness
Theorems for **Basic Recursive Arithmetic** (BRA), a Guard-style
equational system on binary trees with explicit substitution and
primitive recursion (Guard, *Lecture notes on recursive arithmetic*,
Argonne, 1963).

The headline results, in `BRA/GoedelIIFull.agda` (and
`BRA/Thm11.agda`):

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
`BRA/godelI-II-summary.tex`, section "Numerals: the asymmetry…".

For the mathematical write-up see `BRA/godelI-II-summary.tex` (compile
to `godelI-II-summary.pdf`).

## Discipline

- `--safe --without-K --exact-split` on every file.
- ASCII only.
- Zero postulates, zero holes, no `with`-abstraction, no dot patterns.
- camelCase for every let-binding (mid-identifier `_` collides with
  Agda's mixfix grammar).

## What's in `BRA/`

The Agda development sits entirely under `BRA/`.  Headline modules:

| File                                    | Role                                                          |
|-----------------------------------------|---------------------------------------------------------------|
| `BRA/GoedelIIFull.agda`                 | Top-level `godelII : Deriv Con -> Deriv bot` (unconditional). |
| `BRA/GoedelII.agda`                     | Compose module: takes the Theorem 14 contract, produces godelII. |
| `BRA/Thm14Abstract.agda`                | Abstract Theorem 14 tower (Guard's section 3.5).              |
| `BRA/Th14Step5.agda`                    | Concrete `constr5_final` + `step5_l`.                         |
| `BRA/Thm12.agda`, `BRA/Thm12/…`         | Theorem 12 closure (15 Param + Parts pairs).                  |
| `BRA/Thm/ThmT.agda`                     | The proof checker `thmT` and all `thmTDispX` dispatchers.     |
| `BRA/Sound*Proto.agda`, `Sound*VProof.agda` | Verifying bodies + eval-pass lemmas (sound `thmT`).       |
| `BRA/Base.agda`, `Term.agda`, `Formula.agda`, `Deriv.agda` | Base system: trees, terms, formulas, derivability. |

### Sound `thmT`

The verifying-body cascade in `BRA/Sound*` ensures that for every
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
agda BRA/GoedelIIFull.agda
```

Cold rebuild takes ~32 s on a recent laptop; cached typechecks of the
headline file are under 1 s.

## Repository layout

| Path                  | Status                                                             |
|-----------------------|--------------------------------------------------------------------|
| `BRA/`                            | The active codebase (tracked).                         |
| `BRA/godelI-II-summary.tex`       | Project paper (tracked).                               |
| `README.md`                       | This file (tracked).                                   |
| `old/`                | Legacy Agda, tex, notes, scratch — not tracked, kept on disk only. |

The reference PDFs (Rose, Ryan, Simmons, guard15, Guard 1963 lecture
notes, Chwistek 1939) sit at the repository root but are not tracked
in git; they are expected to be present locally for cross-reference.
