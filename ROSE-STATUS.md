# Rose Formalization: Status and Roadmap

## Overview

This project formalizes Godel's incompleteness theorems in an Agda-based
binary tree calculus, following Rose's system B* and Guard's 1963 lecture notes.
All proofs are `--safe`, with no postulates, no holes, and no `with`-abstraction.

The data type is binary trees: `lf` (leaf) and `nd a b` (node). The term language
has intrinsically scoped terms with `var`, `leaf`, `pair`, `cas` (case analysis),
`rec` (primitive tree recursion), and `niter` (right-spine iteration).

## What Has Been Done

### Layer 1: Core Infrastructure (prior sessions)

| File | Contents |
|------|----------|
| `Base.agda` | Nat, Fin, Eq, Maybe, Sigma, arithmetic lemmas |
| `Tree.agda` | Binary trees: `lf`, `nd` |
| `Term.agda` | Intrinsically scoped terms (var, leaf, pair, cas, rec, niter) |
| `Eval.agda` | Environment-based evaluation, `eval`, `TrueEq` |
| `Equation.agda` | Closed equations between terms |
| `Reify.agda` | `reify : Tree -> Term 0`, `eval-reify : eval (reify t) = t` |
| `Code.agda` | `codeTerm : Term n -> Tree`, tags, decoding |
| `Rename.agda` | Renaming with lifting under binders |
| `Subst.agda` | General substitution, `subst0` |
| `SubstAt.agda` | Positional substitution, `thick`, `substAt`, `injectTerm` |
| `CodedSubst.agda` | Tree-level coded substitution `codedSubst0` |
| `CodeProps.agda` | `codeTerm-rename`, `codeTerm-injectTerm` |
| `CodedSubstCorrect.agda` | `codedSubst-correct : codedSubst = codeTerm . substAt` |
| `EvalSubst.agda` | Substitution lemma: `eval (substAt fz r t) = evalEnv [eval r] t` |
| `Internal.agda` | Internal variable substitution `internalCodSubstVar`, trichotomy, full correctness |

### Layer 2: Diagonal and Fixed Point (current sessions)

| File | Key Results |
|------|-------------|
| `DiagCode.agda` | `codeReify : Tree -> Tree`, `diagCode : Tree -> Tree`, `diagCode-correct` |
| `FixedPoint.agda` | `diag : Term 1 -> Term 0`, `diag-code : codeTerm (diag A) = diagCode (codeTerm A)` |

### Layer 3: Axioms and Theorem Enumeration

| File | Key Results |
|------|-------------|
| `Axiom.agda` | 7 axiom schemes (cas-leaf, rec-leaf, niter-leaf, reflexivity, cas-pair, rec-pair, niter-pair) with soundness |
| `ThEnum.agda` | Full theorem enumerator `thEq`/`th` with axioms + symmetry + transitivity, `thEq-sound` |

### Layer 4: Internal Tree Equality

| File | Key Results |
|------|-------------|
| `TreeEq.agda` | Metalevel `eqTree`, `matchSub` + correctness, `eqTree-sound` |
| `TreeEqInt.agda` | `eqTreeTerm : Term 2` via linearize + niter work-stack; evaluation lemmas (`linearize-eval`, `niter-eval`, `extractFlag-eval`) |
| `EqCheckCorrect.agda` | `eqCheck-main : extractFlagMeta (runNiter ...) = eqTree a b` (the full correctness proof for internal tree equality) |

### Layer 5: Internal Theorem Enumerator with Transitivity

| File | Key Results |
|------|-------------|
| `ThInt.agda` | `thS : Tree -> Tree` (metalevel, with transitivity), `thTerm : Term 1` (internal, with transitivity), `thTerm-correct : evalWith t thTerm = thS t` (fully proved) |

### Layer 6: Godel Sentence Construction

| File | Key Results |
|------|-------------|
| `Godel.agda` | `godelSchema`, `godelSentence`, `godelCode` (code-level fixed point), `godelEval` (semantic fixed point) |

## Key Theorems Proved

1. **Coded substitution correctness** (`codedSubst-correct`):
   `codedSubst (codeTerm r) k (codeTerm t) = codeTerm (substAt k r t)`

2. **Diagonal code correctness** (`diagCode-correct`):
   `diagCode (codeTerm t) = codeTerm (substAt0 (reify (codeTerm t)) t)`

3. **Fixed-point identity** (`diag-code`):
   `codeTerm (diag A) = diagCode (codeTerm A)`

4. **Internal tree equality correctness** (`eqCheck-main`):
   The niter-based work-stack tree comparison computes `eqTree`.

5. **Internal theorem enumerator correctness** (`thTerm-correct`):
   `evalWith t thTerm = thS t` for all trees t.

6. **Godel code-level fixed point** (`godelCode`):
   `codeTerm (godelSentence target) = diagCode (codeTerm (godelSchema target))`

7. **Godel semantic fixed point** (`godelEval`):
   `eval (godelSentence target) = eqTree (thS (codeTerm (godelSchema target))) target`

## What Is Left for Godel I

### Current State

The fixed-point machinery is complete. The internal theorem enumerator `thTerm`
computes `thS` (reflexivity + symmetry + transitivity) with a full correctness proof.
The Godel sentence construction and fixed-point theorems work over this `thS`.

### Missing for Full Godel I

1. **Stronger axiom system in thS**: The current `thS` has reflexivity, symmetry,
   and transitivity. For Rose/Guard Godel I, it needs:
   - Computation axioms (cas-leaf, rec-leaf, niter-leaf) with term decoding
   - Congruence rules (if a=b then pair a t = pair b t, etc.)
   - Possibly: the cas-pair and rec-pair computation rules

2. **Soundness of thS**: A proof that every output of `thS` is the code of a
   true equation. Currently, `ThEnum.agda` has soundness for the full `thEq`
   (which includes axioms + symmetry + transitivity with tree equality checking).
   The `thS` in `ThInt.agda` needs its own soundness proof.

3. **Self-referential target**: The current `godelSentence` takes an arbitrary
   `target : Tree`. For the true Godel sentence, `target` should equal
   `codeTerm G` (where G = godelSentence target). This requires solving the
   fixed-point equation `t = diagCode (codeTerm (godelSchema t))`, which is
   computable but hasn't been formalized.

4. **Unprovability argument**: Once (1)-(3) are in place:
   - G is true (eval G gives a specific tree value)
   - G is not in the range of thS (by the diagonal argument + soundness)
   - Therefore G is a true-but-unprovable equation

### Concrete Steps

- **Step A**: Add computation axioms to `thS` and internalize in `thTerm`. Each
  axiom requires a cas branch in `thStep5Full` plus decoding logic.
- **Step B**: Prove soundness of `thS` (every output codes a true equation).
- **Step C**: Compute the self-referential target and prove the fixed-point identity.
- **Step D**: State and prove: "there exists a closed equation that is true but
  not in the range of thS."

## What Is Left for Godel II

Godel II says: the system cannot prove its own consistency (i.e., cannot prove
that `lf = nd lf lf` is not a theorem).

### Missing for Godel II

1. **Everything from Godel I** (above).

2. **Internal provability predicate**: A term `Prov : Term 1` such that
   `eval (substAt0 (reify c) Prov) = trueT` iff c is the code of a provable
   equation. This requires internalizing the search over all proof trees
   (or using Guard's Df-operator approach).

3. **Guard's Df-operators** (Theorem 12): For each functor f, a term Df such that
   `th(Df(x)) = "f(x) = f(x)"`. These are built by meta-level induction on f
   and compose provability witnesses.

4. **Formalized provability reasoning**: Prove internally that if G is provable,
   then thS produces G's code. This is the "provability implies provability-of-provability"
   step (Hilbert-Bernays-Lob condition).

5. **Derivation of contradiction**: If the system proves its own consistency,
   derive a contradiction using the formalized Godel I + provability reasoning.

### Key References

- Rose, H.E. "Subrecursion" -- Sections 3.1-3.7 for B* system, Theorem 17 (diagonal),
  Theorem 18 (Godel II).
- Guard, J.R. (1963) "Lecture notes on recursive arithmetic" -- Theorems 11-14
  (Godel I, Df-operators, Godel II).

## File Dependency Graph

```
Base
  |
  +-- Tree
  |     |
  |     +-- Term
  |     |     |
  |     |     +-- Equation
  |     |     |
  |     |     +-- Rename
  |     |     |     |
  |     |     |     +-- Subst
  |     |     |     |
  |     |     |     +-- SubstAt
  |     |     |
  |     |     +-- Eval
  |     |     |     |
  |     |     |     +-- Reify
  |     |     |     |
  |     |     |     +-- EvalSubst
  |     |     |
  |     |     +-- Code
  |     |           |
  |     |           +-- CodedSubst
  |     |           |
  |     |           +-- CodeProps
  |     |           |
  |     |           +-- CodedSubstCorrect
  |     |
  |     +-- TreeEq
  |     |     |
  |     |     +-- TreeEqInt
  |     |           |
  |     |           +-- EqCheckCorrect
  |     |
  |     +-- DiagCode
  |     |
  |     +-- Internal
  |
  +-- Axiom
  |
  +-- ThEnum
  |
  +-- FixedPoint
  |
  +-- ThInt (imports TreeEqInt, EqCheckCorrect)
  |
  +-- Godel (imports ThInt, FixedPoint, DiagCode, EvalSubst, TreeEq)
```
