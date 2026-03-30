# Next Session: Godel II a la Rose

## Goal

Follow Rose (1961) to prove Godel II entirely within the equational binary tree
calculus, without a formula layer or Loeb argument. See `rose-godelII.tex` for
the full plan and comparison with Rose's paper.

## Rose's proof structure (from the 1961 paper)

1. th(y) — theorem enumerator. **We have this:** thS in ThInt.agda.
2. Soundness: vl(x, th(y)) = 0. **We have this:** thS-valid / ThSResult.
3. Companion function e(y): from equation A=B, produce false companion A+B. **NOT YET.**
4. Consistency: th(y) != e(th(z)). **NOT YET** (but falseEq-never is close).
5. Representability (Theorems 14-17): substitution/numeral functions are represented by th. **NOT YET.**
6. Godel II (Theorem 18): self-referential undecidability via diagonal + representability. **NOT YET.**

## What exists and typechecks

- Rose/GodelII.agda (600 lines): Loeb-style Godel II (Guard approach, not Rose).
  Contains ProvEq, chi-translation, chiFormTerm — reusable infrastructure.
- Rose/Chi.agda (216 lines): Fixed chi connectives with eval-correctness proofs.
- Rose/Godel.agda: godelSentence, godelEval, falseEq-unprovable, falseEq-never,
  coreTree quotient, godelEq-lf-unprovable.
- Rose/ThInt.agda: thS, thTerm, thTerm-correct, ValidProof, ThSResult, thS-valid,
  dThS, eqTree-thS-lf, crBase, crStep (codeReify internalization pieces).

## Step 1: Companion function (start here)

Define comp : Tree -> Tree. Simplest version:

```
comp : Tree -> Tree
comp (nd L R) = nd (codeReify (nd L R)) (codeReify lf)
comp lf = defaultCode
```

This encodes "the equation code itself = lf", which is always false since
nd L R != lf. Both sides are valid term codes (codeReify produces codeTerm (reify ...)).

Then compTerm : Term 1 computing comp. And prove:
- comp produces a false equation when applied to any ThSResult output
- thS(y) != comp(thS(z)) for all y, z (Rose's Theorem 13)

This uses falseEq-never or a direct argument via ThSResult.

## Step 2: Consistency via companion

Package Step 1 as:
```
roseConsistency : (y z : Tree) -> Not (Eq (thS y) (comp (thS z)))
```

This is the purely object-level consistency theorem, no formula layer needed.

## Step 3: Internal codeReify

Build codeReifyTerm : Term 1 computing codeReify x from x.
ThInt.agda already has crBase and crStep which are the rec base/step for this.
Prove: evalWith x codeReifyTerm = codeReify x.

## Step 4: Godel sentence via companion

Using godelSchema/diag machinery, construct G such that:
  eval G = eqTree (thS c) (comp (thS c))
where c = codeTerm (godelSchema ...).

By eqTree-thS-lf and comp construction, eval G = falseT (true sentence).
By roseConsistency, the equation G = reify falseT is unprovable.

## Step 5: Representability (hard, maybe later)

Prove that comp o thS is representable: exists a proof tree whose thS output
encodes the representability equation. This is Rose's Theorems 14-17 and is
the hardest step. May require extending thS with cas-pair/rec-pair axioms.

## Key files to read

- Rose.pdf (the 1961 paper, 12 pages)
- rose-godelII.tex (the plan document)
- Rose/ThInt.agda (thS, ValidProof, ThSResult, dThS, crBase, crStep)
- Rose/Godel.agda (falseEq-unprovable, falseEq-never, coreTree, godelSentence)
- Rose/GodelII.agda (ProvEq, chiFormTerm — reusable infrastructure)
- Rose/DiagCode.agda (codeReify, codeReify-correct)

## Conventions

- --safe --without-K --exact-split on every file
- ASCII only, no with-abstraction
- Semi-explicit style (see CLAUDE.md)
- No postulates, no holes
