# Rose Binary-Tree Formalization: Next Session

## What exists (13 files in Rose/, all typecheck, no postulates, no holes)

### Core infrastructure
- `Rose/Base.agda` — Nat, Fin, Eq, Maybe, Sigma, Ordering, compareNat, eqCong3
- `Rose/Tree.agda` — `data Tree : lf | nd`
- `Rose/Term.agda` — `Term : Nat -> Set` with var, leaf, pair, cas (2 binders), rec (4 binders)
- `Rose/Equation.agda` — closed equations `Term 0 = Term 0`

### Substitution and evaluation
- `Rose/Rename.agda` — rename with liftRen, liftRen2, liftRen4
- `Rose/Subst.agda` — subst with liftSubst, singleSubst, subst0
- `Rose/Eval.agda` — environment-based eval (mutual: evalEnv/evalCas/evalRec), TrueEq
- `Rose/Reify.agda` — reify : Tree -> Term 0, eval-reify round-trip proof

### Coding (frozen scheme: nd TAG PAYLOAD, tags = natCode 0..4)
- `Rose/Code.agda` — codeTerm, decodeTerm, codeEquation, decodeEquation
- `Rose/SubstAt.agda` — thick, injectTerm (via rename absurdFin), substAt using Fin index

### Coded substitution (Rose Section 3.4 analogue)
- `Rose/CodedSubst.agda` — thickNatCode, thickVarResult, codedSubst (tree-level)
- `Rose/CodeProps.agda` — codeTerm-rename (general renaming invariance), codeTerm-injectTerm
- `Rose/CodedSubstCorrect.agda` — **main theorem**: `codedSubst (codeTerm r) (finToNat k) (codeTerm t) = codeTerm (substAt k r t)`

## The obstruction

`thickNatCode` requires simultaneous recursion on two trees (index and varcode):
```
thickNatCode (suc k) (nd b t) = maybeMap (nd b) (thickNatCode k t)
```

Our `rec` recurses on ONE tree; free variables (including the varcode) stay fixed.
So `rec(k, z, s)` gives `thickNatCode(k, ORIGINAL_varcode)`, not `thickNatCode(k, snd(varcode))`.

This is a known limitation: primitive recursion on one argument cannot express all primitive recursive functions of multiple arguments without composition/iteration combinators.

## The fix: add `niter` (nat-code iterator with carried state)

Add to Term.agda:
```agda
niter : Term n -> Term n -> Term (suc (suc n)) -> Term n
```

Computation:
```
niter lf       state step = state
niter (nd a k) state step = niter k (step[k/1, state/0]) step
```

This iterates `step` along a right-chain (natCode), threading `state` through.
At each step: var 0 = current state, var 1 = remaining tail.
The step can transform the state using cas on the state.

For thickNatCode(index, varcode), use:
- state = varcode (the thing being peeled)
- iterate on index: at each step, peel one layer from the state via cas

```
niter index varcode (cas (var fz) lf (pair leaf (var fz)))
```

Wait — this peel step needs refinement to handle the Maybe encoding and the (nd b) wrapping. But the point is: niter lets the state CHANGE at each step, which is exactly what thickNatCode needs.

## Exact next steps

1. Add `niter` to `Rose/Term.agda` (2 binders: tail, state)
2. Extend `Rose/Rename.agda`, `Rose/Subst.agda` — add liftRen2/liftSubst2 cases for niter
3. Extend `Rose/Eval.agda` — add evalNiter (iterative, not recursive on subtrees)
4. Extend `Rose/Code.agda` — add tag 5 for niter, extend codeTerm/decodeTerm
5. Define internal thickNatCode using niter (in Rose/Internal/)
6. Prove eval of internal term = thickNatCode
7. Build internal codedSubst from internal thickNatCode
8. Prove correctness, chain with codedSubst-correct

## Design constraints (from CLAUDE.md)
- `{-# OPTIONS --safe --without-K --exact-split #-}`
- No postulates, no holes
- ASCII only, small files, explicit definitions
- Semi-implicit style (implicit type params, explicit where it helps)

## Binding convention for niter step (2 binders)
- var 0 = current state
- var 1 = remaining tail (right subtree of current natCode node)
- var (2+k) = outer variable k
