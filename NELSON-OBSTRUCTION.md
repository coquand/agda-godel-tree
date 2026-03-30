# The Nelson Obstruction: Congruence vs CoreInv

## Result (formally verified in Rose/Godel.agda)

**CoreInv is not stable under congruence.**

Equivalently: `coreTree` is not a congruence for the equational theory.

### Counterexample (nelsonObstruction)
```
a = cas leaf leaf (pair leaf leaf)    -- evals to lf, codeTerm tag = tagCase
b = leaf                              -- evals to lf, codeTerm tag = tagLeaf

eval(a) = eval(b) = lf               -- semantically equal
codeTerm(a) ≠ codeTerm(b)            -- syntactically different
coreTree(codeTerm(a)) ≠ coreTree(codeTerm(b))  -- invariant sees the difference
```

Adding congruence (cas a u v = cas b u v from a = b) produces an
equation where CoreInv fails: coreTree strips one side but not the other.

## What This Means

### The incompatibility
Two principles cannot coexist:

1. **Contextual closure (congruence)**: if a = b then f(a) = f(b)
2. **Syntactic invariant (CoreInv)**: coreTree depends on exact code shape

### Why Godel I/II work
CoreInv works BECAUSE the system lacks congruence. The invariant
detects a property of proofs (tag structure of term codes) that is
NOT stable under contextual reasoning. This is what makes it powerful
enough to exclude equations from the range of thS.

### Why internalization fails
The meta-proof of CoreInv uses eqCong coreTree (congruence). To
internalize it, thS would need congruence. But adding congruence
destroys CoreInv. The system cannot add the reasoning power needed
for self-reflection without destroying the property being reflected on.

## The Two Layers

| Layer | What it sees | Stable under congruence? |
|-------|-------------|------------------------|
| Semantic (eval) | Tree values | Yes |
| Syntactic (codeTerm/coreTree) | Code structure | **No** |

CoreInv lives at the syntactic layer. Congruence operates at the
semantic layer. The gap between them is where internalization fails.

## Connection to Nelson

Nelson's program: show that a system cannot prove its own consistency
without collapse. Our result:

- The system has a structural invariant (CoreInv) that implies consistency
- Internalizing the invariant requires congruence
- Congruence destroys the invariant
- Therefore: the system cannot internalize its own consistency proof

This is analogous to Nelson's claim but in a purely equational,
formally verified setting over binary trees.

## Precise Mathematical Statement

**Theorem (Nelson Obstruction).** Let thS be the theorem enumerator
with refl, sym, trans, casLeaf, recLeaf. Let CoreInv be the coreTree
invariant. Then:

1. CoreInv holds for all thS outputs (coreInv-thS-all).
2. CoreInv implies unprovability of specific equations (core-unprovable).
3. If congruence for cas is added to thS, CoreInv fails (nelsonObstruction).
4. The meta-proof of CoreInv uses congruence (eqCong coreTree in trans case).

Therefore: CoreInv characterizes exactly the weakness of the system.
It holds because reasoning is restricted, and it would fail if
reasoning were strengthened to the point of self-applicability.

## Open Questions

1. **Maximal safe congruence**: What is the largest fragment of
   congruence that preserves CoreInv? (Shape-preserving congruence:
   only allow f(a) = f(b) when codeTerm(a) and codeTerm(b) have
   the same outer tag.)

2. **Alternative invariants**: Is there a DIFFERENT invariant that
   is both (a) congruence-stable and (b) strong enough to exclude
   false equations? If not, this is a deeper impossibility.

3. **Quotiented codes**: If we work modulo evaluation (using eval-codes
   instead of raw codeTerm), does a congruence-stable invariant exist?

## Files
- Rose/Godel.agda: nelsonObstruction (line ~775), coreTree, CoreInv
- NEXT-SESSION-CONGRUENCE.md: detailed analysis of the congruence question
