# Next Session: The Congruence Obstruction

## The Precise Question

The proof of CoreInv (coreTree L = coreTree R for all thS outputs)
uses exactly ONE nontrivial step: **congruence for coreTree**.

In the transitivity case (Lemma 31 / coreInv-trans):
```
coreTree L1 = coreTree R1    (IH on first proof)
coreTree R1 = coreTree L2    (eqCong coreTree applied to R1 = L2)
coreTree L2 = coreTree R2    (IH on second proof)
```

The middle step is: from R1 = L2, derive coreTree(R1) = coreTree(L2).
At the metalevel, this is just eqCong. But internally:

**Can thS prove coreTree(x) = coreTree(y) given a proof that x = y?**

## Why This Is the Decisive Question

If YES: CoreInv can be internalized. The system proves its own
structural invariant. Combined with Godel I, this creates the
Nelson-style tension: the system proves it can't prove certain
equations, which is a form of self-consistency.

If NO: CoreInv is inherently metalevel. The system cannot reason
about its own range restriction. This is itself a strong result:
a structural obstruction to self-reflection.

## Analysis: When Is Congruence Available?

thS currently has: refl, sym, trans, casLeaf, recLeaf.

Congruence for a function f means: from x = y, derive f(x) = f(y).

### Case A: f is a computation axiom
If f(x) reduces via casLeaf or recLeaf, then f(x) = f(y) might
follow from computation + trans. E.g., cas leaf x v = x and
cas leaf y v = y, so from x = y: cas leaf x v = x = y = cas leaf y v.

### Case B: f is coreTree (the critical case)
coreTree is defined by: strip cas-leaf/rec-leaf wrappers.

For a SPECIFIC x = y (where both sides are term codes): coreTree
might not have a computation axiom. coreTree checks the TAG of its
input, which is a specific tree structure (tagCase, tagRec, etc.).

The check "is the tag tagCase?" is done by matchSub at the term
level. matchSub is built from cas/niter. So coreTree is a
COMPUTABLE function in the system.

### The Key Insight
If coreTree is represented as coreTreeTerm : Term 1, and if
the system can prove computation axioms for ARBITRARY functions
(not just cas/rec), then congruence follows from:

```
coreTreeTerm(x) = coreTreeTerm(x)    (refl)
x = y                                 (given)
coreTreeTerm(x) = coreTreeTerm(y)    (need congruence!)
```

But thS does NOT have a general congruence rule. It has specific
computation axioms (casLeaf, recLeaf) plus refl/sym/trans.

## What thS Would Need

To internalize eqCong coreTree, thS would need one of:

1. **General congruence axiom**: from proof of a = b, derive
   f(a) = f(b) for any term f. This is a SCHEMA parameterized
   by f, which would require extending thS significantly.

2. **Specific coreTree congruence**: hardcode coreTree as an axiom.
   This is circular (the invariant uses the function that thS
   would need to know about).

3. **Derive it from computation**: show that coreTree(x) = coreTree(y)
   follows from x = y using only casLeaf + recLeaf + trans.
   This IS possible if coreTree's computation can be decomposed
   into cas/rec steps that thS already proves.

## Option 3: The Viable Path

coreTree = niter (linearize v0) v0 stripStep   (niter version)
coreTree = cas (rec v0 z s) leaf v1            (rec version)

Both use cas and rec. If x = y, then:
- rec x z s and rec y z s should give the same result
  (by induction + congruence for rec)
- cas (rec x z s) leaf v1 and cas (rec y z s) leaf v1 same
  (by congruence for cas)

But congruence for CAS and REC requires:
- cas a u v = cas b u v when a = b (congruence in scrutinee)
- rec a z s = rec b z s when a = b (congruence in recursion arg)

These are NOT currently axioms of thS. They would need to be ADDED.

## Concrete Test

Add congruence axioms for cas and rec to thS:
- vpCongCas: from proof of a = b, derive cas a u v = cas b u v
- vpCongRec: from proof of a = b, derive rec a z s = rec b z s

Then: congruence for coreTree follows by induction on the
coreTree computation (cas/rec decomposition).

If these axioms preserve CoreInv (coreTree invariant still holds
with the extended proof system), then we have a RICHER thS that
can internalize its own consistency proof.

If they DON'T preserve CoreInv: the extension breaks the invariant,
and we have a Nelson-style obstruction: adding the reasoning power
needed for self-reflection destroys the structural property that
makes self-reflection meaningful.

## The Nelson Fork

This is EXACTLY Nelson's setup:

- The system has a structural invariant (CoreInv / rank-level bounds)
- To prove the invariant internally, the system needs more power
- Does the added power preserve or break the invariant?

If PRESERVES: system proves own consistency → tension with Godel II
If BREAKS: system cannot prove own consistency → strong incompleteness

## Files
- Rose/Godel.agda: coreTree, CoreInv, coreTreeTerm/coreTreeRec
- Rose/ThInt.agda: thS, ValidProof, thS-valid

## Next Steps
1. Add vpCongCas and vpCongRec to ValidProof in ThInt.agda
2. Check if CoreInv still holds (extend coreInv-thS with new cases)
3. If yes: build internal congruence for coreTree
4. If no: document the obstruction (Nelson-style result)
