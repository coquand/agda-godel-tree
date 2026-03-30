# Next Session: True-but-Unprovable Godel I

## Goal

Prove that a specific TRUE closed equation is not in the range of thS
for any valid proof tree. This completes Godel I.

## Candidate: niter-leaf equation

```
niter leaf leaf (pair (var 1) (var 0)) = leaf
```

Both sides evaluate to lf (the niter clock is lf, so state lf is returned).
The equation is TRUE but thS cannot prove it (no niter axioms).

## Why the semantic argument fails

ThSResult gives: thS(y) = nd (codeTerm l) (codeTerm r) with eval l = eval r.
If thS(y) = niterLeafEqCode, then l = niter expression, r = leaf, and
eval l = eval r = lf. This is TRUE — no contradiction from soundness.

Soundness only excludes FALSE equations. For TRUE equations, we need
structural range exclusion.

## The structural argument (sketched)

Key property: codeTerm(niter ...) has tag tagNiter. codeTerm(leaf) has
tag tagLeaf = lf. These are structurally different (nd vs lf).

For thS to produce nd (codeTerm(niter...)) (codeTerm leaf):
- No base form has tagNiter on the left (refl has tagLeaf/tagPair, casLeaf
  has tagCase, recLeaf has tagRec, default has tagLeaf).
- Through swap of casLeafCode(codeTerm(niter...), codeTerm V): left becomes
  codeTerm(niter...) (tag tagNiter). But right becomes nd tagCase (...),
  not codeTerm leaf.
- Through transCode to fix the right: middle must match. The right of
  the swapped form (nd tagCase ...) must equal the left of the second
  operand. If the second is casLeafCode(codeTerm leaf, codeTerm V'):
  its left = nd tagCase (nd (nd lf lf) (nd (codeTerm leaf) (codeTerm V'))).
  For middle match: codeTerm(niter...) = codeTerm leaf inside the structure.
  But tagNiter = nd lf (nd lf (nd lf (nd lf (nd lf lf)))) != lf = tagLeaf.
  Contradiction by nd-vs-lf.

This argument blocks at every depth: any trans chain eventually requires
codeTerm(niter expr) = codeTerm(leaf) in a middle position, which is
absurd by tag discrimination.

## What to formalize

### Approach A: Direct induction on ValidProof

```agda
niterLeaf-unprovable : (y : Tree) -> ValidProof y ->
  Not (Eq (thS y) niterLeafEqCode)
```

By induction on ValidProof:
- Base cases (refl, casLeaf, recLeaf, defaults): structural mismatch with
  niterLeafEqCode by tag/structure discrimination.
- Sym case: need IH excluding both niterLeafEqCode AND its swap.
- Trans case: the hard one. Need to show no transCode composition gives
  niterLeafEqCode. Use the middle-matching constraint + tag discrimination.

Challenge: the sym and trans cases require excluding a FAMILY of forms,
not just one. May need an auxiliary predicate characterizing what thS
CAN produce (a "range predicate") and showing niterLeafEqCode is outside.

### Approach B: Range predicate

Define a predicate RangeOK : Tree -> Set that characterizes all possible
thS outputs from valid proofs, closed under swap and transCode. Show:
1. Every base form satisfies RangeOK
2. swap preserves RangeOK
3. transCode preserves RangeOK
4. niterLeafEqCode does NOT satisfy RangeOK

The predicate could be: "the left side's tag is in {tagLeaf, tagPair, tagCase, tagRec}"
(never tagNiter). This is preserved by swap (just exchanges sides) and
transCode (left comes from first operand or defaults to tagLeaf).

Wait — through swap, the LEFT becomes the RIGHT of a sub-output. The right
of casLeafCode is u = codeTerm U, which CAN have tag tagNiter. So this
simple predicate is NOT preserved by swap.

Need a more refined predicate. Perhaps: "when the left has tag tagNiter,
the right does NOT have tag tagLeaf." This blocks niterLeafEqCode
specifically. But this is ad-hoc.

### Approach C: Tag-pair predicate

Define: LeftRightTags : Tree -> Tree -> Set that constrains which (leftTag, rightTag)
pairs can appear. The allowed pairs from base forms:
- refl: (tagLeaf, tagLeaf), (tagPair, tagPair), etc. (both same)
- casLeaf: (tagCase, any)
- recLeaf: (tagRec, any)
- default: (tagLeaf, tagLeaf)

Through swap: (any, tagCase), (any, tagRec), (tagLeaf, tagLeaf), (tagPair, tagPair)

Through trans: (left of first, right of second) when middle matches;
otherwise (tagLeaf, tagLeaf) from defaultCode.

The constraint: if left has tag tagNiter, it came from swap of a casLeaf/recLeaf
where the data U was a niter expression. Then the right has tag tagCase/tagRec.
For transCode to change the right to tagLeaf: the second operand must have
right with tag tagLeaf. Its left must match the first operand's right (tagCase/tagRec).
So the second operand has left tag tagCase/tagRec and right tag tagLeaf.
This can come from casLeafCode(codeTerm leaf, V) or recLeafCode(codeTerm leaf, S).
Their left is nd tagCase (nd (nd lf lf) ...) or nd tagRec (nd (nd lf lf) ...).
The middle match requires: first's right = second's left.
First's right (from swap of casLeaf(niterExpr, V)) = nd tagCase (nd (nd lf lf) (nd (codeTerm niterExpr) (codeTerm V))).
Second's left = nd tagCase (nd (nd lf lf) (nd (codeTerm leaf) (codeTerm V'))).
For match: codeTerm niterExpr = codeTerm leaf. ABSURD (tag mismatch).

This is the core argument. It should be formalizable as ~50 lines.

## Key files to read

- Rose/ThInt.agda: thS, ValidProof, ThSResult, thS-valid, codeTermEvalEq
- Rose/Godel.agda: current godelI (false equations), godelSentence-lf-false
- Rose/Code.agda: codeTerm, tags (tagNiter, tagCase, tagRec, tagLeaf, tagPair)
- Rose/TreeEq.agda: eqTree, eqTree-sound

## Key imports needed

- tagNiter from Rose.Code
- nd-injL, nd-injR from Godel.agda (already defined)
- ThSResult, thSR, thS-valid from ThInt.agda
