# Next Session: Internalize coreTree (Nelson Connection)

## Context

The coreTree quotient technique gives a purely structural proof of
incompleteness: no semantics, no models, just tag discrimination on
a syntactic invariant preserved by all proof operations. This is
philosophically aligned with Nelson's program of eliminating semantic
assumptions from metamathematics.

## The Nelson Connection

Nelson's key structures map directly to ours:

| Nelson (PRA/Balrog)                | Our system (binary trees)           |
|------------------------------------|-------------------------------------|
| chi-translation (formulas -> terms)| Already equational (no formulas)    |
| Eq(x,y) = (x-y)+(y-x)            | eqTree : Tree -> Tree -> Tree       |
| C(x,y,z) (case function)          | cas t u v                           |
| Characteristic terms               | codeTerm / coreTree                 |
| Rank/level bounds on proofs        | coreTree structural invariant       |
| S* proves own consistency          | coreInv-thS-all (for ALL trees)     |
| PRA proves bounds for each proof   | thS equations hold definitionally   |

### The sharp question (Nelson's Section 9 transplanted)

Nelson's strategy: construct S* that proves its own consistency with
rank/level bounds. Then: P proves S* consistent, S* arithmetizes Q,
and by Kritchman-Raz, derive contradiction.

In our setting:
1. coreInv-thS-all proves consistency (meta-level)
2. If thS can INTERNALLY prove "coreTree(L) = coreTree(R) for my outputs",
   that would be self-consistency
3. Combined with Godel II, this creates tension:
   - System proves its own range restriction
   - But the range restriction implies unprovability of specific equations
   - If the system proves THAT, we approach Nelson's setup

## Goal: Internalize coreTree

Define `coreTreeTerm : Term 1` such that:
```
eval_env[t/0] coreTreeTerm = coreTree t
```

### Design

coreTree dispatches on the tag of its input:
- tag = tagCase: check if scrutinee code = nd lf lf; if so, recurse on cU
- tag = tagRec: same for cZ
- all others: return input unchanged

This is implementable as:
```
coreTreeTerm = rec v0 (identity for lf) stepTerm
```
where stepTerm checks the tag via nested cas.

The recursion structure: coreTree is structurally recursive on Tree.
Since Tree = lf | nd a b, we use rec which gives us access to
the left child (tag), right child (payload), and recursive results.

BUT: coreTree recurses on a SUBTERM of the payload (cU inside
nd (nd lf lf) (nd cU cV)), not on the left or right child directly.
This means rec (which recurses on left and right children) does NOT
directly give us the recursive call we need.

### Solution approaches

**Approach A: Flatten via niter work-stack**
Similar to how eqTree was internalized: use niter with a work-stack
to traverse the tree, stripping cas-leaf/rec-leaf layers iteratively.

The work-stack state: the current code being stripped.
Each niter step: check tag, check scrutinee, extract cU or cZ, continue.
Clock: must be large enough to cover all stripping layers.

Since coreTree only strips ONE layer per call (cas-leaf or rec-leaf
with scrutinee = leaf), and each strip reduces tree size, the number
of strips is bounded by the tree depth. So a linearized clock works.

**Approach B: Direct rec with tag dispatch**
Use rec on the input tree. At each nd node:
- v0 = right child (payload), v1 = left child (tag)
- v2 = rec result on right, v3 = rec result on left

But we need to check: is this a cas-leaf or rec-leaf code?
If tag = tagCase and payload starts with (nd lf lf) ...:
  return the coreTree of cU (which is inside payload)
But cU is a sub-subtree, and rec only gives results for children.

So we'd need the rec on the RIGHT child to have already computed
coreTree of the payload's subterms. This works if the payload is
nd (nd lf lf) (nd cU cV) and rec on the payload gives us
rec-result-on-right = nd (coreTree cU) (coreTree cV).

Actually: rec on (nd (nd lf lf) (nd cU cV)):
- left = nd lf lf, right = nd cU cV
- rec-on-right = nd (rec-on-cU) (rec-on-cV)

If coreTree on sub-trees equals rec-on-sub-trees (by IH), then
rec-on-right = nd (coreTree cU) (coreTree cV).

So for the cas-leaf case: we want coreTree cU. This is the LEFT
child of rec-on-right. We extract it with cas!

**This approach works.** The step term:
1. Check if v1 (tag) = tagCase:
   - Check if left child of v0 (payload) = nd lf lf (scrutinee = codeTerm leaf)
   - If yes: extract coreTree(cU) from v2 (rec result on payload)
     v2 = rec result on payload. If payload = nd scrut (nd cU cV),
     then rec-right = rec on (nd cU cV) = nd (coreTree cU) (coreTree cV).
     But v2 is rec on the RIGHT child of the input, which is the payload.
     Hmm, need to be more careful about what rec gives us.

Actually: the input to coreTree is `nd tag payload`. rec on this gives:
- v3 = left child = tag
- v2 = right child = payload
- v1 = rec result on tag (not useful)
- v0 = rec result on payload

Wait, rec binds 4 variables: rec t z s where s has vars:
- v0 = rec result on right child
- v1 = rec result on left child
- v2 = right child
- v3 = left child

So for input `nd tag payload`:
- v3 = tag, v2 = payload, v1 = rec(tag), v0 = rec(payload)

For the cas-leaf check:
- v3 = tag. Check if = tagCase.
- v2 = payload. Check if starts with nd (nd lf lf) (nd cU cV).
- v0 = rec(payload) = result of applying coreTreeTerm recursively to payload.

If payload = nd scrut rest, then rec(payload) depends on how rec
handles payload. Since rec recurses structurally:
- rec(nd scrut rest) uses: left=scrut, right=rest, rec(scrut), rec(rest)

We need: when tag=tagCase and scrut=nd lf lf and rest=nd cU cV,
return coreTree(cU). rec(rest) = rec(nd cU cV) which gives
nd (coreTree cU) (coreTree cV) if the recursion is correct.
Then coreTree(cU) = left child of rec(rest) = cas (rec(rest)) ???

This is getting nested. The key issue: rec gives us rec(payload),
but payload = nd scrut (nd cU cV), so rec(payload) processes
payload as a node with left=scrut and right=(nd cU cV).

I think Approach A (niter work-stack) is cleaner for internalization.

## Concrete plan

1. Define coreTreeTerm : Term 1 using niter (iterative stripping)
2. Prove coreTreeTerm-correct : eval[t/0] coreTreeTerm = coreTree t
3. Explore: can thS prove coreTree invariance internally?

## Key files

- Rose/ThInt.agda: thS, thTerm, thGenFull (pattern for internal terms)
- Rose/TreeEqInt.agda: linearize, niter work-stack (pattern for niter)
- Rose/Godel.agda: coreTree definition, CoreInv, unprovability results
- Rose/Code.agda: tags, codeTerm structure
