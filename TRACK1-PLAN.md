# Track 1: Derive Compositional Checker Axioms from Tree Induction

## Goal

Replace the 7 compositional checker axioms (currently constructors of
ProofBTA) with DERIVED theorems, using a single tree induction principle
plus a computation language inside the formula type.

The result: `goedel2-BTA` proved with only Hilbert S/K/mp/cgen/cinst
+ tree induction + CodeTerm computation laws. No checker-specific axioms.

## Current State

`BinaryTreeArith.agda` has `goedel2-BTA : ProofBTA ConBTA -> EmptyG2`
with 7 compositional checker axioms as constructors:

```
axChkMPct    -- mp rule (tag 33) preserves checker acceptance
axChkCinst   -- cinst rule (tag 37), parameterized by Formula
axChkEval    -- axEval rule (tag 36), parameterized by Formula
axChkSy      -- fceqSy rule (tag 39)
axChkTr      -- fceqTr rule (tag 38)
axSelfRef    -- self-reference (closed computation)
axPrfCong    -- fPrf congruence
```

Each is metatheoretically validated by `sd-meta-correct` (in
`SelfDestruct.agda`). The goal: make them theorems, not axioms.

## Why This Is Hard

The axioms are about `checkG`'s behavior on specific tags. To derive
them, the formula language must express `checkG`'s tag dispatch. The
current `FormulaBTA` has `fPrf` (abstract proof predicate) but no
way to talk about HOW `fPrf` works.

The fix: make `fPrf` DEFINED (not abstract) by expressing `checkG`
as a CodeTerm operation. Then the compositionality rules follow from
the DEFINITION of `checkG`, provable by computation.

## Architecture

### New file: `BTAComputation.agda`

This replaces `BinaryTreeArith.agda` with a system where the checker
is defined inside the formula language.

### Step 1: Extend CodeTerm (~80 lines)

Add to CodeTerm:

```agda
data CodeTermC : Set where
  ctVar   : CVar -> CodeTermC
  ctLit   : Code -> CodeTermC
  ctNode  : CodeTermC -> CodeTermC -> CodeTermC
  -- NEW: case analysis on Code structure
  ctCase  : CodeTermC -> CodeTermC -> CodeTermC -> CodeTermC
  -- NEW: left/right child extraction
  ctLeft  : CodeTermC -> CodeTermC
  ctRight : CodeTermC -> CodeTermC
  -- NEW: atom tag extraction
  ctTag   : CodeTermC -> CodeTermC
  -- NEW: Nat equality test on atoms
  ctEqNat : CodeTermC -> CodeTermC -> CodeTermC
```

Semantics of `ctCase`:
```
evalCTC env (ctCase e atomBranch nodeBranch) =
  case evalCTC env e of
    catom k   -> evalCTC (extendEnv env (catom k)) atomBranch
    cnode a b -> evalCTC (extendEnv (extendEnv env b) a) nodeBranch
```

The atom branch binds one variable (the atom tag k as catom k).
The node branch binds two variables (left child at cvs cvz, right
child at cvz).

Also extend: `liftCTC`, `substCTC0`, `evalCTC` for all new constructors.

### Step 2: Define checkG as a CodeTerm (~100 lines)

Define `ctCheckG : CodeTermC` as a CodeTerm that, when evaluated with
a code variable bound at cvz, computes checkGT's result.

The definition mirrors `checkG`'s 10-tag dispatch:

```
ctCheckG = ctCase (ctVar cvz)
  -- atom case: failCode
  (ctLit failCode)
  -- node case: variables are left=cvs cvz, right=cvz
  -- Dispatch on left child's tag
  (ctCase (ctVar (cvs cvz))
    -- left is atom: dispatch on tag value
    (tagDispatch (ctVar cvz) -- the tag (as catom k)
                 (ctVar ???) -- the payload (right child of original)
                 ???)        -- recursive results
    -- left is node: failCode (checkG rejects cnode(cnode(...),_))
    (ctLit failCode))
```

The tag dispatch uses nested `ctEqNat` for each of the 10 tags
(n30-n35, n36g-n39g).

**THE HARD PART: recursion.** `checkG` at tag 33 (mp) recursively
calls itself on sub-codes. In CodeTerm, there is no recursion
combinator. Options:

(a) Add `ctFold : CodeTermC -> CodeTermC -> CodeTermC -> CodeTermC`
    (primitive recursion on Code: atom case + node case with
    recursive results). This is the cleanest but requires careful
    de Bruijn binding management.

(b) Unroll to fixed depth. Since `sdCode` has depth 4, unrolling
    checkG to depth 4 suffices for the Goedel II derivation. This
    avoids general recursion but limits the result to bounded proofs.

(c) Use the fuel parameter. Define `ctCheckG(fuel)` by Nat recursion
    on fuel (requires Nat recursion in CodeTerm too).

**Recommendation: option (a).** Add `ctFold` as a primitive recursion
combinator for Code. Its semantics:

```
evalCTC env (ctFold target atomCase nodeCase) =
  fold (evalCTC env target)
  where
  fold (catom k) = evalCTC (extendEnv env (catom k)) atomCase
  fold (cnode a b) =
    let ra = fold a; rb = fold b
    in evalCTC (extendEnv (extendEnv (extendEnv (extendEnv env rb) ra) b) a) nodeCase
```

The node case binds 4 variables:
- cvz = left child (a)
- cvs cvz = right child (b)
- cvs (cvs cvz) = recursive result on left (fold a)
- cvs (cvs (cvs cvz)) = recursive result on right (fold b)

Then `ctCheckG = ctFold (ctVar cvz) atomCase nodeCase` where
atomCase = ctLit failCode and nodeCase does the 10-tag dispatch
using the recursive results.

### Step 3: Replace fPrf with defined predicate (~20 lines)

In the new FormulaBTA:

```agda
data FormulaBTAC : Set where
  fbotC  : FormulaBTAC
  fimpC  : FormulaBTAC -> FormulaBTAC -> FormulaBTAC
  fcAllC : FormulaBTAC -> FormulaBTAC
  fceqC  : CodeTermC -> CodeTermC -> FormulaBTAC  -- CodeTerm equality
```

NO `fPrf`. Instead, define:

```agda
fPrfC : CodeTermC -> CodeTermC -> FormulaBTAC
fPrfC p c = fceqC (ctApp ctCheckG p) c
```

where `ctApp ctCheckG p` substitutes p for the variable in ctCheckG.

### Step 4: Prove compositionality rules (~150 lines)

Each rule follows from ctCheckG's definition + ctCase computation.

For example, axChkMPct becomes:

```agda
axChkMPct-derived :
  ProofBTAC (fimpC (fPrfC p1 (ctNode (ctLit (catom n5)) (ctNode encA encB)))
                   (fimpC (fPrfC p2 encA)
                          (fPrfC (ctNode (ctLit n33c) (ctNode p1 p2)) encB)))
```

Proof sketch:
- fPrfC (ctNode n33c (ctNode p1 p2)) encB
  = fceqC (ctApp ctCheckG (ctNode n33c (ctNode p1 p2))) encB
- ctApp ctCheckG (ctNode n33c (ctNode p1 p2)) reduces by ctCase:
  - outer ctCase: node case (left=n33c, right=ctNode p1 p2)
  - tag dispatch: ctEqNat n33c n33c = true
  - result: ctMatchMP (ctApp ctCheckG p1) (ctApp ctCheckG p2)
- So fPrfC (ctNode n33c ...) encB = fceqC (ctMatchMP (checkResult p1) (checkResult p2)) encB
- The hypothesis fPrfC p1 enc(A→B) gives checkResult p1 = enc(A→B)
- The hypothesis fPrfC p2 enc(A) gives checkResult p2 = enc(A)
- ctMatchMP enc(A→B) enc(A) = enc(B) by computation

The proof uses CodeTerm computation laws (which are proved as
lemmas from evalCTC's definition) + transitivity/symmetry of fceqC.

### Step 5: Rebuild sdDerivedImp and goedel2 (~50 lines)

Copy the S/K derivation from BinaryTreeArith.agda, using the
derived compositionality rules instead of axioms.

## Key Lemmas Needed

### CodeTerm computation laws

```agda
ctCase-atom : evalCTC env (ctCase (ctLit (catom k)) ab nb) = evalCTC (extendEnv env (catom k)) ab
ctCase-node : evalCTC env (ctCase (ctLit (cnode a b)) ab nb) = evalCTC (extendEnv (extendEnv env b) a) nb
ctEqNat-refl : evalCTC env (ctEqNat (ctLit (catom k)) (ctLit (catom k))) = trueCode
ctFold-atom : evalCTC env (ctFold (ctLit (catom k)) ac nc) = evalCTC (extendEnv env (catom k)) ac
ctFold-node : evalCTC env (ctFold (ctLit (cnode a b)) ac nc) = ...with fold a and fold b...
```

### Proof system computation axioms

For each CodeTerm computation law, add a ProofBTAC axiom:
```agda
axCaseAtom : ProofBTAC (fceqC (ctCase (ctLit (catom k)) ab nb) (subst k in ab))
axCaseNode : ProofBTAC (fceqC (ctCase (ctNode a b) ab nb) (subst a b in nb))
axEqNatRefl : ProofBTAC (fceqC (ctEqNat t t) (ctLit trueCode))
```

These are DEFINITIONAL (they hold by computation of evalCTC).

### Congruence for fceqC

```agda
axCongLeft : ProofBTAC (fimpC (fceqC a b) (fceqC (ctLeft a) (ctLeft b)))
axCongNode : ProofBTAC (fimpC (fceqC a1 a2) (fimpC (fceqC b1 b2) (fceqC (ctNode a1 b1) (ctNode a2 b2))))
axTrans : ProofBTAC (fimpC (fceqC a b) (fimpC (fceqC b c) (fceqC a c)))
axSym : ProofBTAC (fimpC (fceqC a b) (fceqC b a))
```

## Risk Factors

1. **Agda type-checker performance**: deeply nested CodeTermC
   expressions may cause slow normalization. Mitigation: use
   `private` and `abstract`, break proofs into small lemmas.

2. **De Bruijn index management**: ctCase and ctFold bind variables.
   Substitution and lifting must handle these correctly. This is
   the most error-prone part.

3. **ctFold semantics**: the node case binds 4 variables (a, b,
   fold a, fold b). Managing 4 de Bruijn indices in the node
   branch is complex. Consider using named helpers instead of
   raw de Bruijn.

4. **checkG mutual recursion**: checkG calls evalG which calls
   checkG. ctFold does structural recursion on Code, but evalG
   uses fuel. For the specific tags in sdCode, evalG's behavior
   can be hardcoded (tag 36 calls evalG on specific CExps).
   But the general case may need a separate fuel parameter.

## Success Criterion

The file `BTAComputation.agda` compiles under `--without-K --exact-split`
with no postulates, no holes, and contains:

```agda
goedel2-comp : ProofBTAC ConBTAC -> EmptyG2
```

where ProofBTAC has NO checker-specific axioms — only:
- Hilbert S/K/mp/cgen/cinst
- CodeTerm computation laws (ctCase, ctEqNat, ctFold beta rules)
- CodeTerm congruence (fceqC transitivity, symmetry, congruence)
- Tree induction (axTreeInd)

The 7 compositionality rules are DERIVED as theorems.

## Estimated Effort

- Step 1 (CodeTerm extensions): 1 hour
- Step 2 (ctCheckG definition): 2-3 hours
- Step 3 (replace fPrf): 30 minutes
- Step 4 (prove compositionality): 2-3 hours
- Step 5 (rebuild goedel2): 30 minutes
- Buffer for type-checker issues: 2 hours

**Total: 6-10 hours.**

## File Dependencies

```
ChwistekSyntax.agda
ChwistekProvability.agda
ChwistekCodeLogic.agda
ChwistekCodeQuant.agda
ChwistekGodelSentence.agda
ChwistekSoundness.agda
ChwistekGodel2Genuine.agda  (for checkG, n36g-n39g, etc.)
SelfDestruct.agda            (for sdCode, encCSubPhi)
    |
    v
BTAComputation.agda          (the new file)
```
