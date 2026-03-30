# Next Session: Toward Godel II

## What was done (2026-03-30)

### thS-sound (ThInt.agda)
- Defined `IsReflCode : Tree -> Set` — every thS output is `nd (codeReify a) (codeReify a)`
- Proved `thS-sound : (y : Tree) -> IsReflCode (thS y)` by structural induction
- Helper lemmas: `swapRefl`, `transRefl` (using `eqTree-sound` for transitivity)

### Godel I (Godel.agda)
- `notInRange`: general range exclusion — if target is not a reflexivity code, it's not in thS's range
- `godelI-casLeaf`: weak Godel I — cas-leaf equation is true but unprovable (tag mismatch)
- `godelSentence-lf-false`: the Godel sentence for target=lf evaluates to falseT
- `godelI`: diagonal Godel I — the Godel equation (using godelSentence) is true but unprovable

### Key insight from Godel II discussion
The full Guard D_f machinery (Theorem 12) is overkill. For Godel II, we only need D_f
for ~3 specific functions (thS, conjugation, composition helpers), not for ALL primitive
recursive functions. The "quoteProofTree" idea has the right direction but understates
the required machinery — D2 (internal modus ponens on provability) needs its own transformer.

## What to do next

### Priority 1: Extend thS with computation axioms

The current thS only has refl + sym + trans, making IsReflCode trivially true (every
theorem has both sides equal). For a meaningful Godel II, thS needs to prove non-trivial
equations. Add to thS:

1. **cas-leaf**: `cas leaf u v = u`
2. **cas-pair**: `cas (pair a b) u v = v[a,b]` (with substitution)
3. **rec-leaf**: `rec leaf z s = z`
4. **rec-pair**: `rec (pair a b) z s = s[a, b, rec a z s, rec b z s]`

Each requires:
- A new branch in thS (metalevel)
- A new branch in thStep5Full (internal term)
- Extending thGenFull correctness proof
- Extending soundness (which will no longer be IsReflCode — need TrueEqCode instead)

### Priority 2: Soundness for extended thS

With computation axioms, thS outputs are no longer reflexivity codes. Need a general
soundness predicate:

```agda
TrueEqCode : Tree -> Set
TrueEqCode lf = Unit
TrueEqCode (nd l r) = Eq (eval (decodeTm0 l)) (eval (decodeTm0 r))
```

This requires the decode round-trip lemma:
```agda
decodeTerm 0 (codeTerm t) = just t
```
(at least for the terms that thS can produce).

### Priority 3: D_thS — the proof-quoting operator

The key operator for Godel II. Given proof tree p, construct q such that:
```
thS(q) = nd (codeReify (thS p)) (codeReify (thS p))
```
i.e., q proves the reflexivity equation `thS(p) = thS(p)`.

This is trivial for the reflexivity branch of thS (just use nd lf p as the proof tree).
But the HARD part is the internal version: a Term that computes q from p, with
a correctness proof.

### Priority 4: Godel II statement and proof

Rose's Godel II (Theorem 13): `th(y) != e(th(z))` is valid but unprovable.

In our setting: the conjugate function `e` swaps an equation code:
`e(nd L R) = nd R L`. The consistency statement is:
"for all y, z: thS(y) != swap(thS(z))"
which says no theorem contradicts another theorem.

The argument:
1. If Con is provable, then from any proof p of A, we can build a proof that
   "A is consistent with the system" (using D_thS + the Con proof)
2. In particular, for the Godel sentence G, this gives a proof of G
3. But G is unprovable (Godel I)
4. Contradiction

## Files to modify

- **ThInt.agda**: extend thS with computation axioms, update soundness
- **Godel.agda**: Godel II statement and proof
- **Possibly new**: Rose/GodelII.agda if the file gets too large

## Key references

- Rose pp.130-135: Theorems 10-13 (soundness, consistency, Godel II)
- Guard pp.15-17: Theorems 11-14 (Godel I, D_f, Godel II)
- The D_thS approach: only internalize thS (not all functions)

## Architecture decision

Stay in the **purely equational setting** (no Imp/Prov formula types).
Express consistency as Rose does: `th(y) != e(th(z))`.
This avoids adding formula types and keeps compatibility with the existing infrastructure.
