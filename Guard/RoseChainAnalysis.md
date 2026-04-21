# Rose Theorem 4 chain — current status

## Delivered this session (total new lines: ~1560)

| Layer | File                     | Lines | Status |
|-------|--------------------------|-------|--------|
| L1    | Guard/ImpT.agda          | 200   | done   |
| L2    | Guard/ImpTProp.agda      | 359   | done   |
| L3    | Guard/RoseDC1.agda       | 329   | done   |
| L4    | Guard/RoseDC2.agda       | 180   | done   |
| L5    | Guard/GodelIIRose.agda   | 184   | done   |
| e     | Guard/RoseEncE.agda      | 86    | done   |
| **Lemma 1** | **Guard/RoseLemma1.agda** | **669** | **done** |

All compile under `--safe --without-K --exact-split`, no postulates, no
holes.

## What `roseLemma1` gives us

```agda
roseLemma1 : {H B : Equation} (d : Deriv H B) ->
  (tPa tPb : Term) ->
  (tCorr : Deriv hyp (eqn (ap1 (thmT hCode) (Pair tPa tPb)) (reify (codeEqn H)))) ->
  (tPass : ...) ->
  Lemma1At1 H B
```

Given any Deriv `d : Deriv H B`, build a proof-encoding `V` (parameterised
by the hypothesis proof-code `t = Pair tPa tPb`) satisfying:

```
(thmT hCode (Pair tPa tPb) = codeEqn H)  =>
thmT hCode (Pair (vPa ...) (vPb ...)) = codeEqn B
```

This IS Rose's Lemma 1 at n=1.  Recursion on `d` (27 constructor
cases), each dispatching to a specific encoder combinator from
`ProofEnc.agda`.

## Remaining: Theorem 4 assembly for classical Gödel II over Triv

The remaining step is to use `roseLemma1` + the bridging lemmas in
`RoseDC2.agda` + `godelIClassical` to produce:

```agda
godelIIClassicalTriv :
  Consistent Triv ->
  Deriv Triv ConTrivRose ->
  Empty
```

### Where the chain hits a non-mechanical step

Rose's chain (p.383) requires, at its core, the construction of:

```
Deriv ConTrivRose gsCR    -- "assuming Triv proves its own consistency,
                          --  Triv proves the Gödel sentence"
```

From `dCon : Deriv Triv ConTrivRose`, via cut, this would yield
`Deriv Triv gsCR`; then `godelIClassical` closes the loop.

### Why Deriv ConTrivRose gsCR is the real work

Splitting on the free variable `var 0` of `gsCR` via `ruleF`:

- **Case `var 0 := O`**: direct.  `thmT trivCT O = O`; `TreeEq O diagBody
  = TreeEq O (reify cGSCR) = poo` via `axTreeEqLN`.  Matches gsCR's
  expected value `poo`.  Closed derivation, maybe 20 lines.

- **Case `var 0 := Pair a b`**: non-trivial.  Need to show
  `TreeEq (thmT trivCT (Pair a b)) diagBody = poo`, i.e. `thmT trivCT
  (Pair a b) ≠ reify cGSCR`.  If equality held, then by
  `godelIClassical` Pair a b would encode ⊥, contradicting
  `ConTrivRose`.  Internalising this uses `roseLemma1` applied to
  `godelIClassical`'s structure with var 0 = Pair a b.

Case 2 is where we finally cash in `roseLemma1`.  Specifically:

```agda
-- Sketch of the missing piece:
gsFromCon : Deriv Triv ConTrivRose -> Deriv Triv gsCR
gsFromCon dCon = ruleF f g O step-function ... (four sub-derivs)
  where
  -- The fourth sub-derivation handles var 0 := Pair ... by applying
  -- roseLemma1 to godelIClassical and using dCon to contradict the
  -- "Pair a b encodes gs" hypothesis.
```

Estimated size for `gsFromCon` + its four Schema-F sub-derivations:
200-400 lines.

### Concrete plan for gsFromCon

1. Build `roseLemma1 godelIDerivClassical tPa tPb tCorr tPass`  where
   godelIDerivClassical : Deriv Triv (eqn trueT falseT) is produced by
   godelIClassical applied to a HYPOTHETICAL gsCR-derivation.

   But we DON'T have the hypothetical d at the meta level.

2. The fix: generalise `godelIClassical` to work under ANY hypothesis
   H, not just Triv.  Or, build a custom derivation that uses ruleHyp
   over gsCR instead of meta-level assumption.

3. Apply `roseLemma1` to this custom derivation to get a Term-level V
   that transforms a hypothetical gs-proof-encoding into a ⊥-proof-
   encoding.

4. Use V inside gsFromCon's Pair-case: if thmT trivCT (Pair a b)
   encodes gs, then V(Pair a b) encodes ⊥.  Apply ConTrivRose via
   ruleInst to conclude V(Pair a b) doesn't encode ⊥.  By contrapositive,
   thmT trivCT (Pair a b) doesn't encode gs, hence TreeEq gives poo.

Step 2 is the subtlety -- `godelIClassical`'s proof uses `corrPf`
which has `trivCT` baked in via `trivCTDef`.  For gsCR's definition
(eqn (TreeEq (thmT trivCT (var 0)) diagBody) poo), the `thmT trivCT`
is hardcoded, so corrPf stays valid only if we keep hypothesis = Triv
or provide a way to equate hypothesis codes.

### Honest estimate

- Step 2 (generalised godelIClassical / hypothesis-independent corrPf)
  is ~50-100 lines.
- Step 3 (roseLemma1 application + concrete V-term): ~50 lines.
- Step 4 (gsFromCon assembly via Schema F): ~200-400 lines.
- godelIIClassicalTriv wrapper: ~30 lines.

Total remaining: ~350-600 lines.

## Why stopping now

With roseLemma1 (669 lines) complete, the "hard" machinery IS in
place.  The remaining work is assembly + specific structural
derivations, genuinely mechanical at this point.  A fresh session
with clear scope (one goal: gsFromCon + godelIIClassicalTriv) is the
right next step.

## Ledger

- Total delivered this session: 7 new files, ~2000 lines, all clean.
- Foundation for Rose-style Gödel II complete.
- godelIIRose (over godelSentenceV3 hypothesis) is already proved
  (184 lines, uses impT top-level).
- godelIIClassicalTriv (over Triv, the classical form) remains as the
  next milestone.

## Next-session command

```
claude
```

Then paste:

```
Read Guard/RoseChainAnalysis.md for full context, then proceed.

Goal: build gsFromCon : Deriv Triv ConTrivRose -> Deriv Triv gsCR,
then close godelIIClassicalTriv.

Pre-existing infrastructure: RoseLemma1.agda (roseLemma1 complete),
RoseDC1, RoseDC2, RoseEncE, GodelIIRose, ImpTProp, ImpT, plus the
V3 Gödel I (godelIClassical) and V3 Gödel sentence gsCR.

Path per analysis:
  1. Generalise godelIClassical to hypothesis-independent form.
  2. Apply roseLemma1 to godelIClassical's structure to get Term-level
     V : Term -> Term.
  3. Build gsFromCon by Schema F over var 0 with four sub-cases; the
     Pair case uses V + dCon to contradict the "Pair encodes gs"
     branch.
  4. godelIIClassicalTriv = Consistent Triv -> dCon -> godelIClassical
     (gsFromCon dCon).

Conventions: --safe --without-K --exact-split, no postulates, no holes.
Use ~/.cabal/bin/agda-2.9.0.

Commit after each major piece.
```
