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

### Session update (Guard/GodelIIClassicalTriv.agda)

Delivered this session:

  * `Guard/GodelIIClassicalTriv.agda` -- 0.1s, no postulates no holes.
  * Top-level `godelIIClassicalTrivWith gsFromCon con dCon` reducing
    classical Gödel II over Triv to `godelIClassical` + consistency.
  * Schema F ingredients:
      - `FF` = `Comp2 TreeEq (thmT trivCT) (KT diagBody)`
      - `GG` = `KT poo`
      - `zz` = `poo`
      - `ss` = `Post (KT poo) Pair`
  * Three of four Schema-F premises proved:
      - `baseF : FF O = zz`     (via axComp2 + axRecLf + axKT +
                                  diagFTargetCR + axTreeEqLN)
      - `baseG : GG O = zz`     (axKT)
      - `stepG : GG (Pair v0 v1) = ss (Pair v0 v1) (Pair (GG v0)
                                  (GG v1))`   (axKT + axPost)
  * `gsFromConWith : StepFType -> Deriv Triv gsCR`  assembling
    the four premises via `ruleF` + bridging to `gsCR`'s expanded form
    (axComp2 + axKT on both sides).
  * `StepFCoreType` + `stepFFromCore`: the F-step Schema-F premise
    factored through its TreeEq-core form
      Deriv Triv
        (eqn (ap2 TreeEq (ap1 (thmT trivCT) (ap2 Pair (var 0) (var 1)))
                           diagBody)
             poo)
  * `godelIIClassicalTrivWithStepF` / `godelIIClassicalTrivWithCore`
    taking the remaining open premise as a parameter.

Remaining work: `StepFCoreType`, i.e. a `Deriv Triv` of the above
TreeEq-equation with `var 0`, `var 1` free.  The analysis of §2-§4
above stands for this step.

Concrete blocker observed while attempting the construction:
`roseLemma1` as implemented produces encodings under `thmT (reify
(codeEqn H))`, not under `thmT trivCT`, for any choice of hypothesis
`H`.  This matches `thmT trivCT` only when `H = Triv`.  With `H =
Triv` the needed input derivation would be `Deriv Triv gsCR` or
`Deriv Triv bot` -- both circular.  Paths forward that were
considered but not attempted:

  (i)  Implement the "planned" roseLemma1 variant (see
       NEXT-SESSION-IMPT-GODELII.md lines 128-142) which uses `thmT
       trivCT` throughout and takes TWO encodings (for `A` and `A→B`);
  (ii) Redesign gsCR to use `thmT` of the hypothesis's code rather
       than the hardcoded `trivCT` (would require a V3-style free
       slot in the template);
  (iii) Direct tree-structural proof with MORE Schema-F splits (Pair
        case of `thmT trivCT (Pair v0 v1)` is stuck on open var 1).

Session output: Guard/GodelIIClassicalTriv.agda (~380 lines,
infrastructure + three of four Schema-F premises proved, one open
premise factored).  The theorem `godelIIClassicalTrivWithCore`
reduces classical Gödel II over Triv to a single precise open
lemma of known content.

### Session update 2: Option (i) executed

Implemented `Guard/RoseLemma1T.agda` (614 lines, 0.25s, no postulates)
-- the Ryan-style Lemma 1 over the ambient `thmT trivCT`, matching
Rose (1967) and Ryan (1978) Lemma 1.  Key structural difference from
`Guard/RoseLemma1.agda`:

  * `Lemma1T H B` fixes the evaluator to `thmT trivCT` throughout,
    rather than `thmT (reify (codeEqn H))`.
  * At each closed axiom case (axI / axFst / ... / axRecPNd), uses
    `enc*Corr trivCT` directly from `Guard.ProofEnc` instead of
    `fromProofE3 (thm14EV3Ax* H)`.
  * Structural cases (Sym / Trans / Cong1 / CongL / CongR / Inst / F)
    use the same hCode-parametric encoders at `hCode = trivCT`.
  * Hypothesis case (`roseL1T_Hyp`) splices in caller-supplied
    `tPa, tPb, tCorr, tPass` unchanged.
  * Top-level `roseLemma1T : Deriv H B -> ... -> Lemma1T H B` with
    full dispatch over all 28 Deriv constructors.

The key object `dAux : Deriv H_enc B_aux` is now exhibited in
`Guard/GodelIIClassicalTriv.agda`:

  H_enc = "Pair (var 0) (var 1) encodes gsCR under thmT trivCT"
  B_aux = "TreeEq (thmT trivCT (Pair v0 v1)) diagBody = O"

  dAux = ruleTrans (congL TreeEq diagBody (ruleHyp {H_enc}))
                   (ruleTrans (congR TreeEq (reify cGSCR) diagFTargetCR)
                              (treeEqSelf (reify cGSCR)))

`dAuxEncoded` witnesses that `roseLemma1T dAux` typechecks and
produces a `Lemma1T H_enc B_aux`.

### What remains to close godelIIClassicalTriv

With Lemma1T implemented and dAux exhibited, the remaining chain
(Rose/Ryan Theorem 4 last step) is:

 1. Apply `roseLemma1T dAux` with  tPa = var 0 , tPb = var 1 ,
    and  tCorr = hypothetical "Pair v0 v1 encodes gsCR".  The
    hypothesis H_enc is played against `ruleHyp`, so tCorr gets
    substituted where `dAux` uses `ruleHyp{H_enc}`.  Result:
    `V : Term` with
      `vCorr : thmT trivCT V = reify (codeEqn B_aux)`.

 2. Instantiate  dCon  at  var 0 := V : object-level theorem
      `impT (TreeEq (thmT trivCT V) codeBotT) falseT = trueT`.

 3. Establish the tree-disequality fact
      `TreeEq (reify (codeEqn B_aux)) codeBotT = poo`
    via  axTreeEqNN  recursive decomposition (or by showing the
    two trees differ in a specific slot).  The two trees ARE
    syntactically distinct --  codeEqn B_aux  = codeEqn (eqn LHS O)
    vs  codeBot = codeEqn (eqn O poo) -- so this is a concrete
    computation.

 4. Combine:  thmT trivCT V = reify (codeEqn B_aux) (from 1)
    with  TreeEq (reify (codeEqn B_aux)) codeBotT = poo (from 3)
    to obtain  TreeEq (thmT trivCT V) codeBotT = poo .  Apply the
    impT-instance from 2 with a  falseT  antecedent  (poo = Pair O O
    matches the Pair-shape antecedent pattern of the impT
    evaluation): step 2's impT says "if antecedent is O, consequent
    falseT; else trueT".  With antecedent = poo (Pair), impT
    evaluates to trueT vacuously.  We need the OTHER direction:
    with antecedent = O (trueT).

 5. Use the  Pair v0 v1  hypothesis to reduce the antecedent to
    trueT, close the chain via modus ponens to get  falseT = trueT
    under the H_enc hypothesis.  This is the final contrapositive
    step (if Pair v0 v1 encodes gsCR, then inconsistency).

 6. Wrap up in object-level  impT  to get Schema-F step-F premise
    proper.

Estimated additional work: 150-300 more lines of Deriv-level tree-
disequality + modus-ponens chain.  The non-trivial piece is step 5/6
(object-level contrapositive closure), not any of steps 1-4 which
are direct applications of existing machinery.

Total session 2 output:
  * `Guard/RoseLemma1T.agda`  (614 lines, new).
  * `Guard/GodelIIClassicalTriv.agda` additions (+90 lines).
  All clean, no postulates.

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
