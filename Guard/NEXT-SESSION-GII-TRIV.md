# Next Session: close godelIIClassicalTriv via e-encoder

## Command

From `/Users/coquand/CHWISTEK`:

```
claude
```

Then paste:

```
Read Guard/NEXT-SESSION-GII-TRIV.md for full context, then proceed.

Goal: close  godelIIClassicalTriv : Consistent Triv ->
                                    Deriv Triv ConTrivRose ->
                                    Empty
by completing the Rose/Ryan Theorem 4 modus-ponens chain started in
Guard/GodelIIClassicalTriv.agda.

Infrastructure already delivered and committed:
  * Guard/RoseLemma1T.agda             Ryan-style Lemma 1 over thmT trivCT.
  * Guard/GodelIIClassicalTriv.agda    Schema F reduction with 3 of 4
                                        premises proved; dAux exhibited;
                                        dAuxEncoded typechecks.
  * Guard/ImpT.agda  +  Guard/ImpTProp.agda   object-level impT toolkit.
  * Guard/RoseEncE.agda                e-Tree / e-Term encoder skeleton.

Conventions: --safe --without-K --exact-split, no postulates, no holes.
Use ~/.cabal/bin/agda-2.9.0 (NOT /opt/homebrew/bin/agda).
Commit after each major piece.

Proceed autonomously.
```

## What's done (committed on main)

Seven commits as of 2026-04-21:

```
26b7a92  [doc] RoseChainAnalysis: option (i) executed, remaining chain laid out
21da0a1  [gii-triv] Integrate RoseLemma1T and exhibit constructible dAux
7ff35eb  [rose-l1t] RoseLemma1T: Ryan-style Lemma 1 over thmT trivCT
08a8b3a  [doc] RoseChainAnalysis: session update on Guard/GodelIIClassicalTriv
c8dc3ad  [gii-triv] Factor step-F premise through TreeEq-core form
f39c293  [gii-triv] GodelIIClassicalTriv: infrastructure for Schema F approach
0d5bfd6  [doc] RoseChainAnalysis: roseLemma1 done, gsFromCon identified as remaining bottleneck
```

Key artifacts:

**`Guard/RoseLemma1T.agda`** (614 lines, 0.25s, no postulates):
  * `Lemma1T H B` record: `vCorr` under `thmT trivCT` (Ryan-style).
  * `roseL1T_Hyp`: splices caller-supplied `tPa, tPb, tCorr, tPass`.
  * 22 closed-axiom cases (`roseL1T_AxI` … `roseL1T_AxRecPNd`).
  * 7 structural-rule wrappers (Sym / Trans / Cong1 / CongL / CongR
    / Inst / F).
  * Top-level  `roseLemma1T : Deriv H B -> tPa tPb -> tCorr ->
    tPass -> Lemma1T H B`  with dispatch over all 28 Deriv cases.

**`Guard/GodelIIClassicalTriv.agda`** (474 lines):
  * `ConTrivRose` (impT-form Triv-consistency).
  * Schema F ingredients `FF, GG, zz, ss` (FF = `Comp2 TreeEq (thmT
    trivCT) (KT diagBody)`, GG = `KT poo`).
  * `baseF` / `baseG` / `stepG` proved.
  * `gsFromConWith : StepFType -> Deriv Triv gsCR` assembles via
    `ruleF` + bridging.
  * `StepFCoreType` factoring through the TreeEq-core form.
  * `godelIIClassicalTrivWithStepF` / `godelIIClassicalTrivWithCore`
    close the theorem modulo the open premise.
  * `dAux : Deriv H_enc B_aux` where
    - `H_enc = eqn (ap1 (thmT trivCT) (Pair (var 0) (var 1)))
                   (reify cGSCR)`
    - `B_aux = eqn (ap2 TreeEq (ap1 (thmT trivCT) (Pair v0 v1))
                               diagBody)
                   O`
    Built from `ruleHyp{H_enc}` + `congL` + `congR` +
    `diagFTargetCR` + `treeEqSelf`.
  * `dAuxEncoded = roseLemma1T dAux`  -- sanity-checks that the
    Lemma-1 application typechecks.

## What's blocking

`dAuxEncoded` produces `V` with `thmT trivCT V = reify (codeEqn
B_aux)`, but **codeEqn B_aux ≠ codeBotT** (different tree shapes).
So instantiating `dCon` at `V`:

  `dCon [v_0 := V] : impT (TreeEq (thmT trivCT V) codeBotT) falseT
                      = trueT`

doesn't fire -- the antecedent evaluates to `poo` (via tree-
disequality between `codeEqn B_aux` and `codeBotT`), and
`impT poo falseT = trueT` is vacuous.

**To actually derive bot from  dCon , we need a  V  with
`thmT trivCT V = codeBotT`**, not  `= codeEqn B_aux`.  This requires
composing with an `e`-encoder (Rose's function sending code of
`A = B` to code of `A ≠ B`, where "≠" uses the `TreeEq`/`impT`
structure).

## Concrete plan -- pick up here

### Step A: prove `e`-correctness under `thmT trivCT`

**File**: probably new `Guard/RoseEncECorr.agda` (or extend
`Guard/RoseEncE.agda`).

**Goal**: given an encoding `encV : Term` of an equation `eqn A B`
under `thmT trivCT` (i.e., `thmT trivCT encV = reify (codeEqn (eqn
A B))`), build `encENeq : Term` such that:

  `thmT trivCT encENeq = reify (codeEqn (eqn (ap2 TreeEq A B)
                                             falseT))`

I.e., "encENeq encodes the equation 'TreeEq A B = falseT' under
`thmT trivCT`".

Construction: Rose/Ryan build `encENeq` as a *term-level* combinator
applied to `encV`.  Specifically, use the existing axiom-encoders
(`encAxTreeEq*`, `encCongL`, `encCongR`, etc.) to assemble the
encoding of the longer equation from the encoding of the shorter.

Alternative route: build a specific small Deriv `dE : Deriv (eqn A
B) (eqn (ap2 TreeEq A B) falseT)` and use `roseLemma1T dE` to get
the e-encoder as V directly.  `dE` itself uses only `congL TreeEq B
(ruleHyp ...)` + `treeEqSelf`-style reasoning with `axTreeEqNN`.
Probably cleaner than hand-building the encoding term.

Estimated: 50-100 lines.

### Step B: compose e with dAux's V to land on codeBotT

We want final `V'` with `thmT trivCT V' = codeBotT =
reify (codeEqn (eqn trueT falseT))`.

Chain:
  * `dAux` gives V encoding B_aux = "TreeEq ... = O".
  * Apply `e`-encoder: V' encoding "TreeEq (TreeEq ...) O = falseT".
  * Hmm -- this doesn't directly give codeBot either.

Actually re-examine: `codeBot = codeEqn (eqn trueT falseT) = codeEqn
(eqn O poo)`.  We need a V whose `thmT trivCT`-image is
`reify (codeEqn (eqn O poo))`.

Cleaner plan: build `dBot : Deriv H_enc (eqn trueT falseT)`
directly, then `roseLemma1T dBot` gives V with the right image.

For  `dBot`  we need to derive `trueT = falseT` from H_enc (= "Pair
v0 v1 encodes gsCR").  The chain inside Deriv:

  1. `ruleHyp {H_enc}` :  thmT trivCT (Pair v0 v1) = reify cGSCR.
  2. Instantiate `gsCR` at var_0 := Pair v0 v1 -- but we DON'T have
     `Deriv H_enc gsCR`.

So `dBot : Deriv H_enc bot` is NOT directly constructible either,
by the same Deriv-single-hypothesis obstacle.

### Step C: reformulate the chain

This is where the design work is.  Options:

**Option α**: Use H = gsCR (not H_enc) and rely on Lemma 1 to
splice tCorr at ruleHyp{gsCR}, with tCorr asserting "Pair v0 v1
encodes gsCR".  But ruleHyp{gsCR} has conclusion `gsCR` (= "TreeEq
... = poo"), not "... encodes gsCR".  The caller-supplied tCorr
would need to be different from what Lemma 1 is designed to splice.

**Option β**: Redesign Lemma 1 to take TWO hypotheses (Rose's n=2
case in NEXT-SESSION-IMPT-GODELII.md:128-142), or use  Prov3  style
combined encoding.

**Option γ**: Use H_enc and derive, under H_enc, a particular
`Deriv H_enc (eqn (ap2 TreeEq X codeBotT) O)` directly, bypassing
`gsCR`.  The idea: since H_enc says "thmT trivCT V' = reify cGSCR"
(where V' is specific), instantiate dCon at V' and get
`impT (TreeEq (reify cGSCR) codeBotT) falseT = trueT`.  The
antecedent `TreeEq (reify cGSCR) codeBotT` structurally reduces
(both are closed reified trees) to either O or poo.  If = poo,
impT is vacuous.  If = O, means reify cGSCR = codeBotT -- check
whether they're Agda-decidably distinct trees.

Actually:  cGSCR = codeEqn gsCR  vs  codeBot = codeEqn (eqn O poo).
These are distinct.  So `TreeEq (reify cGSCR) codeBotT = poo`
derivably.  Hence `impT poo falseT = trueT` vacuously.  dCon at
V' = Pair v0 v1 gives trueT identity, no useful info.

So Option γ doesn't close either.

### Step D: re-read Rose's proof precisely

Before writing more Agda, **carefully re-read Rose (1967) Thm 4
and Ryan (1978) Main Theorem** to trace EXACTLY what encoding `V`
he constructs and how it lands on `codeBot` (or the equivalent
"negation" in his setting).

Key question: does Rose apply `e` to the WHOLE chain's output, or
does he construct a different derivation whose natural encoding
already yields the negation?

My best guess: Rose's chain uses `e(th(V(x)))` where `V(x)` encodes
"gsCR = 0" (i.e., the Gödel sentence has characteristic 0 at x),
so `e(th(V(x)))` encodes the negation, which contradicts the
Gödel sentence's assertion that "gsCR != th(z)".  So `e` is
applied ONCE at the end, converting an "= O" encoding to a "!=
O" encoding.

If that's right, Step A (e-correctness under thmT trivCT) is
the right tool, and Step B chains:
  V from dAux = encodes "TreeEq ... = O"
  e(V) = encodes "TreeEq (TreeEq ...) O = falseT"
Neither is codeBot directly.

Hmm.  Probably Rose's consistency statement is subtly different
from ours (ConTrivRose uses codeBot; Rose uses a parametric
"encoded negation").  **Action: examine Rose's consistency
statement and ε(th(x)) in the paper, and align our ConTrivRose
formulation.**

Estimated: 200-400 lines after the design is settled (Step D).

## Files to touch (in order)

1. **Read** Rose1.pdf §3-4 and Ryan.pdf §2 (especially Main
   Theorem proof, which Ryan says "parallels Rose").  Write down
   what specific encoding lands on codeBot/eCode.
2. **Design memo**: write  Guard/ROSE-CHAIN-DESIGN.md  (~100 lines)
   laying out the exact shape of V and where `e` fits in.  This
   is the missing piece of analysis.
3. **`Guard/RoseEncECorr.agda`**: e-correctness under `thmT trivCT`
   (Step A).  Either via direct term construction or by building
   a small Deriv and roseLemma1T-encoding it.
4. **`Guard/GodelIIClassicalTriv.agda`**: extend with the Rose
   chain -- assemble `dBot` (or equivalent), encode, instantiate
   `dCon`, close via  impT  modus ponens.

## Sanity commands

```
time ~/.cabal/bin/agda-2.9.0 Guard/RoseLemma1T.agda
  # 0.25s, no output
time ~/.cabal/bin/agda-2.9.0 Guard/GodelIIClassicalTriv.agda
  # 0.15s, no output
```

## Design-decision budget

Before writing more Agda, spend ~30 min on paper re-reading Rose
and drafting ROSE-CHAIN-DESIGN.md.  The Agda is mechanical once
the shape of V is clear.  Rushing straight to Agda without the
design step is exactly how we ended up with the hCode mismatch
in the first place.
