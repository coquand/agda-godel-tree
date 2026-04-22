# Next session: continue Option G (BRA migration)

## Committed state (this session ends: 2026-04-22)

**Update after continuation of 2026-04-22 session:**

Committed in continuation (past what's listed below):

  * encAxS (tag n31) + encAxSCorr + encAxSPass
  * encAxNeg (tag n32) + encAxNegCorr + encAxNegPass

Both are mechanical variants of encAxK.  Guard/ProofEncFormula.agda
now 477 lines with 3 of 4 formula-level encoders delivered.

Remaining: encMp (the delicate one).  Proof plan detailed at the
end of this file.

---

## Prior committed state

- `Guard/BRA-DESIGN.md` — architecture doc for Option G.
- `Guard/BRA.agda` — single-layer BRA data type with `fromDeriv`,
  `ruleHypB`, `axK/axS/axNeg`, `axEqTrans/axEqCong1/L/R`, `mp`, and
  `ruleSub` (with `Eq (substF x t hyp) hyp` side condition). 189 lines,
  typechecks clean.
- `Guard/Formula.agda` — extended with `codeFormula`, `tagImp`, `tagNeg`.
- `Guard/ThFunTForV3.agda` — extended with `case30` (encAxK), `case31`
  (encAxS), `case32` (encAxNeg), `case33` (encMp). Dispatch chain
  extended: `ndT30V3..ndT33V3`, new bottom `ndT34V3 = sndArg2`. Helpers
  `mkImpF`, `mkNegF`, `tagImpT`, `tagNegT`.
- `Guard/ThFunTForV3Pass.agda` — miss chains extended through tags
  n30..n33.
- `Guard/ProofEncFormula.agda` — first formula-level encoder:
  `encAxK + encAxKCorr + encAxKPass`. 192 lines. Template for the
  remaining 3.
- `Guard/RoseLemma1T.agda` + `Guard/GodelIIClassicalTriv.agda` +
  `Guard/GodelIIClassicalTrivStrong.agda` — unretired earlier this
  session; they typecheck under Option A but are now **not needed**
  for Option G (Rose Lemma 1 is bypassed).

## Remaining work (ordered, ~800-1000 lines)

### Step 5 continued: add 3 more encoders to ProofEncFormula.agda

Template = `encAxK`. Each follows the exact same structure:

```
<encoder-def>        -- Term combinator, natCode-tagged
<encoder-Corr>       -- recNdRed + guardNdV3 + 30-step ndBranchMiss
                     -- + ndBranchHit + case-specific reduction
<encoder-Pass>       -- passthroughSucV3 with appropriate Tree dat
```

**encAxS** (tag n31): 3-arg (pC, qC, rC); body = `Pair pC (Pair qC rC)`.
Case31's reduction uses `origB1`, `origB2` for qC, rC access.
Expected output shape: encoded `(P ⊃ Q ⊃ R) ⊃ ((P ⊃ Q) ⊃ (P ⊃ R))`.
Reduction chain: ~20 lines of `mkImpF`/`fanRed`/`origARed`/`origBRed`
nesting (it's more nested than encAxK's output). ~90 lines total.

**encAxNeg** (tag n32): 2-arg (pC, qC); body = `Pair pC qC`.
Case32 uses `mkNegF origA`, `mkNegF origB`, `mkImpF origB origA`.
Expected output: encoded `~P ⊃ (~Q ⊃ (Q ⊃ P))`.
Reduction: ~15 lines. Total ~85 lines.

**encMp** (tag n33): 2-arg sub-encodings; body = `Pair sub1 sub2`.
Case33 is the delicate one — it doesn't just reduce to a closed
form; the `branch check1mp (branch check2mp rbSndSnd (kF2 O)) (kF2 O)`
structure means the output depends on whether sub2's validator has
imp-shape AND antecedent matches sub1's validator.

### encMp detailed plan

Signature (using Formula parameters for clean treeEqSelfReify use):

```agda
encMpCorr :
  (hCode sub1 sub2 : Term) (P Q : Formula) {hyp : Equation} ->
  -- dispMiss1: sub1's outer form misses all dispatch tags in the inner
  -- thmT call `thmT (Pair sub1 sub2)`.  In practice, satisfied via
  -- passthroughSucV3 when sub1 is an existing encoder output.
  ((x rcs : Term) {h : Equation} ->
    Deriv h (eqn (ap2 (ndDispatchV3 hCode) (ap2 Pair sub1 x) rcs)
                 (ap2 sndArg2 (ap2 Pair sub1 x) rcs))) ->
  ({h : Equation} -> Deriv h (eqn (ap1 (thmT hCode) sub1)
                                  (reify (codeFormula P)))) ->
  ({h : Equation} -> Deriv h (eqn (ap1 (thmT hCode) sub2)
                                  (reify (codeFormula (P imp Q))))) ->
  Deriv hyp (eqn (ap1 (thmT hCode) (encMp sub1 sub2))
                 (reify (codeFormula Q)))
```

Proof structure (~180 lines):

1. **Outer dispatch to case33** (~35 lines):
   recNdRed + guardNdV3 + 33 ndBranchMiss + ndBranchHit for n33.
   Arrives at `ap2 case33 enc recs`.

2. **Compute recsB = thmT sub2** (~15 lines):
   Use `intermediateGenericV3 hCode sub1 body' <anything> <anything> dispMiss1`
   to get `thmT (Pair sub1 sub2) = Pair (thmT sub1) (thmT sub2)`.
   Then `recsB = Snd(Snd(recs)) = thmT sub2` via axSnd + axPost
   unfoldings.

3. **Apply sub2Corr** to rewrite `thmT sub2` to
   `reify (codeFormula (P imp Q))`
   = `Pair tagImpT (Pair (reify (codeFormula P)) (reify (codeFormula Q)))`.

4. **Reduce check1mp enc recs to O** (~15 lines):
   check1mp unfolds to `TreeEq rbFst tagImpT`. rbFst = Fst recsB =
   Fst (Pair tagImpT ...) = tagImpT (via axFst). Then
   `TreeEq tagImpT tagImpT = O` via `treeEqSelfReify tagImp`.

5. **Apply branchHit for outer branch** (1 line):
   Reduces to `branch check2mp rbSndSnd (kF2 O) enc recs`.

6. **Reduce check2mp enc recs to O** (~20 lines):
   check2mp = `TreeEq rbSndFst recsA`. Compute:
   - rbSndFst = Fst(Snd(recsB)) = Fst(Pair codeP codeQ) = codeP.
   - recsA = Fst(Snd(recs)) = thmT sub1 = codeP (via sub1Corr).
   - Then `TreeEq codeP codeP = O` via `treeEqSelfReify (codeFormula P)`.

7. **Apply branchHit for inner branch** (1 line):
   Reduces to `rbSndSnd enc recs`.

8. **Reduce rbSndSnd enc recs to codeQ** (~15 lines):
   rbSndSnd = Snd(Snd(recsB)) = Snd(Pair codeP codeQ) = codeQ.

### encMpPass

Standard `passthroughSucV3 hCode n32 (nd sub1-tree sub2-tree)`, where
sub1-tree and sub2-tree are the TREE forms (given by the caller).
Signature parameterized over sub1, sub2 trees (since encMp's sub-
encodings can be arbitrary Term constructions, not just `reify
(codeFormula P)`, we parameterize over the raw Pair body).

Total ~200 lines for encMp, ~30 lines for encMpPass.

### Alternative: case33-without-checks

If the full-check-based encMp proves too painful, a simpler
case33-without-checks would produce `rbSndSnd` unconditionally.
This is *unsound in isolation* (fake encMp(sub1, sub2) with
non-matching sub-proofs would still validate).  BUT for the Gödel II
chain, all sub-proofs are constructed correctly, so the weaker
case33' version suffices *when combined with the caller's sub1Corr
and sub2Corr*.  This would shrink encMp to ~80 lines.

Document clearly in a comment that this weakens soundness for a
stand-alone user but is safe in the chain context.

### Step 6: Transcribe Guard Th 14 chain in BRA

New file `Guard/GodelIIBRAv2.agda`. Keep `Guard/GodelIIBRA.agda`
unchanged (Provable-layer placeholder); v2 is the one that actually
closes.

#### Notation

Throughout the chain, we use:
  * `x = var zero` — the proof-slot free variable.
  * `j = reify cGSCR` — Gödel number of gsCR, a closed Term.
  * `thx = ap1 (thmT trivCT) (var zero)` — "th applied to x".
  * `rhsT` — the `sub(i,i)` term from GodelIClassical (closed).
    `rhsT = reify cGSCR = j` provably via `diagFTargetCR`.
  * `cor : Fun1` — the `num`-analog (Guard.CodeOfReify). `cor x` is
    the "underlined x" of Guard Def 12.

#### Required helpers (reuse from RouteADf.agda and construct)

From `Guard/RouteADf.agda` (**already committed, typechecked**):
  * `thm13AtRefl : (t y : Term) {hyp : Formula} -> BRA hyp (atomic (eqn t y)) -> BRA hyp (atomic (eqn (thmT trivCT (DfRefl t y)) (encEqRefl t y)))`
    — rename Provable to BRA during port. This IS our Th 13 lift.

Need to construct (derivable from existing BRA + fromDeriv):
  * `hypSyll : BRA h (P imp Q) -> BRA h (Q imp R) -> BRA h (P imp R)`
    — derived from axK, axS, mp (already in `Guard/ProvableEqLifts.agda` as `hypSyll'`; port to BRA).

Need to construct (genuinely new):
  * `contraposition : BRA h ((P imp Q) imp ((not Q) imp (not P)))`
    — derivable from `axNeg`. ~15 lines.

#### The 5 chain steps (Guard p.17 ordering)

Let `conjHyp : Formula = atomic (eqn thx j)`  ("th(x) = j" as BRA formula).

**Step 1**: `BRA (atomic Triv) (conjHyp imp atomic (eqn (thmT trivCT (DfRefl thx j)) (encEqRefl thx j)))`.
Direct: `deductionThm conjHyp _ (thm13AtRefl thx j ruleHypB)`.
~10 lines. **Already done in `RouteAChain.agda` — port Provable→BRA.**

**Step 2**: `BRA (atomic Triv) (atomic (eqn (thmT trivCT (DfRefl rhsT j)) (encEqRefl rhsT j)))`.
Closed, no hyp discharge. `thm13AtRefl rhsT j (fromDeriv diagFTargetCR)`.
~5 lines. **Already done in `RouteAChain.agda` — port.**

**Step 3**: `BRA (atomic Triv) (conjHyp imp atomic (eqn (thmT trivCT (DfRefl thx j)) (ap2 Pair (cor thx) (cor rhsT))))`.
Reuses DfRefl thx j; rewrites 2nd-slot `cor j` to `cor rhsT` via
`diagFTargetCR + prSym + prCong1 cor + prCongR Pair + prTrans`.
~30 lines. **Already done in `RouteAChain.agda` — port.**

**Step 4**: `BRA (atomic Triv) (conjHyp imp atomic (eqn (thmT trivCT Y) (encEqRefl (TreeEq thx rhsT) poo)))` for some Y.
  * Construct Y: `Y = encMp (sub4a) (sub4b)` where:
    - sub4a is an encoded proof of gsCR's contrapositive under hyp.
    - sub4b is an encoded tautology `t` (Guard's "x₀ = x₂ ⊃ (x₁ = x₂ ⊃ x₀ = x₁)").
  * **Alternative (recommended)**: construct Y directly using
    encAxRefl (of a specific closed witness) + a cor-rewrite chain,
    avoiding the complexity of Guard's Y.  Specifically, under
    `thx = j` and `rhsT = j`, we can derive `TreeEq thx rhsT = O`
    directly as a Deriv, encode via `thm13AtRefl` analog.  The
    REMAINING question for step 4 is what the encoded ≠ form looks
    like — see below.
  * **The key design decision**: Our encoding of "A ≠ B" is the
    equation "TreeEq A B = poo".  Its encoded form at thmT level is
    `reify (codeEqn (eqn (TreeEq A B) poo))`.  Under the whole-
    underline convention, this is `encEqRefl (TreeEq thx rhsT) poo`.
    So step 4 asks for Y such that thmT(Y) = this term.  Using
    thm13AtRefl at t = TreeEq thx rhsT, y = poo, with hypothesis
    Provable(`TreeEq thx rhsT = poo`)…  but this hypothesis IS gsCR.
  * **Resolution**: step 4 cannot be derived from `thx = j` alone at
    the BRA layer without additional content.  BUT: step 4 is NOT
    DERIVED from thx=j in Guard's chain — "by the definition of j"
    is Guard's justification.  In BRA terms, j's definition
    literally IS that Gödel number, so a specific Y built to match
    encodes the identity trivially.
  * **Concrete Y**: Y = `encAxRefl (reify cGSCR)`.  Via encAxReflCorr,
    `thmT trivCT Y = Pair (reify cGSCR) (reify cGSCR)` = encEqRefl
    (reify cGSCR) (reify cGSCR).  But this is "j = j", not "th(x) ≠
    sub(i,i)".  So this naive Y doesn't work.
  * **The right Y** (via encSub, which is `ruleInst` at tag n23):
    encode `reflForm var0` where reflForm is "TreeEq var0 var0 = O"
    (a closed derivable Deriv), then ruleInst with (thx, 0) to get
    "TreeEq thx thx = O".  Then thx=j+rhsT=j rewrites to get
    "TreeEq thx rhsT = O" encoded.  Which is the OPPOSITE of step 4
    (poo vs O)…
  * **Honest note**: step 4's full transcription in our whole-
    underline form IS delicate.  Recommended approach: **REPLACE
    Guard's step 4 with a Deriv-level lemma**.  Since the chain
    ultimately produces BRA facts via fromDeriv, we can construct
    the step-4 content directly as a Deriv `{h} -> Deriv h
    (step4-eqn)` using the existing equational machinery, then lift
    via fromDeriv. The internal step-4 content becomes a closed
    Deriv identity, bypassing formula-level MP encoding.

**Step 5**: `BRA (atomic Triv) (conjHyp imp atomic (eqn (thmT trivCT combined) codeBotT))`.
  * combined = `encMp (sub5a) (sub5b)` where sub5a is step-3's Df,
    sub5b is step-4's Y (both via encMp composition).
  * Proof: compose step-3 with step-4 via encMp's transitivity on
    encoded equations + hypSyll' (at the BRA implication level).
  * Requires encMpCorr with correctly-typed sub-proofs.
  * ~50 lines.

**Closure** (`ChainBRA = conBRAEqn ⊃ atomic gsCR` at Triv):
  1. `ruleSub zero combined (conBRAEqn-side-condition-trivial) dCon`:
     BRA (atomic Triv) (atomic (substEq zero combined conBRAEqn))
     = BRA _ (atomic (eqn (TreeEq (thmT trivCT combined) codeBotT) falseT))
     ≡ "th(combined) ≠ codeBotT" (which conflicts with step 5 under conjHyp).
  2. Compose step 5's conclusion (`conjHyp ⊃ th(combined) = codeBotT`) with
     the contrapositive (`th(combined) ≠ codeBotT ⊃ ¬conjHyp`) using
     `axNeg + mp`: obtain `atomic Triv ⊃ (¬conjHyp)`.
  3. ¬conjHyp = `not (atomic (eqn thx j))` = "th(x) ≠ j".
  4. Rewrite j = rhsT via `diagFTargetCR + axEqCongR`: obtain
     `not (atomic (eqn thx rhsT))` = "th(x) ≠ rhsT" = gsCR-content
     (modulo impT-wrapping if gsCR uses impT form).
  5. **NOTE**: our gsCR = `eqn (TreeEq thx rhsT) poo`, which is
     already TreeEq-form not a `not` formula.  So the closure needs
     to bridge `not (atomic (eqn thx rhsT))` (BRA-level negation) to
     `atomic (eqn (TreeEq thx rhsT) poo)` (equation-form).  This
     bridge uses: at the Deriv/thmT level, TreeEq-self + axTreeEqNN
     pattern.  ~30 lines.
  6. Package: `BRA (atomic Triv) (conBRAEqn ⊃ atomic gsCR)` = ChainBRA.
  7. Feed to `provableGodelIBridge` (ported from Provable): closes
     `Consistent Triv -> BRA (atomic Triv) (atomic conBRAEqn) -> Empty`.

~250 lines total for Step 6, not ~200. Revised estimate.

### Step-4 design caveat (read carefully)

The step-4 sub-issue (above) is the one legitimate soft spot in the
plan.  If during implementation step 4 proves unexpectedly painful,
the **escape hatch** is:

  * Replace step 4's encMp-based Y with a Deriv-level proof of the
    step-4 equation, then `fromDeriv` lift into BRA.
  * The Deriv-level proof uses: `thx = j` and `rhsT = j` (closed)
    to derive an equation that, when encoded, gives a specific
    thmT output.
  * This avoids encMp for step 4 entirely; only step 5 uses encMp.
  * Shortens encMp's required sophistication.

If even this escape hatch surfaces an obstruction, STOP and report
back.  Do not introduce ad-hoc postulates or workarounds.

### Step 7: Port downstream BRA users

`Guard/ConBRA.agda`, `Guard/ProvableGodelIBridge.agda`, `Guard/GodelIIBRA.agda`
port by mechanical `Provable -> BRA` substitution (they don't use `ruleSub`,
just `mp` and `fromDeriv`). Keep old `Provable.agda` as deprecated.
~150 lines modified.

### Optional: Soundness proof for BRA

`Guard/BRASound.agda` — classical semantic model showing all BRA
constructors preserve validity. `ruleSub` is sound under its
Eq-side-condition. Parallel to existing `ProvableSound.agda`. ~150 lines.

Not required for Gödel II but valuable for robustness.

## Architecture invariants to maintain

1. `Deriv` is frozen. Do not modify `Step.agda`. Gödel I lives in Deriv.
2. BRA operates OVER Deriv via `fromDeriv`. BRA statements about
   equations reduce to Deriv proofs.
3. Formula-level encoders (encAxK/S/Neg/Mp) extend `thmT`'s dispatch at
   the END (n30+). Existing encoders at tags 0-29 are unchanged.
4. `ruleSub`'s side condition is `Eq (substF x t hyp) hyp`, mirroring
   `ruleInst`'s Option A discipline. At `hyp = atomic Triv` the
   condition holds trivially (Triv is closed).
5. No new Deriv axioms. The BRA layer adds only rules/axioms that are
   justifiable classically.

## Estimated total time

- Encoders encAxS, encAxNeg, encMp: ~400 lines, 1 session.
- Chain transcription: ~200 lines, 1 session.
- Port: ~150 lines, 0.5 session.
- Soundness (optional): ~150 lines, 0.5 session.

**Total: ~750 lines, 2-3 sessions.**
