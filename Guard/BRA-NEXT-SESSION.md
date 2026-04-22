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

New file `Guard/GodelIIBRAv2.agda` (or rename existing `GodelIIBRA.agda`).

Skeleton:

```agda
module Guard.GodelIIBRAv2 where

open import Guard.Base
open import Guard.Term
open import Guard.Step using (Deriv ; Consistent)
open import Guard.Formula
open import Guard.BRA
open import Guard.ThFunTForV3 using (thmT)
open import Guard.ProofEnc  -- existing equational encoders
open import Guard.ProofEncFormula  -- new formula-level encoders
open import Guard.SubstTForPrecompClassical using (Triv ; gsCR ; cGSCR ; trivCT ; templateCodeCR)
open import Guard.ConBRA using (conBRAEqn ; ConBRA ; conBRAEqnSubstZero)
open import Guard.GodelIClassical using (godelIClassical ; diagFTargetCR)
open import Guard.ProvV3 using (codeBotT)
open import Guard.Thm14EV3 using (thm14EV3 ; encT ; corr)

-- Guard Th 14 transcription:
--
-- Step 1-5 from guard15.pdf p.17.  Each step as a BRA (atomic Triv) lemma.
-- Step 5's combined proof uses encMp + existing encoders.
-- Closure uses:  ruleSub on dCon (with Eq-side-condition trivial at Triv)
-- + axNeg + mp to produce Provable (atomic Triv) (atomic gsCR).
-- Then provableGodelIBridge (ported to BRA) closes.

-- godelII_BRA : Consistent Triv -> BRA (atomic Triv) (atomic conBRAEqn) -> Empty
```

~200 lines.

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
