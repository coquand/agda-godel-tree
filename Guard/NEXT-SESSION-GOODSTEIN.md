# Next session: close stepFCoreFromConStrong (Phase C+D)

## Command

```
claude
```

Then paste:

```
Read Guard/NEXT-SESSION-GOODSTEIN.md and Guard/GOODSTEIN-PLAN.md for
context.  Also read Rose1.pdf (at repo root, /Users/coquand/CHWISTEK/Rose1.pdf)
pp. 382-384 for the Theorem 4 / Main Theorem chain — follow it
rule-by-rule per feedback_follow_rose_paper.md.

Goal: transcribe the Goodstein-style chain into
stepFCoreFromConStrong : Deriv Triv ConTrivRoseStrong -> StepFCoreType
using the Goodstein infrastructure delivered last session (axGoodstein
axiom, treeEqRefl, extended roseLemma1T / thm14EV3 / ProofEnc chains).

The impT-to-=poo bridge is a Schema-F induction establishing TreeEq
2-valuedness, mechanical per Rose1.pdf.  Not open-ended.

Conventions: --safe --without-K --exact-split, no postulates, no holes.
Use ~/.cabal/bin/agda-2.9.0.
Commit after each major piece.

Proceed autonomously.
```

## Status

Phases A and B of Guard/GOODSTEIN-PLAN.md are complete.
Phase C (chain transcription) + Phase D (top-level closure) remain.

### Delivered (committed)

- `[goodstein-A1-A2]` 1edbe6f — Guard/Step.agda adds axGoodstein
  constructor; Guard/DerivLift.agda extends lift with axGoodstein case.

- `[goodstein-A3-A6]` 5452b27 — full fan-out into the thmT evaluator
  and Deriv-pattern-matching recursors:
    * Guard/ThFunTForV3.agda: case29 + ndT29V3/ndT30V3 redesign
    * Guard/ThFunTForV3Pass.agda: 29-miss ndDispatchV3PairMiss /
      ndDispatchV3OPairMiss chains
    * Guard/ProofEnc.agda: encAxGoodstein / encAxGoodsteinCorr /
      encAxGoodsteinPass
    * Guard/RoseLemma1T.agda: roseL1T_AxGoodstein + dispatch
    * Guard/Thm14EV3.agda: thm14EV3AxGoodstein (wraps ProofEnc helpers)
      + dispatch; imports Guard.ProofEnc (no cycle).

- `[goodstein-B]` 11f3124 — Guard/TreeEqRefl.agda:
    treeEqRefl : Deriv hyp (TreeEq a b = O) -> Deriv hyp (a = b)
  Five-step chain using axGoodstein + axIfLfL + congL.

Guard/GodelIIClassicalTrivStrong.agda still typechecks; the
top-level theorem remains parameterised by stepFCoreFromConStrong
(now the only open piece).

### What remains: Phase C (chain transcription) + Phase D (close theorem)

The target:

```agda
stepFCoreFromConStrong :
  Deriv Triv ConTrivRoseStrong -> StepFCoreType
-- where StepFCoreType = Deriv Triv (eqn (ap2 TreeEq (thmT trivCT pv)
--                                                    diagBody)
--                                        poo)
-- pv = Pair v0 v1
```

#### Chain structure (per Ryan.pdf p.459 + Rose1.pdf p.383)

Reductio under the hypothetical
`H_enc = eqn (ap1 (thmT trivCT) pv) (reify cGSCR)`
("Pair v0 v1 encodes gsCR under thmT trivCT"):

1. Under H_enc: derive B_aux = `eqn (ap2 TreeEq (ap1 (thmT trivCT) pv)
   diagBody) O` (= "TreeEq of thmT-evaluation and diagBody is 0").

   dAux already exists in Guard/GodelIIClassicalTriv.agda (uses
   ruleHyp{H_enc} + diagFTargetCR + treeEqSelf).

2. Apply roseLemma1T dAux v0 v1 tCorr tPass — produces V1 : Term with

     vCorr₁ : Deriv hyp (thmT trivCT (Pair (vPa V1) (vPb V1))
                         = reify (codeEqn B_aux))

   conditional on caller's tCorr witnessing that Pair v0 v1 encodes
   H_enc under thmT trivCT.

3. Construct the key step via **treeEqRefl**:

   Under the hyp "Pair v0 v1 encodes gsCR", we have (by 2.vCorr₁) that
   V1 encodes B_aux = "TreeEq (thmT trivCT pv) diagBody = O".  Apply
   treeEqRefl at the encoded level to transport this into the
   equation  thmT trivCT pv = diagBody.  The detail: treeEqRefl
   operates on terms directly, not encodings — the meta-role here is
   to provide a Deriv (a = b) from Deriv (TreeEq a b = O).

4. Apply roseLemma1T again to the Deriv-H_enc of
   `thmT trivCT pv = diagBody` (from step 3): produces V2 : Term with

     vCorr₂ : Deriv hyp (thmT trivCT V2 = reify (codeEqn
                           (eqn (thmT trivCT pv) diagBody)))

   This is the "Lemma 1 twice" step of Rose Theorem 4.

5. Apply eTCorrect (Guard.RoseEFun) to V2's conclusion:
     eT (thmT trivCT V2) = reify (codeEqn
                           (eqn (TreeEq (thmT trivCT pv) diagBody) falseT))

6. Apply dConStrong via ruleInst at (var 0 := Pair v0 v1, var 1 := V2):
     impT (TreeEq (thmT trivCT pv) (eT (thmT trivCT V2))) falseT = trueT.

7. Under the H_enc hypothesis, derive the antecedent of step 6 evaluates
   to O (= trueT): thmT trivCT pv = eT (thmT trivCT V2) holds because
   thmT trivCT pv = reify cGSCR (by H_enc) and eT (thmT trivCT V2) =
   reify (codeEqn (...)) = reify (something equal to cGSCR via the
   diagonal identity).  The exact shape needs diagFTargetCR plumbing.

8. So impT O falseT = falseT (axIfLfL); but step 6 gives impT = trueT.
   Hence Deriv H_enc (falseT = trueT) — inconsistency under H_enc.

9. Discharge H_enc: since we have Deriv H_enc (falseT = trueT), we know
   that Triv does NOT prove H_enc (else Triv would be inconsistent,
   which is not what we're proving here).  This step is tricky — the
   "does not prove" is a meta-statement, not an equation.

10. The step-F core StepFCoreType states TreeEq (thmT trivCT pv)
    diagBody = poo.  This holds iff  thmT trivCT pv ≠ diagBody  iff
    H_enc is not provable.  Classical-Gödel-II reasoning uses the
    above chain + Triv-consistency to derive this.

#### The sticky point — reassessed as mechanical

An earlier session's handoff (and the 2026-04-21 Phase-A+B session
debrief) flagged step 2 and the step-9/10 discharge as a potential
**design gap**.  On closer reading of Rose1.pdf this is wrong:
Rose's calculus is Goodstein-style (explicit equational recursion),
**not Peano-PRA**, so the "impT = trueT  →  TreeEq = poo" bridge is
**equationally derivable** — just non-obvious.

The likely mechanism is a Schema-F induction establishing **2-valuedness
of TreeEq's output** on the relevant term family.  axGoodstein is
exactly the ruleF step-case building block; treeEqRefl handles one
direction (=0 gives equality, closing the reductio); and the =poo
direction is the ruleF consequence when combined with dConStrong's
"not =0".  This puts the bridge squarely inside the 200-400-line
transcription budget.

Three routes to the polymorphic-tCorr obstacle (see
Guard/RoseChainAnalysis.md lines 165-180):

  (i) Encode tPa, tPb as direct Term-level witnesses of
      H_enc's content + supply tCorr from a Triv-polymorphic chain
      using axGoodstein + treeEqRefl.  **This is the intended route**
      — the Goodstein-axiom infrastructure was designed for it.

  (ii) Redesign gsCR with a hypothesis-code slot (V3-style).  Heavy.

  (iii) More Schema-F splits to bypass the Pair-var case.  Stuck.

#### Key new lever: treeEqRefl

`treeEqRefl` transforms `Deriv hyp (TreeEq a b = O)` into `Deriv hyp
(a = b)`.  Previously, deriving `a = b` required a chain of congX
rewrites and the equation `a = b` had to be explicit at the outer
level.  treeEqRefl lets us work with TreeEq-form statements and
project to equality form at the end, which matches the shape of
Ryan's Main Theorem chain (the V2 encoding produces a TreeEq-form
equation B_aux that we then convert to equality form for the next
Lemma 1 application).

### Size estimate

200-400 lines for `stepFCoreFromConStrong`, per original plan.

### Approach

1. **Build the core hypothetical chain** (under hyp = H_enc):
   dAux → roseLemma1T → treeEqRefl → roseLemma1T-again → eTCorrect →
   ruleInst dConStrong → modus ponens → falseT = trueT.

2. **Discharge H_enc** via the "internal Gödel II" trick.  Possibly
   uses impTProp lemmas from Guard.ImpTProp to object-level-ify the
   reasoning.

3. **Plug into stepFCoreFromConStrong**.

4. **Close** `godelIIClassicalTrivStrong = ... godelIIClassicalTrivStrongWithCoreFromCon stepFCoreFromConStrong`.

### Files likely touched

- `Guard/GodelIIClassicalTrivStrong.agda` (+200-400 lines).
- Possibly `Guard/RoseLemma1T.agda` if a polymorphic tCorr helper
  needs adding there.
- Possibly `Guard/RoseEncE.agda` or `Guard/ImpTProp.agda` for auxiliary
  object-level reasoning lemmas.

### Risk map (revised)

| Phase | Risk | Mitigation |
|---|---|---|
| Chain steps 1-7 | medium | use treeEqRefl + existing lemmas; worked-out sketch above |
| Step 8 (falseT=trueT under H_enc) | low | reduces to axIfLfL + ruleTrans |
| Step 9-10 (discharge H_enc + land on TreeEq = poo) | medium | Schema-F 2-valuedness of TreeEq via axGoodstein + treeEqRefl + dConStrong; mechanical transcription of Rose1.pdf's Goodstein-style chain |
| Phase D assembly | low | just godelIIClassicalTrivStrongWithCoreFromCon + composition |

**Key insight (2026-04-21 reassessment)**: Rose1.pdf's equational
calculus is Goodstein-style, so the "impT = trueT → TreeEq = poo"
step is not a design gap requiring new theory — it is a Schema-F
induction establishing TreeEq's 2-valuedness equationally.
axGoodstein is specifically the step-case ingredient Rose uses for
this induction.  Phase C/D is transcription work, not open-ended
research.

## Past incarnations of this handoff

- Session 2026-04-21 (prior): plan written + infrastructure attempted
  + reverted.  Handoff for axGoodstein full fan-out.

- Session 2026-04-21 (this): Phase A + Phase B delivered (3 commits).
  Handoff for Phase C + Phase D.
