# Next session: execute the Goodstein-axiom plan

## Command

```
claude
```

Then paste:

```
Read Guard/NEXT-SESSION-GOODSTEIN.md and Guard/GOODSTEIN-PLAN.md for context, then proceed.

Goal: add  axGoodstein  as a new Deriv axiom and execute the full
fan-out, then close  stepFCoreFromConStrong  via the Goodstein-based
treeEqRefl meta-function and Ryan's Main Theorem chain.

Conventions: --safe --without-K --exact-split, no postulates, no holes.
Use ~/.cabal/bin/agda-2.9.0.
Commit after each major piece.

Proceed autonomously.
```

## Why the plan needs a full session (not a partial one)

Adding `axGoodstein` as a Deriv constructor requires updating
EVERY pattern-match on Deriv in the repo.  Attempting a minimal
add-then-stub approach fails because:

- `roseLemma1T`'s new axGoodstein case requires a valid `Lemma1T`
  record, which needs `vPa, vPb : Term` encoding the axiom plus
  `vCorr : Deriv hyp (eqn (ap1 (thmT trivCT) (Pair vPa vPb)) (reify
  (codeEqn B)))` — a polymorphic derivation that `thmT trivCT`
  evaluates the encoding to the correct codeEqn.  No existing
  encoding matches `B = eqn (ap2 IfLf ...) (ap2 IfLf ...)`; we
  genuinely need a new dispatch case.

- Similarly `thm14EV3` needs a `ProofE3` record for this axiom, with
  a new tag in `Guard/ThFunTForV3.agda`'s `ndDispatchV3` and a new
  `case29` Fun2 that produces the correct codeEqn.

- Without those, the fan-out leaves RoseLemma1T.agda and
  Thm14EV3.agda non-exhaustive — Agda rejects them.

Cannot ship a "partial" axGoodstein addition that leaves repo broken.

## Sequence of work

### Phase A (Infrastructure)

1. **`Guard/Step.agda`**: add `axGoodstein (a b : Term) : Deriv hyp
   (eqn (ap2 IfLf (ap2 TreeEq a b) (ap2 Pair a O)) (ap2 IfLf (ap2
   TreeEq a b) (ap2 Pair b O)))`.  ~4 lines.

2. **`Guard/DerivLift.agda`**: `lift (axGoodstein a b) = axGoodstein
   a b`.  1 line.

3. **`Guard/ThFunTForV3.agda`**: extend `ndDispatchV3` to recognize a
   new tag (say `n29`).  Currently the chain bottoms out at
   `ndT29V3 = sndArg2`; replace with `ndT29V3 = branch (tc n29)
   case29 sndArg2` where `case29 : Fun2` is the encoder for
   axGoodstein.  Design `case29` as a Fan/Pair expression matching
   the codeEqn of `eqn (IfLf (TreeEq a b) (Pair a O)) (IfLf (TreeEq
   a b) (Pair b O))` from the input body encoding `Pair aC bC`
   where `aC = reify (code a), bC = reify (code b)`.  ~20-30 lines.

4. **`Guard/ProofEnc.agda`**: add `encAxGoodsteinCorr` and
   `encAxGoodsteinPass` helpers — parallel to
   `encAxTreeEqNNCorr/Pass`.  Use `ndBranchMiss` lemmas to navigate
   to tag n29, then `ndBranchHit` + structural reduction.  ~40-80
   lines.

5. **`Guard/RoseLemma1T.agda`**: add `roseL1T_Goodstein : (H :
   Equation) (a b : Term) -> Lemma1T H (eqn ...)` using the new
   helpers, and extend the top-level `roseLemma1T` dispatch.  Also
   extend the helper functions `aRPass`, `f1DM`, `f1gDM`, `f2xDM` in
   the private block to route tag n29 through their ndDispatchV3PairMiss
   calls.  ~30-60 lines.

6. **`Guard/Thm14EV3.agda`**: add `thm14EV3Goodstein : (H : Equation)
   (a b : Term) -> ProofE3 H (eqn ...)` parallel to `thm14EV3AxRefl`,
   and extend the top-level `thm14EV3` dispatch.  Also add a
   `axGoodsteinPassthroughV3` helper in `Guard/ThFunTForV3Pass.agda`
   or equivalent.  ~80-150 lines.

### Phase B (Reflection meta-function)

7. **`Guard/TreeEqRefl.agda`** (new): define

```agda
treeEqRefl : {a b : Term} {hyp : Equation} ->
             Deriv hyp (eqn (ap2 TreeEq a b) O) ->
             Deriv hyp (eqn a b)
treeEqRefl {a} {b} treeEqHyp =
  ruleTrans
    (ruleSym step3)
    (ruleTrans step2 step4)
  where
  step1 : Deriv hyp (eqn (ap2 IfLf (ap2 TreeEq a b) (ap2 Pair a O))
                         (ap2 IfLf (ap2 TreeEq a b) (ap2 Pair b O)))
  step1 = axGoodstein a b

  -- Rewrite LHS of step1 using treeEqHyp.
  step2 : Deriv hyp (eqn (ap2 IfLf (ap2 TreeEq a b) (ap2 Pair a O))
                         (ap2 IfLf O (ap2 Pair a O)))
  step2 = congL IfLf (ap2 Pair a O) treeEqHyp

  step3 : Deriv hyp (eqn (ap2 IfLf O (ap2 Pair a O)) a)
  step3 = axIfLfL a O

  -- (Similarly bridge step1's RHS to b.)
  ...
```

~30-50 lines.

### Phase C (Chain transcription)

8. **`Guard/GodelIIClassicalTrivStrong.agda`**: transcribe Ryan's
   Main Theorem chain into `stepFCoreFromConStrong`.  Uses:
   `thm14EV3` (Lemma 2), `roseLemma1T` (Lemma 1), `eTCorrect` (ε),
   `godelIClassical` (Lemma 3), `treeEqRefl` (new, from step 7),
   `axGoodstein` (for any direct uses).

   Chain structure per Ryan.pdf p.459 Main Theorem + Rose1.pdf p.383
   Theorem 4 proof:

   1. Assume dConStrong + reductio assumption "z is proof of gsCR"
      (encoded as hypothesis `H_enc` using `ruleHyp`).
   2. Under H_enc: derive `G(z) = 0` via `congR TreeEq + treeEqSelf`.
   3. Apply `thm14EV3` to step 2's derivation → proof-code `p_G` with
      `thmT trivCT p_G = reify (codeEqn {G(z) = 0})`.
   4. Construct derivation `{G(z) = 0} ⊢ {se(N,N) = th(z)}` using
      `treeEqRefl` (the new Goodstein-derived meta-function).
   5. Apply `roseLemma1T` to step 4's derivation → V with `thmT
      trivCT V = reify (codeEqn {se(N,N) = th(z)})` conditional on
      tCorr for the hypothesis `{G(z) = 0}`.
   6. Apply `eTCorrect` to get `ε(thmT trivCT V) = reify (codeEqn
      {se(N,N) ≠ th(z)})`.
   7. Apply `dConStrong` at (var 0 := z, var 1 := V) with the
      transform from step 6.
   8. Close by reductio against the diagonal identity
      (`diagFTargetCR`) and `godelIClassical`.

   ~200-400 lines.

### Phase D (Close the top-level theorem)

9. **Provide `stepFCoreFromConStrong`** satisfying its type signature
   in `Guard/GodelIIClassicalTrivStrong.agda`.  Combine with existing
   `godelIIClassicalTrivStrongWithCoreFromCon` to obtain the actual
   `godelIIClassicalTrivStrong : Consistent Triv -> Deriv Triv
   ConTrivRoseStrong -> Empty`.

10. **Typecheck**: `~/.cabal/bin/agda-2.9.0
    Guard/GodelIIClassicalTrivStrong.agda`.  Fix any errors.

11. **Commit**: final commit with message summarising what's done.

## Estimated total

~400-700 lines, 1 focused session if infrastructure pieces click
cleanly; 2 if the Thm14EV3 dispatch extension needs debugging (it's
the most fragile part — 2448-line file, 29 existing tags, careful
ndBranchHit/ndBranchMiss chain).

## Risk map

| Phase | Risk | Mitigation |
|---|---|---|
| A1-A2 | none | one-liners |
| A3 (ThFunTForV3 dispatch) | low-medium | copy existing branch pattern |
| A4 (ProofEnc helpers) | medium | parallel to existing enc*Corr/Pass |
| A5 (RoseLemma1T case) | low-medium | 17+ existing analogues to copy |
| A6 (Thm14EV3 case) | medium-high | 29 existing cases, but each very specific; the exact encoding structure for IfLf/Pair/TreeEq needs careful derivation |
| B (TreeEqRefl) | low | purely local, uses axGoodstein + existing primitives |
| C (chain) | medium | requires picking correct Term-level instantiations for dConStrong; specific roseLemma1T tCorr supply needs working out |
| D | low | assembly |

## Current session outcome

Plan written + committed.  Infrastructure changes NOT made (reverted
to keep repo green).  Handoff doc in place for next session.
