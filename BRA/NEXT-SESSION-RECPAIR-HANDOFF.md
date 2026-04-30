# Next session — Theorem 12 Rec case (Pair-step internalisation)

## Status (2026-04-30)

**Goal:** `Th12_F1_Rec_zs : Deriv P_Th12_Rec_zs` — schematic Theorem
12 for the Rec primitive, with `var 0` free.  Required by Theorem 14
step5 instantiation.

**State:** Lf-case and the BRA-level Pair-case (RecPairCase) are
proved.  Universal closure via `ruleIndBT` requires a step argument
of type

```agda
Deriv ((substF zero (var v1) P_Th12_Rec_zs) imp
       ((substF zero (var v2) P_Th12_Rec_zs) imp
        (substF zero (ap2 Pair (var v1) (var v2)) P_Th12_Rec_zs)))
```

i.e., a closed Hilbert proof of the Pair-case **assuming both IHs
as nested implications**.  This is the only thing left for Rec.

`BRA/Th12RecUniv.agda` (1560 LoC, ~2 s typecheck) carries this gap
as a `WithBasePairParam` sub-module parameter.  All other steps
(A-G plus toIH1Rec_lifted, single-lifted dispatchers) are proved.

## What was tried this session and abandoned

**Approach:** Implement the Hilbert deduction theorem syntactically
by mirroring every dispatcher used in basePair into a "doubly-lifted"
variant operating on `Deriv (P1 imp (P2 imp atomic ...))`.

**Delivered (committed):**

- `BRA/Thm/ThmT.agda` +380 LoC — single-lifted `thmTDispCongL_param_lifted`
  / `CongR` / `RuleTrans` plus their helpers `body_*_eval_param_lifted`,
  `pairOfFan_eval_lifted`, `pairOfConst_eval_lifted`,
  `congLR_extractTj_param_lifted`.  Commit `9673103`.

- `BRA/Thm/ThmT.agda` +778 LoC — doubly-lifted variants
  (`*_doublelifted`), level-2 helpers (`liftAxiomTwo`, `B_combinatorTwo`,
  `liftedRuleTransTwo`, `liftedCong*Two`).  Commit `1d04d46`.

ThmT typechecks ~7 s (the 9-min spike was a one-time recompile cascade
after the first edit; subsequent rebuilds are fast).

**Abandoned:** the `basePair_param` body in `Th12RecUniv.agda` —
~200 LoC of nested `let` bindings invoking the doubly-lifted
dispatchers.  Failed with `NoParseForApplication`, and the structure
itself was clearly the wrong shape (slow to typecheck, fragile, ugly).

## Why it's the wrong shape

The user's principle: small files, fast typecheck.  Slowness signals
**mathematical mismatch**, not engineering inconvenience (see
`feedback_guard_fast_typecheck.md`).  The doubly-lifted dispatcher
chain was hitting both bounds:

- ThmT.agda: 14 000 LoC, well over the ~250 LoC budget.
- The basePair_param body had to thread P1, P2 through every
  intermediate result manually, with `axS / axK / mp` cascades that
  Agda's unifier had to chew through.

This is the brute-force Hilbert deduction theorem.  It works in
principle but the explosion in proof size and unification work
suggests we are not factoring the mathematics correctly.

## The honest mathematical situation

`guard15.pdf` does not cover this step — Guard's Theorem 12 for Rec
is sketched but the full universal-closure derivation is not in the
paper.  We have no roadmap from the source.

This is **expected for Gödel II** and is one of the things that makes
its formalisation hard.  Internalising the inductive step of a
recursion-defined function inside an axiomatic system is the
load-bearing piece of the second incompleteness theorem.  Other Thm 12
cases (Fst, Snd, IfLf, etc.) are leaf-or-Pair-constant in the IHs
and discharge cleanly via `fromBaseAndPair` (axK + axK + ruleIndBT).
Rec is the first case where the IHs are **genuinely used** in the
Pair-case proof — the `RecPairCase` chain embeds `ih1.image` and
`ih2.image` into the encoded equation.  So the deduction theorem
really does need to bite, and at two levels.

## Open questions for fresh analysis

1. **Different formula shape for `P_Th12_Rec_zs`?**  The current
   formula bundles "thmT(Df_F1_Rec_zs(var 0)) = codeFTeq1Asym ..."
   into a single atomic Eq.  Maybe a richer formula (e.g.,
   incorporating an explicit witness that lets ruleIndBT's IHs be
   used by Term-level computation rather than Deriv-level
   substitution) would let the proof be IH-constant — and then
   `fromBaseAndPair` discharges it.

2. **Different `Df_F1_Rec_zs` shape?**  The current Df uses
   `Comp2 Pair (KT tagCode_ruleTrans) inner_Rec`.  Maybe a Df whose
   recursive structure carries the IH-witness internally (so the
   Pair-case BRA-level evaluation IS the IH-application, and the
   proof at Pair input doesn't need an external Deriv hypothesis)
   would dissolve the obstacle.

3. **A different rule than `ruleIndBT`?**  ruleIndBT's step argument
   shape is what forces the doubly-lifted form.  Could the universal
   closure for Rec be reached via a different combination (e.g.,
   `ruleInst` + a single-IH lemma proved separately + a global
   composition)?  This would route around the Hilbert deduction
   theorem entirely.

4. **Single-shot deduction theorem at the BRA level?**  Instead of
   walking through every dispatcher node, prove ONE general
   "Hilbert deduction theorem for atomic Eq derivations" lemma in
   BRA/Deriv.agda or a small new file:

   ```
   deductionEq : (P : Formula) (a b : Term) ->
                 (Deriv (atomic (eqn ?? ??)) -> Deriv (atomic (eqn a b))) ->
                 Deriv (P imp atomic (eqn a b))
   ```

   if such a thing is provable for the specific shape we need.
   This may not exist in general (Agda functions aren't Hilbert
   proofs) but might exist for the **linear** case (input used once),
   which would cover most of basePair's structure if we can refactor
   the chain to use each IH-image exactly once.

5. **Look at how Ryan / Rose handle this for HBL (Hilbert-Bernays-Löb)
   provability conditions.**  Theorem 14 of guard15.pdf cites HBL
   provability conditions; the analog for Rec inside BRA might
   point at the right factoring.

## Constraint reminders for next session

- Files ≤ ~250 LoC.
- Typecheck < 2 s per file.
- If the candidate proof shape blows past either bound, **stop and
  rethink the math**.  Do not push through with abstract blocks or
  splits hoping the bound clears — the bound is the signal.
- Slow typecheck on a single fresh edit is the loudest indicator
  that the formulation has diverged from the underlying mathematics.

## Files to read at session start

1. `BRA/NEXT-SESSION-RECPAIR-HANDOFF.md` (this file).
2. `BRA/Th12RecUniv.agda:1089-1494` — current WithClosure module,
   basePair (concrete) and WithBasePairParam parameter shape.
3. `BRA/Th12Rec.agda:235-565` — RecPairCase, the BRA-level
   Pair-case proof (uses ih_v1, ih_v2 IH images).
4. `BRA/Deriv.agda:220-232` — ruleIndBT signature.
5. `BRA/FromBaseAndPair.agda` — how IH-constant Pair-case proofs
   are usually discharged.
6. Memory: `feedback_guard_fast_typecheck.md`,
   `feedback_th14_needs_schematic_repeated.md`,
   `feedback_ski_syntactic_translation.md`,
   `project_th12rec_univ_progress.md`.
