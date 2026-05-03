# Next session — `thmT` parametric Definition 12 line 2 (DONE)

## Summary (2026-05-02)

The structural fix proposed in `BRA/NEXT-SESSION-THMT-PARAMETRIC.md` is **done**, but **not** via Route 1 (mutual block).  Route 1 was *infeasible*: Agda's termination checker rejects circular mutual constants of an inductive type (verified by direct test — see "Why not Route 1" below).

Instead, the fix follows the pattern documented in `BRA/ARCHITECTURE-FINDINGS.md` Finding 1 (the `parDispCongL/R` reorder): **reorder the `encRuleInst` payload so the OPEN proof-index sits at the outer Snd**, with the closed `(varCode, tCode)` pair at the inner Fst.

This eliminates the inner-distribution shape obligation entirely — `body_ruleInst`'s extractor only needs ONE distribution of `thmT` (over a closed Pair), and there is no shape requirement on the proof-index.

## Files changed

  * `BRA/Thm/Parts/RuleInst.agda` — `encRuleInst` reordered to
    `nd tag (nd (nd (code(var x)) (code t)) y_h)`.
  * `BRA/Thm/ThmT.agda`:
    - `body_ruleInst` simplified to
      `Fan (Lift (Comp Fst Snd)) (Post (Comp Snd (Comp Snd Snd)) Pair) subT`.
    - `body_ruleInst_eval` re-proved with the simpler structure.
    - `thmTDispRuleInst` updated to use ONE distribution.
    - `body_ruleInst_eval_param` and `thmTDispRuleInst_param`:
      **xShape parameter dropped** — both are now shape-free in the
      proof-index.
    - `encodeRich (ruleInst ...)` updated to use new payload.
  * `BRA/Thm12/Param/RuleInst.agda` — `parEncRuleInst` reordered.
  * `BRA/Thm14SubLemma.agda` — xShape dropped, `thmTSubLemma` is now
    shape-free.
  * `BRA/Thm14Constr5Final.agda` — `f_part`, `K_part`, `h_part` re-shaped
    to put proof-index at outer Snd.
  * `BRA/SbRuntime.agda` — `Df_F1_I` re-shaped to new layout.
  * `BRA/Th12Z.agda` — `Df_F1_Z` re-shaped to new layout (and stale
    `axRecLf O stepCor` -> `axRecLf stepCor` repair).
  * `BRA/Th12Fst.agda`, `BRA/Th12Snd.agda`, `BRA/Th12FstLf.agda`,
    `BRA/Th12SndLf.agda` — stale `axRecLf O stepCor` repairs (unrelated
    to the encoding refactor; pre-existing breakage from a prior
    `axRecLf` signature change).
  * `BRA/Thm14Step4Test.agda` — replaced with a tiny demonstration of
    the new shape-free dispatch.

## Verified to typecheck

  * `BRA/Thm/ThmT.agda`               (~6s with cache)
  * `BRA/GoedelII.agda`               (composes; still parametric over
                                       `constr5` and `step5`)
  * `BRA/Thm14SubLemma.agda`          (shape-free)
  * `BRA/Thm14Constr5Final.agda`      (new layout for f/g/K/h_part)
  * `BRA/SbRuntime.agda`              (`Df_F1_I_runtime` works without
                                       xShape)
  * `BRA/Thm14Step4Test.agda`         (one-line `step4_param` derivation)
  * `BRA/Th12I.agda`, `BRA/Th12Z.agda`, `BRA/Th12Fst.agda`,
    `BRA/Th12Snd.agda`, `BRA/Th12Pair.agda`, `BRA/Th12Const.agda`,
    `BRA/Th12FstLf.agda`, `BRA/Th12SndLf.agda`
  * `BRA/Thm12.agda`, `BRA/Thm12Final.agda`

## Files NOT touched (pre-existing breakage)

These files were broken before the refactor and remain broken — they
reference an obsolete `axRecLf` / `axRecNd` signature OR an obsolete
`Rec` constructor.  Not on the Goedel II critical path:

  * `BRA/Thm12RecCheck.agda`, `BRA/Thm12AsymCases.agda`,
    `BRA/Thm12AsymBaseCases.agda`, `BRA/Thm12FstSpotCheck.agda`
  * `BRA/Th12Rec.agda`, `BRA/Th12RecP.agda`, `BRA/Th12RecUnivPair.agda`,
    `BRA/Th12TreeEq.agda`
  * `BRA/StepT12.agda`, `BRA/Thm12AsymParametric.agda`
  * `BRA/Thm12/RecRefactorPlan.agda`, `BRA/Thm12/TreeEqNN.agda` (some
    are sketches)

These can be repaired in a separate session by running
`sed 's/axRecLf O \w\+/axRecLf \w\+/g'` and similar — the fixes are
mechanical.

## Why not Route 1 (mutual block)

The doc proposed embedding `thmT` reference inside `body_ruleInst` via
a `mutual` block.  Tested: Agda rejects this with **TerminationIssue**.
Quoting from `BRA/MutualTest.agda` (now deleted):

```agda
mutual
  data F1 : Set
  data F2 : Set
  data F1 where  base1 : F1 ; use2 : F2 -> F1
  data F2 where  base2 : F2 ; use1 : F1 -> F2

mutual
  a : F1
  a = use2 b
  b : F2
  b = use1 a
```

```
error: [TerminationIssue]
Termination checking failed for the following functions:
  a b
Problematic calls:
  b (at line 19.12-13)
  a (at line 22.12-13)
```

Agda's termination checker requires structural decrease for mutual
recursion of constant values of an inductive type.  Circular references
between two such constants are infinite values and rejected.

The same applies to `body_ruleInst` and `thmT`: if `body_ruleInst`
literally embeds `thmT` (a Fun1) and `thmT` transitively contains
`body_ruleInst`, the value graph is cyclic and not constructible.

## What's now possible (Phase C)

`thmTSubLemma : (n : Nat) (tT y codeP : Term) ->
   Deriv (atomic (eqn (ap1 thmT y) codeP)) -> ...` is **shape-free**.

Phase C of `BRA/NEXT-SESSION-THM14-PHASE-C.md` (the `step3_l..step5_l`
chain in `BRA/Thm14Constr5Final.agda`) can now be filled mechanically:

  1. Use `thmTSubLemma` (shape-free) for each sb-step.
  2. Use `thmTDispMp_param` (already exists) for each mp-step.
  3. Compose into `step5_l : (x : Term) -> Deriv (PrAtX x imp ...)`.

After Phase C, supply `(constr5, step5)` to `BRA.GoedelII.Compose` to
get unconditional `godelII : Deriv Con -> Deriv bot`.

## Constraints honoured

  * ASCII only.
  * `{-# OPTIONS --safe --without-K --exact-split #-}` everywhere.
  * No postulates, no holes, no with-abstraction, no dot patterns.
  * No new `Deriv` constructors (Route 2 not taken — not needed).
  * No mutual blocks (Route 1 infeasible).

## See also

  * `BRA/ARCHITECTURE-FINDINGS.md` Finding 1 — the analogous fix for
    `parDispCongL/R`.
  * `BRA/NEXT-SESSION-THM14-PHASE-C.md` — Phase C plan (now consumable).
