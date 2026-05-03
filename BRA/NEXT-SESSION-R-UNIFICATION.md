# Next session — unify Rec / RecP into one primitive recursion operator

## SESSION PROGRESS (2026-05-01, evening)

**Step 1 done.**  `treeRec : Fun1 -> Fun2 -> Fun2` is a real Fun2 constructor in `BRA/Term.agda`.  `codeF2` (depth-2 encoding `nd tag (nd (codeF1 f) (codeF2 s))`, tagged `natCode 34`), `substF2`, and `KT` all extended.

**No SplitError.UnificationStuck.**  The dot-pattern-free `encodeRich` (rewritten in the previous session) absorbed the new constructor without coverage-check unification trouble.  This was the feared blocker; it is now empirically a non-issue.

**Step 5 (consumer cascade) done.**  `treeRec` cases added (mostly trivial fall-throughs since axioms aren't yet in scope) to:
- `BRA/CodeCommutes.agda` — `codedSubst_nd_codeF2` + `codeCommutesF2`.
- `BRA/Thm/ThmT.agda` — `fstReifyCodeF2`.
- `BRA/CorF.agda` — `corF1 Fst/Snd/(Rec)`, `corF2 IfLf/TreeEq/(RecP)/(treeRec)` shape dispatchers.
- `BRA/StepT12.agda` — `evalFun2 (treeRec f s)` with the correct equational behaviour (leaf = `evalFun1 f a`, Pair = `evalFun2 s ...`).
- `BRA/StepT12Universal.agda` — `noRec1_KT (ap2 (treeRec f s) a b) = nr_Z`.  `nr_treeRec` constructor for `NoRec2` deferred until `evalCorrect_treeRec` exists.

**Step 6 verified.**  `BRA/Term.agda`, `BRA/Deriv.agda`, `BRA/Thm/ThmT.agda`, `BRA/Thm12.agda`, `BRA/GoedelII.agda`, all 11 `BRA/Thm12/Parts/*.agda` files, and the entire downstream cascade typecheck.

**Step 7 stub.**  `Thm12.FromBridges` gained one new abstract parameter:
```
(D_treeRec_complete : (f : Fun1) (s : Fun2) -> Thm12_F2_Result (treeRec f s))
```
and the corresponding `thm12_F2 (treeRec f s) = D_treeRec_complete f s` clause.  This keeps Thm12 typechecking parametrically; the parameter is discharged when `axRLf, axRNd` are added.

**Base rename.**  `BRA/Base.agda`'s metalevel Tree recursor renamed from `treeRec` to `treeRecMeta` (was unused outside its own definition).

## What's left

- **Step 2: add `axRLf`, `axRNd` to `BRA/Deriv.agda`.**  This is the next step.  Plan-of-attack:
  - `axRLf : (f : Fun1) (s : Fun2) (p : Term) -> Deriv (atomic (eqn (ap2 (treeRec f s) p O) (ap1 f p)))`
  - `axRNd : (f : Fun1) (s : Fun2) (p a b : Term) -> Deriv (atomic (eqn (ap2 (treeRec f s) p (ap2 Pair a b)) (ap2 s (ap2 Pair p (ap2 Pair a b)) (ap2 Pair (ap2 (treeRec f s) p a) (ap2 (treeRec f s) p b)))))`
  - These are plain primitive equational axioms; no derivation tree.

- **Step 3: extend `encodeRich` for the two new axioms.**  Each needs:
  - A new tag in `BRA/Thm/Tag.agda` (`tagAxRLf`, `tagAxRNd`) appended after `tagRuleIndBT2 = 45`.  Place at end so existing `thmTDispAx*` skip chains don't need to grow.
  - `body_axRLf`, `body_axRNd` Fun2 dispatchers in `BRA/Thm/ThmT.agda`.
  - `checkTag_axRLf`, `checkTag_axRNd`, `branch_axRLf`, `branch_axRNd`, `next_axRLf`, `next_axRNd` cascade entries.  Wire into the cascade tail: replace the current fall-through (`next_ruleIndBT2 = ... fallback`) with `... -> checkTag_axRLf -> checkTag_axRNd -> fallback`.
  - `thmTDispAxRLf`, `thmTDispAxRNd` lemmas (skip-chain at all 45 prior tags + body_eval at the new tag).
  - `encodeRich (axRLf f s p) = ...` and `encodeRich (axRNd f s p a' b') = ...` clauses.
  - Estimated effort: ~600-800 LoC, mechanical mirror of existing `axRecPLf` / `axRecPNd` shape.

- **Step 7: prove `thm12_F2 (treeRec f s)`.**  Once `axRLf, axRNd` exist, the proof structure mirrors `BRA/Thm12/Parts/RecP/Construction.agda` but the leaf case is `ap1 f p` (not forced to `O`).  Cleaner than RecP because no `corOfReify` bridge / `z_corLemma` needed.

- **Cleanup (option a from the original plan):** once Step 7 lands, the legacy `axRec*`, `axRecP*` constructors can be retired and the `Th12RecCloseS*` / `Th12RecPCloseS*` families deleted (~8 files, ~6k LoC).

## Pre-existing plan (kept for reference)



## Background

This session has three durable inputs to read first, in order:

1. `BRA/ARCHITECTURE-FINDINGS.md` — the two design defects in BRA's syntax (the `parDispCongL` shape obligation and the `Rec`/`RecP` split), with the diagnosis of what mathematically went wrong, what was tried in past sessions, and what the right framing is.

2. The four feedback memories saved on 2026-05-01:
   - `feedback_no_fancy_agda.md` — proofs follow Guard's mathematics, no fancy Agda features.
   - `feedback_rec_recp_misdesign.md` — `Rec`/`RecP` as a misdesigned split of Guard's `Rfgh`.
   - `feedback_congL_encoding_depth_3.md` — the `parDispCongL` encoding shape problem (deferred).
   - `feedback_deriv_index_unification.md` — `Deriv` is naturally indexed by Formula and that's correct; case analysis on `Deriv P` is the **eliminator**; no unification should ever be needed.

3. The current state of `BRA/Thm/ThmT.agda`'s `encodeRich` — already rewritten this session with implicit `{P : Formula}` and zero dot patterns; this is the form to preserve.

## Guiding principles (read every clause carefully — these govern everything below)

1. **BRA's proofs follow the elementary mathematics of guard15.pdf.** No Agda-specific cleverness.

2. **Pattern matching on `Deriv` corresponds to applying the elimination rule.** One clause per constructor. Each clause is plain `f (constructor args) = body`, where `body` only uses what the constructor's pattern bound. The constructor identifies the case — that is the entire dispatch.

3. **Pattern-matching should never trigger Agda unification through functions.** If Agda complains about `SplitError.UnificationStuck` (or any "I'm not sure if there should be a case for ..." error involving function-valued indices like `substF x t P`), that is a sign your formalisation has drifted from the eliminator-shaped induction Guard uses. The fix is at the Agda surface (clause arrangement, explicit binding, helper structure), not at the mathematics.

4. **Forbidden Agda features in BRA proofs:** dot patterns (`.(formula)`), `with`-abstraction, irrelevance annotations, instance arguments, REWRITE pragmas, axiom K. The codebase currently has zero of these (verified at end of last session) and must continue to.

5. **`Deriv : Formula -> Set` being indexed is correct.** Do NOT propose de-indexing it. The index records the conclusion of the derivation, mirrors the mathematics, and works fine. The issue, when it arises, is that Agda's pattern-match elaboration is doing a coverage check that doesn't appear in Guard's argument — find a different Agda surface, don't alter Deriv.

## Goal of this session

Replace the misdesigned `Rec` / `RecP` split with a single unified primitive-recursion operator on binary trees, mirroring Guard's `Rfgh` (guard15.pdf p.10, axioms 9-10).

### The unified primitive

```
ap2 (operator f s) p O          = ap1 f p
ap2 (operator f s) p (Pair a b) = ap2 s (Pair p (Pair a b))
                                   (Pair (ap2 (operator f s) p a)
                                         (ap2 (operator f s) p b))
```

Constructor: `treeRec : Fun1 -> Fun2 -> Fun2`. The name is fixed (decided in the previous session — `R` conflicts with the formula variable `R` used in `(P Q R : Formula)` quantifications across `BRA/Thm/ThmT.agda`, `BRA/Deriv.agda`, `BRA/Thm/Parts/AxS.agda`; `treeRec` is unambiguous and self-documenting). Use it everywhere; do not re-litigate.

### Recovery of legacy forms

- `RecP s` in legacy code becomes the pattern synonym `treeRec Z s` (since `Z p = O` by `axZ`, the leaf cases coincide).
- `Rec O s` (the only form of legacy `Rec` actually used in BRA — see `cor = Rec O stepCor`, `thmT = Rec O stepProto`) becomes a Fun1 wrapper: `Comp2 (treeRec Z s) Z I`, which evaluates to `treeRec Z s O t` for input `t`.
- General legacy `Rec z s` for arbitrary `z : Term` is **not** recoverable (and is unused — verify this in the codebase before relying on it).

### Interderivability of axioms

The new operator's axioms `axRLf : (operator f s) p O = f p` and `axRNd : (operator f s) p (Pair a b) = ...` make `axRecPLf` and `axRecPNd` derivable as one-line lemmas (`axRecPLf s p = ruleTrans (axRLf Z s p) (axZ p)`; `axRecPNd s p a b = axRNd Z s p a b`). Two ways to handle this in `BRA/Deriv.agda`:

- (a) Replace the four `axRec*` and `axRecP*` primitive constructors entirely with `axRLf` and `axRNd`; derive the legacy ones as lemmas. **Cleanest end state**, but breaks `encodeRich`'s pattern-match clauses on `axRecPLf` / `axRecPNd` / `axRecLf` / `axRecNd` and the cascade dispatchers in `BRA/Thm/ThmT.agda`. The `encodeRich` change is direct (replace the four clauses with two for the new constructors); the cascade is more work.

- (b) Keep all four legacy axioms as primitives alongside the new two; new code uses the new ones, legacy stays. **Smaller cascade**, but slightly bloated.

Pick (a) if the cascade work is tractable; (b) is the safe fallback.

## Concrete plan

### Step 1 — Add the new operator without breaking anything

1. In `BRA/Term.agda`, add `treeRec : Fun1 -> Fun2 -> Fun2` to `data Fun2`. Keep `RecP` for now.
2. Add the pattern synonym `pattern RecP s = treeRec Z s`. Remove `RecP` from `data Fun2`.
3. Update `codeF2`, `substF2`, `KT` to handle the new constructor. **For `codeF2`**: pick whether to encode `f` in the tree (`nd tag (nd (codeF1 f) (codeF2 s))` — depth 2) or drop it (`nd tag (codeF2 s)` — depth 1, matching legacy). Depth 1 is backward-compatible with the existing cascade dispatcher; depth 2 is more honest but requires cascade work.
4. Verify `BRA/Term.agda` typechecks.

### Step 2 — Add the axioms

1. In `BRA/Deriv.agda`, add `axRLf` and `axRNd` as primitive Deriv constructors.
2. Decide (a) or (b) above. If (a), remove the four legacy axioms and add derived lemmas after the data block.
3. Verify `BRA/Deriv.agda` typechecks.

### Step 3 — Handle the cascade through `encodeRich`

This is the critical step. Adding `treeRec` to Fun2 will likely re-trigger `SplitError.UnificationStuck` in `encodeRich` (as it did twice in the previous session). **Per the principles above, this is an Agda-elaboration issue, not a mathematics issue — do not de-index Deriv or revert.**

Try, in order:

1. **Reorder clauses.** The error in past sessions was `substF x t P ≟ atomic (...)` while elaborating an early clause. Putting `ruleInst` (and `ruleIndBT` / `ruleIndBT2`) clauses **first** in `encodeRich` may let Agda discharge the function-valued index up front, before reaching concrete-index clauses. Worth trying first since cost is zero.

2. **Bind the index explicitly with `{P = ...}`** at the LHS of clauses adjacent to the failing one. This may give Agda enough information to skip the offending unification.

3. **Make `ruleInst`'s P explicit:** change `ruleInst : (x : Nat) (t : Term) {P : Formula} -> Deriv P -> Deriv (substF x t P)` to take `P` explicitly. Update all `ruleInst` call sites (small cascade — a handful of places).

4. **Last resort: write `encodeRich` via a manually-built `Deriv-elim`** that takes one continuation per constructor. Heavier but elaborates without coverage-check unification. Only do this if (1)-(3) all fail.

Verify `BRA/Thm/ThmT.agda` typechecks after each attempt; revert and try the next if not.

### Step 4 — (skipped)

`treeRec` doesn't collide with any Formula variable name in BRA, so no alpha-renames are needed.  Skip this step.

### Step 5 — Cascade through consumers

The list of files that pattern-match on `RecP` or `Rec`:
- `BRA/CodeCommutes.agda` — replace `(RecP _)` with `(treeRec _ _)` patterns
- `BRA/CorF.agda` — same
- `BRA/StepT12.agda`, `BRA/StepT12Universal.agda`
- `BRA/StepReduce.agda`
- `BRA/Sb2.agda`
- `BRA/Cor.agda` — `cor = Rec O stepCor` becomes `Comp2 (treeRec Z stepCor) Z I` (or use a new direct definition)

For each, mechanical pattern-match update.

### Step 6 — Verify the 11 already-correct Thm12 cases still typecheck

```
for f in I Z Fst Snd Pair Const IfLf TreeEq Comp Lift Post; do
  ~/.cabal/bin/agda-2.9.0 BRA/Thm12/Parts/$f.agda
done
```

These should remain unchanged. If anything breaks, the change in encoding propagated unexpectedly.

### Step 7 (optional, if time permits) — Prove `thm12_F2` for the new operator

With `Rec`/`RecP` collapsed into a single `treeRec`, the recursion in `BRA/Thm12.agda` has one fewer case. The proof for `thm12_F2 (treeRec f s)` follows the structure of the old `Rec`/`RecP` proofs (in `BRA/Th12RecCloseS*.agda` and `BRA/Th12RecPCloseS*.agda`), but should be cleaner because:
- The leaf is `f p` (a Fun1 application), not an arbitrary `z : Term`. So no `corOfReify` bridge / `z_corLemma` needed (was Task B of the original NEXT-SESSION-THM12-FAN-COMP2.md, which dissolves with this refactor).
- The Pair case is the same structure as RecP, encoded the same way.

If this step gets done, the entire `Th12RecCloseS*` and `Th12RecPCloseS*` families (8 files) become deletable, and `BRA/Thm12.agda` loses its `D_Rec_NN_fun` / `D_correct_Rec_NN_pt` / `z_corLemma_for` / `D_RecP_NN_fun` / `D_correct2_RecP_NN_pt` / `D_correct_Rec_univ` / `D_correct2_RecP_univ` parameters.

If this step doesn't get done, document the proof skeleton for the next session.

## Out of scope for this session

- The `parDispCongL` re-encoding (Comp2 / Fan shape obligation). Defer until the unified-operator refactor lands; touching the cascade dispatcher twice would be wasteful. See `feedback_congL_encoding_depth_3.md`.

## Verification checklist before declaring done

- [ ] `BRA/Term.agda` typechecks with the new operator.
- [ ] `BRA/Deriv.agda` typechecks with the new axioms.
- [ ] `BRA/Thm/ThmT.agda` typechecks (includes `encodeRich` with the new constructor handled).
- [ ] All listed consumer files typecheck.
- [ ] All 11 `BRA/Thm12/Parts/*.agda` files (I, Z, Fst, Snd, Pair, Const, IfLf, TreeEq, Comp, Lift, Post) typecheck unchanged.
- [ ] No new dot patterns, `with` abstractions, or other forbidden Agda features anywhere.
- [ ] If Step 7 is done: `thm12_F2 (treeRec f s)` typechecks and the Th12RecCloseS* files are deleted.

## Reminders

- **Do not de-index `Deriv`.** The index is correct.
- **Do not propose dropping `--exact-split` or other strictness.** It isn't the cause.
- **Do not replace pattern matching with `with` or `Deriv-elim`** unless Steps 3.1–3.3 have all failed.
- **Treat `SplitError.UnificationStuck` as "Agda's elaboration chose the wrong strategy, redirect it"**, never as "the formalisation is wrong".
- One clause per Deriv constructor, plain pattern. The constructor identifies the case. That's the entire dispatch principle.

## Starting commands

```bash
cd /Users/coquand/CHWISTEK

# Verify the build is clean before changes:
~/.cabal/bin/agda-2.9.0 BRA/Thm/ThmT.agda    # ~30s warm, ~3min cold
~/.cabal/bin/agda-2.9.0 BRA/Thm12.agda
for f in I Z Fst Snd Pair Const IfLf TreeEq Comp Lift Post; do
  ~/.cabal/bin/agda-2.9.0 BRA/Thm12/Parts/$f.agda
done

# Quick guards for principle compliance:
grep -rln '\.(' BRA/*.agda BRA/Thm/*.agda BRA/Thm12/*.agda 2>/dev/null  # should match nothing
grep -rln 'with ' BRA/*.agda BRA/Thm/*.agda 2>/dev/null | head           # double-check no `with`
grep -rn 'rewrite\|REWRITE\|instance' BRA/*.agda 2>/dev/null | head      # forbidden features
```

