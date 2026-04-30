# Next session: Theorem 12 TreeEq case + full Thm12 composition

## Mission

1. **Finish Theorem 12 for TreeEq.**  This is the last of the 15 primitive
   functors.  After this, all per-primitive schematic Theorem 12 results
   are in place.

2. **Compose full Theorem 12** in `BRA/Thm12.agda` (the Phase 7 glue).
   `Thm12.agda` already has `FromBridges` parametric on the 3 NN cases
   (Rec, RecP, TreeEq) and a few Phase-7-layer pieces.  With Rec and
   RecP universal closures DONE (commits `0ee1cbc`, `661214d`), only
   TreeEq + Phase 7 plumbing remains.

## Status going in

**All 14 of 15 primitive functors PROVED with schematic Theorem 12:**

| Primitive | File | Status |
|---|---|---|
| I, Z, Fst, Snd, Const, Pair, IfLf | `BRA/Th12{I,Z,Fst,Snd,Const,Pair,IfLf}.agda` | atomic; concrete |
| Comp, Comp2, Lift, Post, Fan | `BRA/Th12{Comp,Comp2,Lift,Post,Fan}.agda` | composer; parametric on prior Th12 |
| **Rec** (Fun1) | `BRA/Th12RecUniv.agda:1899` | **`Th12_F1_Rec_zs_concrete` UNCONDITIONAL** (commit `0ee1cbc`) |
| **RecP** (Fun2) | `BRA/Th12RecPUniv.agda:1464` | **`Th12_F2_RecP_s_concrete` UNCONDITIONAL** (commit `661214d`) |
| **TreeEq** (Fun2) | `BRA/Th12TreeEq.agda:252` | **PARAMETRIC on (Pair, Pair) case**.  3 of 4 shape cases (LL, LN, NL) concrete; NN deferred. |

`BRA/Thm12.agda` (Phase 7a glue) exists with `FromBridges` parametric on
3 NN cases + Phase-7 plumbing.  See its 251 LoC for the structure.

## TreeEq: the gap

### What's done (Th12TreeEq.agda:252)

3 non-recursive shape cases (LL, LN, NL) are fully proved using
`thmTDispAxTreeEq*_param` dispatchers:
- `Th12_F2_TreeEq_at_LL`
- `Th12_F2_TreeEq_at_LN`
- `Th12_F2_TreeEq_at_NL`

### What's NOT done

The (Pair, Pair) case (axTreeEqNN).  Specifically:

```
axTreeEqNN : Deriv (eqn (ap2 TreeEq (Pair a1 a2)(Pair b1 b2))
                         (ap2 IfLf (ap2 TreeEq a1 b1)
                                   (Pair (ap2 TreeEq a2 b2) (Pair O O))))
```

The recursion is **diagonal**: result depends on `TreeEq a1 b1` and
`TreeEq a2 b2`, NOT all 4 corners.  This is the core difficulty.

### The structural obstruction (READ BEFORE CODING)

`BRA/RuleIndBT2.agda` documents the situation clearly:
- Standard 4-IH `ruleIndBT2` (IHs at all 4 corners (v1,w1), (v1,w2),
  (v2,w1), (v2,w2)) IS derivable from nested `ruleIndBT`.
- "Diagonal" form (IHs ONLY at (v1,w1) and (v2,w2)) is NOT derivable
  in BRA's substitution language.

Three documented options (from `BRA/RuleIndBT2.agda` header):
- **(a)** Add `ruleIndBT2` as new `Deriv` primitive (~430 LoC).
- **(b)** Reformulate TreeEq's recursion to fit the all-4-IH form.
- **(c)** Use BRA-level `TreeEq` combinator at the Df-construction
  level so BRA's recursion supplies the 2 cross-IHs automatically.

**Pattern (c) is what Rec/RecP use** — `axRecNd` / `axRecPNd` provide
the IHs structurally via the recursion functor.  **STRONGLY PREFER
PATTERN (c).**  Adding a Deriv primitive is a last resort.

### The IfLf-form trick from RecP — REUSABLE

For RecP, the breakthrough was: `step_inner` can't emit `ap2 Df_F2_RecP_s
p v_i` directly (self-reference), but CAN emit the BRA-equivalent
IfLf-form via `Fan` composition.  See `project_th12_recp_basepair_done.md`
in auto-memory.

For TreeEq, the analog should be: `step_inner_for_TreeEq` can't directly
reference `Df_F2_TreeEq` but CAN emit a BRA-equivalent expanded form
where the inner recursion uses the BRA-level TreeEq itself (and the
chain Df references this via TreeEq's recursive output).

**Concretely, design Df_F2_TreeEq as something like:**

```
Df_F2_TreeEq = Fan (Lift (KT tagCode_ruleTrans))
                   inner_dispatch_TreeEq
                   Pair
```

where `inner_dispatch_TreeEq` either:
- Uses `IfLf` for shape dispatch (LL, LN, NL, NN) wrapping a `TreeEq
  step_inner_TreeEq`-style functor for the recursive part; OR
- Uses a 2D version of the same pattern.

The exact construction needs careful design — TreeEq's natural recursion
isn't directly via `Rec` or `RecP` (BRA's `TreeEq` is a Fun2 with
4 axTreeEq* axioms, not a generic recursion functor).  May need to
build the recursion via `RecP` over a paired argument, or via
`Comp2`/`Lift` composition.

## Recommended phasing

### Phase A (~2-3 hours): Design Df_F2_TreeEq

Goal: produce a closed `Df_F2_TreeEq : Fun2` whose runtime behavior:
- At `(O, O)`: emits the LL payload.
- At `(O, Pair w1 w2)`: emits the LN payload.
- At `(Pair v1 v2, O)`: emits the NL payload.
- At `(Pair v1 v2, Pair w1 w2)`: emits the NN chain content with IH.Df
  slots in some BRA-equivalent form that step_inner-style emitters can
  produce.

**Design notes:**
- The LL/LN/NL cases are like Rec's lf-case: handled by the outer IfLf
  dispatch.
- The NN case needs to invoke TreeEq's recursion structurally so the IHs
  at `(a1, b1)` and `(a2, b2)` are supplied automatically — the analog
  of axRecPNd providing IHs.
- The IfLf-form trick from RecP applies: IH.Df slots use the BRA-equivalent
  expanded form, not direct reference to Df_F2_TreeEq.

### Phase B (~3-4 hours): Prove Th12_F2_TreeEq schematic

`P_Th12_TreeEq : Formula`, `Th12_F2_TreeEq : Deriv P_Th12_TreeEq`.  Apply
`ruleIndBT` (NOT `ruleIndBT2`) on var 0 (= one of the recursion args)
with the inner recursion handled by Df_F2_TreeEq's structural
recursion.

This is the analog of `BRA/Th12RecPUniv.agda` — likely ~1000-1500 LoC
total because TreeEq is binary-recursive AND has 4 shape cases (vs
RecP's 2).

If `ruleIndBT` doesn't suffice and `ruleIndBT2` is genuinely needed:
fall back to option (a) from `BRA/RuleIndBT2.agda`.  Time-box ruleIndBT
attempts to ~2 hours before falling back.

### Phase C (~1-2 hours): Discharge Thm12.FromBridges

`BRA/Thm12.agda`'s `FromBridges` module takes the 3 NN cases + Phase-7
plumbing as parameters.  With Rec, RecP, TreeEq universal closures
done, instantiate the parameters.

The Phase-7 plumbing (z_corLemma supplier, Fst-shape proofs for
Comp2/Fan, universal Rec/RecP correctness) should be derivable from
the existing Th12RecUniv / Th12RecPUniv / Th12TreeEq deliverables —
but may have NN/shape mismatches that need bridges.  Allow 1-2 hours
for these.

### Phase D (~1 hour): Verify + commit

Concrete instantiation of `D : Fun1 -> Fun1`, `D2 : Fun2 -> Fun2`
producing schematic Theorem 12 for ANY closed Fun1/Fun2.  This unblocks
Theorem 14 (Goedel II).

## Files to consult before starting

1. **`BRA/NEXT-SESSION-TREEEQ-THM12.md`** (this file).
2. **`BRA/Th12RecPUniv.agda`** — the closest template (binary recursive,
   IfLf-form trick).  Especially:
   - Lines 240-241: `step_inner` with chain content emitters.
   - Lines 463-495: `wrapped_IfLf_form` + `Df_F2_RecP_s_eqv_IfLf_form` bridge.
   - Lines 497-1027: `emit_*_red` reduction lemmas + `Df_chain12_at` +
     `Df_F2_RecP_s_at_Pair_chain_proven`.
   - Lines 1418-1465: BasePair sub-module + basePair_param.
3. **`BRA/Th12RecP.agda`** — `RecPPairCase_doublelifted` for the
   doubly-lifted Sigma pattern.
4. **`BRA/Th12TreeEq.agda`** — current state; LL/LN/NL cases done.
5. **`BRA/RuleIndBT2.agda`** — the obstruction analysis; pattern (c)
   recommendation.
6. **`BRA/Thm12.agda`** — Phase 7a glue with FromBridges.
7. **`BRA/Thm12/Parts/TreeEq.agda`** — existing partial.
8. **`BRA/NEXT-SESSION-RECP-TREEEQ.md`** — original planning doc;
   Phase 4 has TreeEq design (sequential sbt2 trick mentioned, may not
   be needed if pattern (c) works).
9. **`guard15.pdf`** pages 12-17 — original Theorem 12/14 statements.
10. **`ndw2.pdf`** — re-read in case there's a trick.

## Memory records to read

- **`project_th12_rec_basepair_done.md`** — Rec resolution (template).
- **`project_th12_recp_basepair_done.md`** — RecP resolution; the
  IfLf-form trick fully explained.  **Read in detail.**
- `project_thm12_phase7a_done.md` — Phase 7a glue inventory.
- `feedback_treeeq_needs_indBT2.md` — older claim that ruleIndBT2 is
  needed; may be superseded by pattern (c).  **Reverify.**
- `feedback_recpair_godel2_inherent.md` — [SUPERSEDED] the "inherent
  hard step" framing; resolved by IfLf-form trick.
- `feedback_guard_fast_typecheck.md` — typecheck-time discipline.
- `feedback_one_lemma_per_paper_step.md` — break large constructions
  into named lemmas.
- `feedback_thm12_must_be_schematic.md` — Theorem 12 contract shape.
- `feedback_no_new_deriv_axioms.md` — strong preference against new
  Deriv primitives.

## Constraints (project conventions)

- Files ≤ ~250 LoC where feasible (Th12RecPUniv at 1470 is over budget;
  acceptable for the recursive cases, but new files should respect this).
- Typecheck < 2s per file.  Th12RecPUniv typechecks in 0.48s — set
  this as a target for Th12TreeEq.
- No postulates, no holes.  `--safe --without-K --exact-split`.
- ASCII-only; no Unicode mixfix.  Named operators (`Eq.trans`, etc.).
- **Strongly prefer pattern (c)** over adding `Deriv` primitives.  Per
  `feedback_no_new_deriv_axioms.md`: "Don't add Deriv constructors for
  things Rose/Ryan derive; use Schema F instead."
- Verify each phase typechecks before adding the next.

## Definition of done (best case)

- **TreeEq fully proved:** `Th12_F2_TreeEq_concrete : Deriv P_Th12_TreeEq`
  parametric only on legitimate IHs (the closure assumption + Theorem 12
  for sub-functors used in Df construction).
- **Thm12.FromBridges fully discharged:** all 3 NN parameters + Phase-7
  plumbing instantiated.  `BRA/Thm12.agda` produces concrete
  `D : Fun1 -> Fun1` and `D_correct : (f : Fun1) -> Deriv P_Th12_F1_f`
  for ANY closed `f`.

## Definition of done (realistic)

- **TreeEq fully proved.**  This alone is a substantial session
  (~1-2 days of work in worst case if pattern (c) hits snags).
- **Thm12 composition deferred** to a follow-up session.

## Specifically AVOID

- **Don't add `ruleIndBT2` as a Deriv primitive without exhausting
  pattern (c) first.**  The Rec/RecP precedent strongly suggests
  pattern (c) works for TreeEq too.  If you find yourself reaching
  for the primitive after < 2 hours of pattern (c) attempts, STOP and
  reread `BRA/RuleIndBT2.agda` + `feedback_no_new_deriv_axioms.md`.
- **Don't over-claim "TreeEq proved" if the (Pair, Pair) case has
  parametric assumptions beyond the legitimate IHs.**  See
  `feedback_verify_not_assumed.md`, `feedback_honest_naming.md`,
  `feedback_verify_dont_trust_comments.md`.
- **Don't skip the Plan B trick search.**  ndw2.pdf gave the Carneiro
  insight; `feedback_variant_deduction_theorem.md` may apply.  ~30 min
  trick search before committing to heavy engineering.
- **Don't commit incremental progress that breaks the build.**  Each
  commit should typecheck cleanly.
- **Don't expect TreeEq to be small.**  RecP took ~1100 LoC across
  3 phases.  TreeEq has 4 shape cases (vs RecP's 2) and may need
  ~1500-2000 LoC.  Budget accordingly.

## Commit cadence

- Commit per phase (Df_F2_TreeEq design, schematic Th12 Pair-Pair case,
  full closure, Thm12 composition).
- Commit messages: descriptive, include LoC totals + typecheck times.
- Update memory records at session end:
  - `project_th12_treeeq_done.md` (or partial-done) for the TreeEq result.
  - `project_thm12_full_composition_done.md` for the Thm12 result, if reached.

## Session retrospective

Previous RecP session (commits `9510572`, `a44f5f0`, `661214d`):
- Phase 1 (72 LoC, IfLf-form bridge): 30 min.
- Phase 2 (111 LoC, real step_inner): 30 min.
- Phase 3 (580 LoC, reduction lemmas + composition): ~2 hours.
- Total ~3 hours of careful coding.  Each phase typechecked before the
  next.  No major dead-ends because of the well-understood RecP analog
  template.

For TreeEq, expect ~1.5-2x the time because:
- 4 shape cases (LL, LN, NL, NN) vs 2 (lf, Pair).
- TreeEq's "step" isn't a simple Fun2 like step_inner — needs design.
- The diagonal recursion may force creative Df construction.

Plan ~5-7 hours total.  If progress stalls past 4 hours on Phase A
(Df design), commit progress + handoff doc, restart fresh next session.
