# Next session — finish Theorem 12 properly

## Hard constraints (read first; do not weaken)

1. **Theorem 12 must be derivable for ALL of Fun1 / Fun2 syntax — no restrictions.**
   - Not "for closed (z, s)".
   - Not "for z = reify t".
   - Not "for what Goedel II needs".
   - Goedel II uses thm12 universally; it cannot be specialised.
   - Concretely: `thm12_F1 (Rec z s)` must work for arbitrary `z : Term` (including `var k`) and arbitrary `s : Fun2`.

2. **No shape Sigma-witnesses anywhere.** The earlier Phase 8a/8b shape lemmas (`BRA/Thm12/ShapeF1Fst.agda`, `ShapeF1Snd.agda`, `ShapeF2IfLf.agda`, `ShapeF2TreeEq.agda`, `ShapeAdapters.agda`) and the `Df_shape` / `D2g_shape` parameters of `BRA.Thm12.FromBridges` were rejected. Delete them.

3. **No `closed` field on result records.** It was bookkeeping for an avoidable universal→per-x adapter.

4. **No `z_corLemma`, `z_closed`, `s_closed` parameters.** They artificially restrict the Rec / RecP cases to closed-Tree z.

5. **Files small (≤ 250 LoC where possible) and fast (each ≤ 1 s typecheck).** Long monolithic let-bodies forbidden — split into named lemmas with abstract signatures.

## What is already correct (11 of 15 cases)

These need no changes; the recursion's clauses are literal one-liners pointing at existing artifacts.

### Atomic (8 cases)
```agda
thm12_F1 I    = mkR1 D_I    D_correct_I       -- BRA/Thm12/Parts/I.agda
thm12_F1 Z    = mkR1 D_Z    D_correct_Z       -- Parts/Z.agda
thm12_F1 Fst  = mkR1 D_Fst  D_correct_Fst     -- Parts/Fst.agda
thm12_F1 Snd  = mkR1 D_Snd  D_correct_Snd     -- Parts/Snd.agda
thm12_F2 Pair  = mkR2 D2_Pair  D_correct2_Pair    -- Parts/Pair.agda
thm12_F2 Const = mkR2 D2_Const D_correct2_Const   -- Parts/Const.agda
thm12_F2 IfLf   = mkR2 D_IfLf   D_correct2_IfLf_univ      -- Parts/IfLf.agda:957
thm12_F2 TreeEq = mkR2 (Construction.D_TreeEq …) D_correct2_TreeEq_univ
                   -- Parts/TreeEq.agda:586  Construction module
```
All produce per-x / per-(x,v) Deriv directly. No closure, no shape, no parametric suppliers.

### Composite without shape (3 cases)
```agda
thm12_F1 (Comp f g)    = -- BRA.Thm12.Parts.Comp.CompCase  with sub-IHs only
thm12_F2 (Lift f)      = -- BRA.Thm12.Parts.Lift.LiftCase  with sub-IH only
thm12_F2 (Post f h)    = -- BRA.Thm12.Parts.Post.PostCase  with sub-IHs only
```
Each takes per-x IHs from `thm12_F1` / `thm12_F2` recursive calls and produces per-x output directly. No shape parameters in their signatures (verified by inspection).

## What needs correction (4 cases)

### Comp2 and Fan: shape Sigma-witnesses must be eliminated

**Current state.** `BRA/Thm12/Parts/Comp2.agda` and `BRA/Thm12/Parts/Fan.agda` demand `Df'_shape`, `Dg_shape`, `D2_h1_shape`, `D2_h2_shape` arguments — Sigma-witnesses that `Fst (Df' x) = ap2 Pair x' y'` for arbitrary `x`. These exist only because `parDispCongL` / `parDispCongR` (from `BRA/Thm12/Param/CongL.agda` and `Param/CongR.agda`) feed them into `thmTDistrib_param`.

**What's wrong.** The shape Sigma-witness for `Fst (Df' x) = Pair _ _` is unprovable for arbitrary `x` without ruleIndBT-based shape lemmas (Phase 8b's ~600 LoC of artificial work, rejected). The shape obligation is artificial: at the call site, the IH `D_correct_f' : (x : Term) -> eqn (thmT (Df' x)) (Pair u1 u2)` already gives the Pair-decomposition of `thmT (Df' x)`, with `u1`, `u2` syntactically Pair-shaped (parEnc-form Terms). The Comp2 / Fan cases construct exactly these `u1, u2` themselves to feed `parDispCongL` / `parDispCongR`. The Sigma-witness is bookkeeping leakage.

**Correction strategy (TASK A — first work in the session).**

Two viable forms; the session should pick one or both.

**Form A1 — generic refactor of CongL / CongR.**
Rewrite `parDispCongL` to take `(u1, u2 : Term)` plus `d_h : Deriv (eqn (ap1 thmT y_h_T) (ap2 Pair u1 u2))` directly:
```agda
parDispCongL : (g : Fun2) (y_h_T xT u1 u2 : Term) ->
  Deriv (atomic (eqn (ap1 thmT y_h_T) (ap2 Pair u1 u2))) ->
  Deriv (atomic (eqn (ap1 thmT (parEncCongL g y_h_T xT))
                     (parOutCongL g xT u1 u2)))
```
Inside, `cong1 Fst` of the IH plus `axFst u1 (the rest)` gives `Fst (ap1 thmT y_h_T) = u1`. If `thmTDistrib_param` actually needs `Fst y_h_T` (not `Fst (thmT y_h_T)`) Pair-shaped, the right move is to **change `thmTDistrib_param` itself** to consume `eqn (thmT y_h_T) (Pair u1 u2)` and bypass `stepProto_else`'s `Fst y_h_T = Pair _ _` requirement. (Read `BRA/Thm/ThmT.agda:10101` `thmTDistrib_param` and `BRA/Thm/ThmT.agda:1850` `stepProto_else` carefully — verify whether `Fst y_h_T` Pair-shape is essential or can be replaced by `Fst (thmT y_h_T) = u1` plus axFst.)

Same for `parDispCongR` symmetrically.

**Form A2 — sb / sb2-based proof for Fan.**
Encode the Fan computation rule `(Fan h1 h2 h)(x, v) = h(h1 x v, h2 x v)` via `parDispAxFan h1 h2 h (cor x)(cor v)`, giving an encoded equation whose RHS is `mkAp2T cF2_h (mkAp2T cF2_h1 (cor x)(cor v)) (mkAp2T cF2_h2 (cor x)(cor v))`. Then use `sb` (or `sb2` for double substitution; see `BRA/Sb2.agda`) plus the IHs on h1, h2 to substitute the `mkAp2T cF2_h1 (cor x)(cor v) → cor (h1 x v)` and `mkAp2T cF2_h2 (cor x)(cor v) → cor (h2 x v)` slots. Then apply the IH on h at `(h1 x v, h2 x v)`. Then `axFan` + `cong1 cor` to bridge to `ap1 cor (ap2 (Fan h1 h2 h) x v)`. No CongL / CongR / shape needed.

This is the user's preferred clean form for Fan. Comp2 follows the analogous sb-based pattern with `mkAp1T` slots and IHs on f', g, h.

### Rec and RecP: static `reify (code z)` vs runtime `ap1 cor z`

**Note on the asymmetry with TreeEq.** TreeEq's `Construction` module (`Parts/TreeEq.agda:586`) ALSO takes closure parameters internally — `D_TreeEq_NN_closed` etc. — but `BRA/Th12TreeEqClose.agda` pins them to refl by choosing a specific closed `D_TreeEq_NN_fun`. The same trick works for Rec / RecP's INTERNAL NN_fun closure (Th12RecCloseSNNFun.D_Rec_NN_fun_chain is closed by construction). The genuine problem for Rec / RecP is NOT internal-NN closure but the **user-facing** `(z, s)` parameters and the resulting `z_corLemma`, `z_closed`, `s_closed` requirements — none of which has a TreeEq analog because TreeEq has no user-chosen sub-Term.

**Current state.** `BRA/Th12RecCloseS.agda` defines `Th12RecCloseS_Case` taking 8 module parameters including `(z_corLemma : Deriv (eqn (ap1 cor z) (reify (code z))))`. This holds only when `z` is a closed Tree (via `corOfReify`) — fails for `z = var k`.

**What's wrong.** `parDispAxRecLf zT sT` (used inside) gives `thmT(parEncAxRecLf zT sT) = parOutAxRecLf zT sT` with `zT = reify (code z)` on its RHS slot. The target `codeFTeq1Asym (Rec z s) O` has `ap1 cor (ap1 (Rec z s) O) = ap1 cor z` on its RHS (after `cong cor + axRecLf z s`). The bridge `zT → ap1 cor z` requires `corOfReify`, which only fires for Tree-shaped z. Restricting to Tree-shaped z is forbidden (HARD CONSTRAINT 1 above).

**Correction strategy (TASK B — second work).**

Only after Comp2 / Fan are clean (Task A landed) does this become tractable. Two candidate mechanisms; the session should examine `BRA/Thm/ThmT.agda` (specifically `body_axRecLf` and surrounding cascade in the abstract block) and pick:

1. **ruleInst-based.** Derive the encoded lf-axiom for `Rec (var n) s` (where `var n` is a fresh variable). Then `ruleInst n z` substitutes the var with the actual `z`. The substituted form's RHS slot should be `subst n z (zT_for_var n)` — and we need this to land on `ap1 cor z` rather than `reify (code z)`. Verify whether ruleInst's substitution into `reify (code (var n))` gives what we want.

2. **Runtime construction via `Comp cor (KT z)`.** Replace the `KT (parEncAxRecLf zT sT)` constant proof code inside `D_Rec_zs` with a Fun1 that builds the proof code at runtime using `Comp cor (KT z)` (= a Fun1 whose application yields `ap1 cor z`) for the RHS slot. The thmT dispatch via `body_axRecLf` then needs to propagate the RHS slot opaquely. **Read `body_axRecLf` to confirm whether it propagates the RHS opaquely or re-encodes via `reify (code _)`.** If the latter, `body_axRecLf` itself needs revision in the abstract block.

The session should NOT commit to one approach without first reading `body_axRecLf` and confirming the actual obstruction. Speculation about `reify (code z)` vs `ap1 cor z` is cheap; the truth lies in `body_axRecLf`'s definition.

**RecP follows the same template** — its `axRecPLf s p` axiom and the corresponding `parDispAxRecPLf` have analogous structure.

## Concrete deliverables for the session

### Step 1 — verify Fan and Comp2 fix (Task A)

1. Modify `BRA/Thm/ThmT.agda` `thmTDistrib_param` (line 10101) and / or `stepProto_else` (line 1850) so the Pair-shape obligation on `Fst y_h_T` is eliminated — replaced by `eqn (thmT y_h_T) (Pair u1 u2)` consumption.
2. Modify `BRA/Thm12/Param/CongL.agda` and `Param/CongR.agda` accordingly: drop the Sigma-witness, take `(u1, u2)` directly + the IH-form Deriv.
3. Update `BRA/Thm12/Parts/Comp2.agda` `Comp2Case` to drop `Df'_shape` / `Dg_shape` parameters; pass `u1, u2` from the parEnc-forms it already constructs.
4. Update `BRA/Thm12/Parts/Fan.agda` `FanCase` similarly. (Or rewrite via sb / sb2 per Form A2 — that's a separate, larger PR.)
5. Verify all of `BRA/Thm12/Parts/*.agda` typecheck.
6. **MANDATORY — present the new `FanCase` (and `Comp2Case`) proofs in the session's reply.**  Show the full statement (signature with NO shape parameters, NO closure parameters), then walk through the proof body line by line, identifying which `parDispAxFan` / IH on h1 / IH on h2 / IH on h step each piece corresponds to, plus the final `axFan + cong cor` bridge.  The user must be able to read the proof and confirm cleanness without re-typechecking.  If the proof exceeds ~80 LoC for FanCase, split into named sub-lemmas (one per Cong / sb / IH step) so each fits in a screen.

### Step 2 — analyse Rec / RecP (Task B)

1. Read `BRA/Thm/ThmT.agda` `body_axRecLf` (search for it). Document exactly how it handles its zT-slot (extracted from input, propagated to output, or re-encoded?).
2. Document exactly which obstruction blocks unrestricted `thm12_F1 (Rec z s)`.
3. Propose ONE concrete fix backed by the body_axRecLf reading. Implement it as `BRA/Th12RecOpen.agda` (or similar) — a replacement for `BRA/Th12RecCloseS.agda` that takes NO `z_corLemma` / `z_closed` / `s_closed` parameters and works for any (z, s).
4. Same for RecP.
5. Verify the recursion's `thm12_F1 (Rec z s)` and `thm12_F2 (RecP s)` clauses are bare one-liners over the new modules.

### Step 3 — assemble final `BRA/Thm12.agda`

1. Drop the `FromBridges` parametric module entirely (its design is wrong).
2. Use plain mutual recursion `thm12_F1 / thm12_F2` over Fun1 / Fun2 syntax with one-line clauses.
3. Result records have ONLY `Df` and `proof : (x : Term) -> Deriv (per-x form)` — no `closed` field, no `shape` field.
4. Verify `thm12_F1 (Rec (var 0) s) : Deriv (P_Th12_F1 (Rec (var 0) s))` typechecks for some sample `s` — concrete evidence that the unrestricted theorem holds.

## Files to delete after the session

```
BRA/Thm12/ShapeF1Fst.agda
BRA/Thm12/ShapeF1Snd.agda
BRA/Thm12/ShapeF2IfLf.agda
BRA/Thm12/ShapeF2TreeEq.agda
BRA/Thm12/ShapeAdapters.agda
BRA/Thm12/Shapes.agda  (or pieces of it; check what's still referenced)
```

(`BRA/Th12RecCloseS*.agda`, `BRA/Th12RecPCloseS*.agda` may also be deletable depending on Task B's outcome. Decide at the end.)

## Memory pointers

- `feedback_thm12_no_restrictions.md` — universal Thm12, no restrictions. Read first.
- `project_thm12_13of15_ready.md` — current inventory of correct vs wrong cases.
- `feedback_thm12_must_be_schematic.md` — earlier guidance on schematic Df.
- `feedback_one_lemma_per_paper_step.md` — small named lemmas, not monolithic let-bodies.
- `feedback_guard_fast_typecheck.md` — 250 LoC, < 1 s typecheck per file, mandatory.

## Starting commands

```bash
cd /Users/coquand/CHWISTEK

# Verify the 11 correct cases still typecheck:
agda BRA/Thm12/Parts/I.agda
agda BRA/Thm12/Parts/Z.agda
agda BRA/Thm12/Parts/Fst.agda
agda BRA/Thm12/Parts/Snd.agda
agda BRA/Thm12/Parts/Pair.agda
agda BRA/Thm12/Parts/Const.agda
agda BRA/Thm12/Parts/IfLf.agda
agda BRA/Thm12/Parts/TreeEq.agda
agda BRA/Thm12/Parts/Comp.agda
agda BRA/Thm12/Parts/Lift.agda
agda BRA/Thm12/Parts/Post.agda

# Read the obstruction site for Comp2/Fan:
grep -n "thmTDistrib_param\|stepProto_else" BRA/Thm/ThmT.agda | head

# Read body_axRecLf for Rec analysis:
grep -n "body_axRecLf\b" BRA/Thm/ThmT.agda
```

Begin with Step 1 (Comp2 / Fan).  Do not touch Rec / RecP until Step 1 is landed.
