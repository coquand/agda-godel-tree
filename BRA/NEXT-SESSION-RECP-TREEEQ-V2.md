# Next session: finish Theorem 12 for RecP, start (maybe finish) TreeEq

## Mission

1. **Finish Theorem 12 for RecP** by closing the `Df_F2_RecP_s_at_Pair_chain`
   gap in `BRA/Th12RecPUniv.agda`.  After this: `Th12_F2_RecP_s_concrete :
   Deriv P_Th12_RecP_s` will be unconditional (only `ih_s_bra` and the meta
   closure assumption remain — both legitimate).

2. **Start Theorem 12 for TreeEq.**  TreeEq is the 4-way 2D-tree-induction
   case.  Per the existing planning doc, it requires `ruleIndBT2` as a new
   Deriv primitive plus a "doubly-lifted Sigma" approach that should
   generalise from RecP.  Aim to get at least the primitive infrastructure
   in place, ideally a working schematic proof.

## Status going in (commits to inspect: 0ee1cbc, 6ca5500, f1c92b1, 8550afb)

**Rec (Fun1):** ✅ FULLY proved.  `Th12_F1_Rec_zs_concrete : Deriv
P_Th12_Rec_zs` typechecks unconditionally inside `WithClosure` (parametric
only on the legitimate `ih_s_bra` for the step `s`).
See `BRA/Th12RecUniv.agda:1899`.

**RecP (Fun2):** mostly proved.
- `BRA/Th12RecP.agda:567` — `RecPPairCase_doublelifted` module: doubly-lifted
  Pair-case Sigma, parametric in IH records.
- `BRA/Th12RecPUniv.agda:613` — `Th12_F2_RecP_s_concrete` exists inside
  `WithBasePairBridge`.
- `BRA/Th12RecPUniv.agda:367-471` — `Th12_at_lf_concrete_proven` (concrete
  lf-case proof; commit `8550afb` removed it as a parameter).
- `BRA/Th12RecPUniv.agda:140` — `step_inner = Const` (STILL A STUB).
- **The remaining gap:** `Df_F2_RecP_s_at_Pair_chain` is still a
  `WithBasePairBridge` parameter.  See "RecP: the gap" below.

**TreeEq:** untouched.

## RecP: the gap

`Df_F2_RecP_s_at_Pair_chain : (v1 v2 : Nat) -> Deriv (eqn (ap2 Df_F2_RecP_s
(var 1) (Pair (var v1) (var v2))) (BasePair.Df_chain12 v1 v2))`.

To discharge concretely, we need:
1. A real `step_inner : Fun2` (replacing `Const` stub).
2. Reduction lemmas for `step_inner`'s emit_* combinators.
3. Compose via axFan + axLift + axKT + axFan + axPost + axSnd + axLift +
   axIfLfN + axRecPNd + step_inner reduction.

### The structural tension (READ BEFORE CODING)

`Df_F2_RecP_s = Fan (Lift (KT tagCode_ruleTrans)) inner_dispatch Pair` where
`inner_dispatch` contains `IfLf` for the lf-vs-Pair dispatch.  At opaque
`var v_i` (the IH from `ruleIndBT`), `IfLf` is **stuck** — neither `axIfLfL`
nor `axIfLfN` fires.

The chain Df from `RecPPairCase_doublelifted` has IH.Df slots = `ap2
Df_F2_RecP_s p (var v_i)` (set by `toIH2RecP_doublelifted` at
`Th12RecPUniv.agda:473`).  **`step_inner` cannot emit this Term directly**
(would be self-referential through the Fun2 algebra).

### The way out (already verified mathematically)

`step_inner` CAN emit the BRA-equivalent **IfLf-form**:

```
Pair tagCode_ruleTrans (ap2 IfLf v_i (Pair (ap1 f_lf p)
                                            (ap2 (RecP step_inner) p v_i)))
```

via `Fan` composition (specifically `Fan emit_v_i emit_payload_v_i IfLf`,
using `Lift (Comp Fst Snd)` to extract `v_i` and `EmitPair (Lift (Comp f_lf
Fst)) RecsFst` for the payload).

This Term is BRA-equal to `ap2 Df_F2_RecP_s p v_i` via
**axFan + axLift + axKT + axFan + axPost + axSnd + axLift** — no axIfLf
needed.

So either:

**Plan A (heavy, mechanical):** ~370 LoC.
- Update `toIH2RecP_doublelifted` (also `toIH2RecP`, `toIH2RecP_lifted`) to
  use the IfLf-form for IH.Df, plus image bridge via `cong1 thmT
  (Df_F2_RecP_s_eqv_IfLf_form_bridge)`.  ~80 LoC.
- Define real `step_inner` emitting the chain content with IfLf-form IH.Df
  slots.  ~100 LoC of Fan/Lift/KT/Comp combinators (mirror
  `BRA/Th12RecUniv.agda:140-220` which has the analog for Rec).
- Reduction lemmas for each emit_* combinator at runtime.  ~150 LoC
  (mirror `BRA/Th12RecUniv.agda:300-400`).
- Compose into `Df_F2_RecP_s_at_Pair_chain`.  ~80 LoC.

**Plan B (search for a trick first — ~30 min time-box):** before diving
into Plan A, investigate whether ndw2.pdf or a related insight admits a
shortcut.  Examples to consider:

- *Carneiro-style at the chain Df level itself:* the chain Df is ALSO a
  syntactic Term.  Can the equality `ap2 Df_F2_RecP_s p (Pair v1 v2) =
  chain_Df` be proved without spelling out step_inner concretely?
  Probably not (it's a definitional reduction at concrete Pair input),
  but worth a 5-minute check.
- *Different IH.Df form that doesn't need IfLf-expansion:* what if
  `toIH2RecP_doublelifted` sets IH.Df = `Pair tagCode_ruleTrans (ap2
  (RecP step_inner) p (var v_i))` (the "drop the IfLf wrapper" form)?
  This would only need step_inner = `EmitPair (KT2 tagCode_ruleTrans)
  RecsFst`-style emission, NOT the IfLf-form.  But it requires bridging
  IH hypothesis (`Df_F2_RecP_s p (var v_i)`) to this form, which goes
  through IfLf at opaque var — same obstruction.  Likely dead end but
  reverify.
- *Variant deduction theorem* (see `feedback_variant_deduction_theorem.md`)
  — might let us discharge the bridge with O(formula length) steps via the
  `Th12_at_lf_substF` special-case witness, sidestepping step_inner entirely.
  This is the most likely shortcut.  Adapting to BRA's term-substitution
  setting is non-trivial but might still be cheaper than 370 LoC.

If Plan B yields nothing in 30 min, commit to Plan A.

### Pattern to mirror

`BRA/Th12RecUniv.agda` has the COMPLETE analogous construction for Rec
(commit `0ee1cbc`).  Specifically:
- Lines 145-220: Helper Fun2 combinators (emit_*) + step_inner.
- Lines 244-305: Df_F1_Rec_zs reduction lemmas.
- Lines 1098-1125: `Df_chain12_at v1 v2` Term-level chain Df.
- Lines 1620-1900: BasePair sub-module + basePair_param + Th12_F1_Rec_zs.

For RecP: the analog is binary (extra `p` arg).  Most pieces translate
directly with minor binary adjustments.  `BRA/Th12RecP.agda:567`
(`RecPPairCase_doublelifted`) gives the chain Df structure.

## TreeEq: starting point

Per `BRA/NEXT-SESSION-RECP-TREEEQ.md` (existing planning doc, sections
"Phase 3" and "Phase 4") and `feedback_treeeq_needs_indBT2.md`:

TreeEq's schematic Theorem 12 needs **`ruleIndBT2`** — 2D-tree induction
with 4 cases (`(O,O)`, `(O, Pair)`, `(Pair, O)`, `(Pair, Pair)`).
This is **not derivable from `ruleIndBT`** in BRA's substitution language;
must be added as a Deriv primitive.

### Phase 3a (definitely this session): add ruleIndBT2 primitive

1. `BRA/Deriv.agda`: add the `ruleIndBT2` constructor.  ~50 LoC.
   Signature: see `BRA/NEXT-SESSION-RECP-TREEEQ.md:96-110` for the exact
   shape (re-derive from the 2D induction principle if unclear).
2. `BRA/Thm/Tag.agda`: `tagRuleIndBT2 = suc <last tag>`.  ~5 LoC.
3. `BRA/Thm/Parts/RuleIndBT2.agda` (new): `encRuleIndBT2`, `outRuleIndBT2`.
   ~70 LoC.
4. `BRA/Thm/ThmT.agda`: extend abstract block with body_ruleIndBT2,
   checkTag_ruleIndBT2, branch_ruleIndBT2, and dispatch chain extension.
   This is the heavy bit (~150-300 LoC).  Pattern: `body_ruleInst2_eval`
   etc. at lines ~12500-12700.

After Phase 3a, the Deriv layer can talk about ruleIndBT2 even without a
TreeEq construction yet.

### Phase 3b (likely this session if 3a goes well): TreeEq schematic Th12

Mirror Rec/RecP's schematic structure:
- `Df_F2_TreeEq : Fun2` — IfLf-dispatched on var 0's shape, with sub-cases.
- `P_Th12_TreeEq : Formula` — the schematic statement.
- `Th12_F2_TreeEq : Deriv P_Th12_TreeEq` via `ruleIndBT2`.

The 4-way step body uses **sequential sbt2** (per the encoding-trick from
the existing planning doc, Phase 4) — this avoids needing `sbt4`.

The doubly-lifted construction generalises to **quadruply-lifted** for
the (Pair, Pair) case (4 IH hypotheses).  Build `B_combinatorFour`,
`liftAxiomFour`, `liftedRuleTransFour`, `liftedCong*Four` analogous to
the Two-suffix helpers in `BRA/Thm/ThmT.agda:283-330`.

The (Pair, Pair) step body needs `thmTDispCongL/CongR/RuleTrans/AxTreeEqNN
_param_quadlifted` — 4 new dispatcher variants.  Mirror the
`_doublelifted` versions in ThmT (lines 10805, 12360, 13231 + the
matching helpers).  Estimate: ~600 LoC of dispatch chain extension, but
mostly mechanical mirror of the doubly-lifted versions.

Don't expect to finish TreeEq this session.  Get the infrastructure in
place; final composition can follow.

## Files to consult before starting

1. `BRA/NEXT-SESSION-RECP-TREEEQ-V2.md` (this file).
2. `BRA/Th12RecUniv.agda` — complete reference for the Rec analog.
3. `BRA/Th12RecP.agda` — `RecPPairCase` + `RecPPairCase_doublelifted`.
4. `BRA/Th12RecPUniv.agda` — current state.
5. `BRA/NEXT-SESSION-RECP-TREEEQ.md` — original planning doc (Phase 3-4
   for ruleIndBT2 + TreeEq).
6. `ndw2.pdf` — re-read for trick inspiration (it solved the Carneiro
   insight for Rec/RecP basePair_param).
7. `guard15.pdf` pages 12-17 — original Theorem 12/14 statements.

## Memory records to read

- `project_th12_rec_basepair_done.md` — Rec resolution, the template.
- `project_th12_recp_basepair_done.md` — RecP current state, IfLf tension.
- `feedback_variant_deduction_theorem.md` — possible shortcut for the
  RecP chain bridge.  Read in detail.
- `feedback_recpair_godel2_inherent.md` — [SUPERSEDED but kept] the
  "inherent hard step" framing was correct in spirit; the Carneiro-at-
  dispatcher technique resolved it.
- `feedback_treeeq_needs_indBT2.md` — confirms ruleIndBT2 is needed as a
  primitive.
- `feedback_guard_fast_typecheck.md` — typecheck-time discipline.
- `feedback_one_lemma_per_paper_step.md` — break large constructions
  into named lemmas.
- `feedback_thm12_must_be_schematic.md` — the Theorem 12 contract shape.

## Constraints (from existing project conventions)

- Files ≤ ~250 LoC (will be exceeded for Th12RecPUniv and Th12RecP; OK
  for those, but new files should respect this).
- Typecheck < 2s per file.  ThmT.agda extensions may push it higher;
  if it crosses 15s on a single fresh edit, **stop and rethink the
  formulation** (see `feedback_guard_fast_typecheck.md`).
- No postulates, no holes.  `--safe --without-K --exact-split`.
- ASCII-only; no Unicode mixfix.  Use named operators (`Eq.trans`,
  `Nat.add`, etc.).
- Don't add `Deriv` constructors except when truly needed (i.e.,
  `ruleIndBT2`).  See `feedback_no_new_deriv_axioms.md`.
- Verify each phase typechecks before adding the next.  Fast typecheck
  is the loudest signal of mathematical correctness.

## Definition of done (best case)

After this session:
- **RecP fully proved:** `BRA/Th12RecPUniv.agda:Th12_F2_RecP_s_concrete`
  parametric only on `Df_F2_RecP_s_closed` and `ih_s_bra` (the
  legitimate IH on `s`).  `WithBasePairBridge` removed (its parameter
  discharged structurally).
- **ruleIndBT2 primitive in place:** `BRA/Deriv.agda` has the new
  constructor; `BRA/Thm/ThmT.agda` has dispatch infrastructure;
  encRuleIndBT2 / outRuleIndBT2 in `BRA/Thm/Parts/RuleIndBT2.agda`.
- **TreeEq schematic stub:** at minimum, `Df_F2_TreeEq : Fun2` and
  `P_Th12_TreeEq : Formula` defined; ideally `Th12_F2_TreeEq` proved
  parametric on the (Pair, Pair) step.  Full closure can defer.

## Definition of done (realistic if Plan A required)

- RecP fully proved.
- ruleIndBT2 primitive added (Phase 3a only).
- TreeEq deferred to a follow-up session.

## Commit cadence

- Commit per phase (RecP closure, ruleIndBT2 primitive, ThmT extensions,
  TreeEq schematic).
- Commit messages: descriptive, include LoC totals + typecheck times.
- Update `project_th12_recp_basepair_done.md` and create
  `project_th12_treeeq_started.md` (or similar) at session end.

## Specifically AVOID

- **Do not over-claim "RecP proved" if the chain Df bridge isn't actually
  discharged.**  See `feedback_verify_not_assumed.md`,
  `feedback_honest_naming.md`, `feedback_verify_dont_trust_comments.md`.
  The user will check.
- **Do not add `Deriv` axioms to bypass mechanical work.**  Only
  `ruleIndBT2` is justified as a new primitive (per the existing
  analysis); everything else should be derived.
- **Do not skip the 30-min Plan B (trick search) for RecP.**  ndw2.pdf
  + variant deduction theorem are credible shortcuts; previous sessions
  confirmed that pdf hints can dramatically simplify the engineering.
- **Do not commit incremental progress that breaks the build.**  Each
  commit should typecheck cleanly.
