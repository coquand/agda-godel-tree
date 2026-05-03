# Next session — Sound thmT, Step 1B (lifted dispatcher) and 1C (ThmT integration)

## State at handoff

Step 1A is **done** (this session). New files validated standalone:

* `BRA/SoundMpProto.agda` (0.1s solo) — `body_mp_v = Post verifierF1 Pair`
  with five Fun1 extractors (`getD1`, `getD2`, `getHead`, `getPT`,
  `getQT`) and the verifier nest
  (`outerCheckF1`, `innerCheckF1`, `innerOrFalsePairF1`, `ccF1`,
  `qfailPairF1`, `verifierF1`). All identifiers camelCase
  (mid-underscore = mixfix hole, breaks parsing).

* `BRA/SoundMpVProof.agda` (0.2s solo) — `body_mp_v_eval_pass` for the
  closed-Formula case:

  ```agda
  body_mp_v_eval_pass :
    (a bb : Term) (t1 t2 pT qT : Term) ->
    Deriv (atomic (eqn (ap1 Snd bb) (ap2 Pair t1 t2))) ->
    Deriv (atomic (eqn t1 (ap2 Pair (reify tagImp) (ap2 Pair pT qT)))) ->
    Deriv (atomic (eqn t2 pT)) ->
    Deriv (atomic (eqn (ap2 TreeEq pT pT) O)) ->     -- inner reflexivity
    Deriv (atomic (eqn (ap2 body_mp_v a bb) qT))
  ```

  The outer reflexivity `TreeEq tagImp tagImp = O` is discharged
  inline with `treeEqRed tagImp tagImp` (closed Tree, Agda reduces
  `boolCase true O falseT` to `O`). The inner reflexivity is a
  hypothesis the caller supplies — for closed `pT = reify (codeFormula P)`
  use `treeEqRed (codeFormula P)(codeFormula P)`; for parametric
  `pT` (Step 1C onward), build `treeEqRefl_param` via `ruleIndBT`.

`BRA/Thm/ThmT.agda`, `BRA/GoedelIIFull.agda`, every consumer
(`Th14Step3.agda`, `Th14Step5.agda`, `Th14Step4Final.agda`, etc.) are
**unchanged**. Baseline `GoedelIIFull` ~0.8s cached.

The architectural audit lives at `BRA/SOUND-THMT-FINDINGS.md`
(superseded for Blocker 1; Blockers 2 + 3 are this session's targets).

## Mathematical context (recap)

Guard's Theorem 14 closure runs entirely under the assumption
`PrAtX x = atomic (eqn (thmT x) cG)`. The witnesses for the new
inner-check hypothesis at the mp dispatcher
(`thmT(K_part x) = neg_P`, `thmT(g_part x) = P_enc`,
`thmT(D_thmT x) = codeFTeq1Hyp …`) are all built UNDER `PrAtX x`,
because the bridge `thmT x = cG` is exactly `axImpRefl P`. So the
dispatcher must take its hypotheses **lifted under `PrAtX x`** —
not because the math is hard, but because that's the context the
math lives in.

The fix is a reformulation of the dispatcher's TYPE, not of the
math. See `BRA/SOUND-THMT-FINDINGS.md` Blocker 2 and
`memory/project_sound_thmt_lifted_dispatcher.md`.

## Tasks (target order)

### Step 1B — `thmTDispMp_param_l` (lifted dispatcher)

Add to `BRA/Thm/ThmT.agda` (after the existing `thmTDispMp_param`,
which stays for closed-Tree call sites):

```agda
thmTDispMp_param_l :
  (P : Formula)
  (y1T y2T : Term) (y1' x' : Term) (pT qT : Term) ->
  Deriv (P imp atomic (eqn (ap1 Fst y1T) (ap2 Pair x' y1'))) ->
  Deriv (P imp atomic (eqn (ap1 thmT y1T)
                            (ap2 Pair (reify tagImp) (ap2 Pair pT qT)))) ->
  Deriv (P imp atomic (eqn (ap1 thmT y2T) pT)) ->
  Deriv (P imp atomic (eqn (ap1 thmT (ap2 Pair tagCode_mp (ap2 Pair y1T y2T))) qT))
```

Build it from `thmTDispMp_param` by lifting the structural reductions
(every closed step is `liftAxiom P …`) and chaining via the
`liftedRuleTrans` / `liftedCong*` helpers in
`BRA/Thm/EvalHelpers.agda`. The unlifted dispatcher remains the
ground truth; the lifted variant is just a wrapper.

**Caveat for Step 1B alone**: this version still uses the old
`body_mp` (which always succeeds without verification). It is sound
only because the consumers happen to pass correct witnesses. Step 1C
swaps in `body_mp_v` and makes the verification load-bearing.

Smoke test: `Th14Step3.agda` and `Th14Step5.agda` rewritten to use
the lifted variant should typecheck unchanged in result, and
`GoedelIIFull.agda` should still produce `godelII : Deriv Con -> Deriv bot`.

### Step 1C — `treeEqRefl_param` + swap `body_mp_v` into ThmT

1. New file `BRA/TreeEqReflParam.agda` (~120 LoC):
   ```agda
   treeEqRefl_param : (t : Term) ->
     Deriv (atomic (eqn (ap2 TreeEq t t) O))
   ```
   By `ruleIndBT` on the motive `atomic (eqn (ap2 TreeEq (var 0) (var 0)) O)`:
   * Base (`var 0 := O`): `axTreeEqLL`.
   * Step (Pair `v1 v2`): build `(P[0:=v1] imp P[0:=v2] imp P[0:=Pair v1 v2])`.
     The conclusion reduces via `axTreeEqNN v1 v2 v1 v2` to
     `IfLf (TreeEq v1 v1)(Pair (TreeEq v2 v2)(Pair O O))`. Substitute
     IH1 (`TreeEq v1 v1 = O`) → `IfLf O (Pair (TreeEq v2 v2)(Pair O O))`,
     reduce via `axIfLfL` to `TreeEq v2 v2`, substitute IH2 → `O`.
     Build the implication via `axS + axK + mp`. See
     `BRA/Th12RecUniv.agda` lines 1295–1315 for the `liftAxiom` and
     `B_combinator` template. Estimate ~80–100 LoC of Carneiro-style
     wrapping.
   * Then `ruleInst zero t` to specialize to arbitrary `t`.

2. In `BRA/Thm/ThmT.agda` abstract block:
   * Replace `body_mp` with `body_mp_v` (just rename; `body_mp_v` has
     the same `Fun2` type, so all `skipAtTag` references in non-mp
     dispatchers are unaffected — they just thread the value past).
   * Replace `body_mp_eval` and `body_mp_eval_param` with the
     verifying versions, importing `body_mp_v_eval_pass` from
     `SoundMpVProof`. The signatures gain a 3rd hypothesis
     (the inner-check Deriv) and a 4th (the inner reflexivity Deriv,
     supplied by the caller — usually `treeEqRefl_param pT`).
   * Update `body_mp_eval_proj` similarly (it can drop the d1
     hypothesis but still needs the inner check + reflexivity).
   * Update `thmTDispMp_param` (and its lifted variant from Step 1B)
     to take + thread the new hypotheses.

3. Same for `body_ruleInst`. Per
   `BRA/SOUND-THMT-FINDINGS.md` Blocker 1 follow-up, the verifying
   `body_ruleInst_v` should check that `thmT y_h` is at least
   `Pair _ _`-shaped (i.e., not `O`); on pass run the existing `subT`
   pipeline; on fail output `codeTriv`. Mirror SoundMpProto/SoundMpVProof
   pattern in new files `BRA/SoundRuleInstProto.agda` /
   `BRA/SoundRuleInstVProof.agda` first to validate, then integrate.

### Step 1D — Rewrite `Th14Step3.agda` and `Th14Step5.agda`

Use the lifted dispatcher throughout. Pass `step1_l` / `step2_l` /
`step3_l` / `K_part_l` directly as inner-check witnesses. Remove the
trailing `liftAxiom (PrAtX x)` at `step3_l` / `step5_l`'s tail.

Inner-check witness map (already constructed in current code):

| Call site | Inner-check witness |
|--|--|
| `Th14Step3.agda:577` (inner mp at f_part / D_thmT) | `step1_l x` |
| `Th14Step3.agda:625` (outer mp at .../D_sub_at_ii) | `step2_l x` (or `liftAxiom P (thm13_F2 …)`) |
| `Th14Step5.agda:260` (inner mp at h_part_skel / g_part) | `step3_l x` |
| `Th14Step5.agda:297` (outer mp at constr5_inner_final / K_part) | `K_part_l x` |

Each consumer rewrite is mechanical: replace `thmTDispMp_param y1T y2T x' y1' pT qT shape d1` with `thmTDispMp_param_l (PrAtX x) y1T y2T x' y1' pT qT shape_lifted d1_lifted innerCheck_lifted`.

### Step 1E — Smoke-test

`time /opt/homebrew/bin/agda BRA/GoedelIIFull.agda` should still
succeed and produce `godelII : Deriv Con -> Deriv bot`. Solo file
budgets:
- `Thm/ThmT.agda`: ~1.5–3s cached (it's 11k+ lines and gains some
  lifted-dispatcher infra).
- `Th14Step3.agda` / `Th14Step5.agda`: <1s each cached.
- `GoedelIIFull.agda`: <2s cached.

If any consumer file slows past 1s solo, **stop and re-architect** —
slowness signals a math mismatch, not a need for more patience.

## Methodology reminders

* Guard's mathematics is light. Fast typecheck = correct math; slow
  typecheck = math mismatch. This is about runtime, not design — but
  keep the consumer files small and the dispatcher's lifted form free
  of computational debt.
* No `with`-abstraction, no dot patterns, no postulates, no holes,
  ASCII only.
* No new `Deriv` constructors. No new ThmT primitives. Reuse
  `liftAxiom` / `liftedRuleTrans` / `liftedCong*` from
  `BRA/Thm/EvalHelpers.agda`.
* **camelCase every let-binding and helper**. Mid-identifier
  underscores break parsing — see
  `memory/feedback_agda_underscore_mixfix.md`.
* Work additively: only new files for Step 1B–1C scaffolding; touch
  `Thm/ThmT.agda` and consumers only after the scaffolds typecheck
  in isolation.
* Verify each new file compiles `<1s` solo before composing.

## Files to read first

1. **This file**.
2. `BRA/SOUND-THMT-FINDINGS.md` — full audit (Blockers 1–3).
3. `BRA/SoundMpProto.agda` + `BRA/SoundMpVProof.agda` — Step 1A
   deliverables; pattern to mirror for `body_ruleInst_v`.
4. `BRA/Th14Step5.agda` — primary consumer; lines 191–306 are the
   relevant body. Note the existing unlifted `inner_mp_raw` /
   `outer_mp_raw` calls and the trailing `liftAxiom`.
5. `BRA/Th14Constr5.agda` lines 148–164 — `step1_l` / `step2_l`
   templates. The same `liftThm13_F1` / `liftAxiom + axImpRefl`
   pattern is what blocks the unlifted form for `step3_l` / `K_part_l`.
6. `BRA/Thm/ThmT.agda` lines 5552–5945 — current `body_mp_eval`,
   `body_mp_eval_param`, `body_mp_eval_proj`, `thmTDispMp` /
   `thmTDispMp_param` / `thmTDispMp_proj`. The Step 1C swap edits
   these in place.
7. `BRA/Thm/EvalHelpers.agda` — `liftAxiom`, `liftedRuleTrans`,
   `liftedCong1/L/R`. The lifted dispatcher's plumbing.

## Files NOT to touch

* `BRA/Thm/Parts/*.agda` (the 31 truly tautological bodies).
* `BRA/Thm12*.agda`, `BRA/Thm11*.agda`, `BRA/Thm13*.agda`
  (the underlying Theorem 12/13/Goedel I closure).
* `BRA/Sub.agda`, `BRA/SubT.agda`, `BRA/Cor.agda`,
  `BRA/CodeCommutes.agda` (substitution machinery).
* `BRA/GoedelII.agda`, `BRA/GoedelIIFull.agda` (the verification
  cascades transparently through the dispatcher upgrade).

## Done when

1. `BRA/Thm/ThmT.agda` contains `thmTDispMp_param_l`,
   `body_mp_v` (replacing `body_mp`), `body_mp_v_eval_pass_param`
   (parametric form using `treeEqRefl_param`), and the analog for
   `body_ruleInst`.
2. `BRA/Th14Step3.agda` and `BRA/Th14Step5.agda` use the lifted
   dispatcher; the trailing `liftAxiom` at the tail is removed.
3. `BRA/GoedelIIFull.agda` typechecks, still proves
   `godelII : Deriv Con -> Deriv bot`, with `thmT` now soundness-
   verified at the mp and ruleInst dispatch layers.
4. Step 2 (the seven other premise-consuming dispatchers:
   `ruleSym`, `ruleTrans`, `cong1`, `congL`, `congR`, `ruleIndBT`,
   `ruleInst2`) is the next handoff and unchanged from
   `BRA/SOUND-THMT-FINDINGS.md`'s outline.
