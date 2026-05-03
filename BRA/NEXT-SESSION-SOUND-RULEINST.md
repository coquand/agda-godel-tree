# Next session — Sound thmT Step 1C-3: body_ruleInst soundification

## State at handoff

Steps 1B / 1C-1 / 1C-2 / 1D **DONE** (previous session, validated):

* `body_mp = body_mp_v` in `BRA/Thm/ThmT.agda` — the verifying mp
  body is now load-bearing.
* `BRA/SoundMpProto.agda` + `BRA/SoundMpVProof.agda` (with both
  closed `body_mp_v_eval_pass` and lifted `body_mp_v_eval_pass_l`)
  ship the verifying combinator and its evaluation proof.
* `BRA/TreeEqReflParam.agda` provides the parametric
  `treeEqReflParam : (t : Term) -> Deriv (atomic (eqn (TreeEq t t) O))`.
* `BRA/CorCGBridge.agda` provides `corCGBridge` for the
  `cor cG ↔ reify (code cG)` equality (used by Th14Step3 outer mp).
* `BRA/Th14Step3.agda` and `BRA/Th14Step5.agda` rewritten to use
  `thmTDispMp_param_l` (lifted dispatcher) with `step1_l`/`step2_l`/
  `step3_l`/`K_part_l` as inner-check witnesses.  Trailing
  `liftAxiom (PrAtX x)` removed from both step5_l and step3_l.

`godelII : Deriv Con -> Deriv bot` cached at 0.78s, unchanged from
baseline.  Per-file budgets all <1s cached.

## What's NOT yet done

`body_ruleInst` is still the non-verifying
```agda
body_ruleInst = Fan (Lift (Comp Fst Snd))
                    (Post (Comp Snd (Comp Snd Snd)) Pair)
                    subT
```
(BRA/Thm/ThmT.agda line 371).  The dispatcher currently runs subT
on whatever payload arrives without checking the input is well-formed.

Per `BRA/SOUND-THMT-FINDINGS.md` Blocker 1 follow-up, the verifying
body_ruleInst_v should:
1. Check `thmT y_h` is at least Pair-shaped (i.e. not O — any leaf
   value indicates a malformed sub-proof encoding).
2. On verification pass, run the existing subT pipeline.
3. On verification fail, output codeTriv = falseT.

## Mathematical context

`body_ruleInst` lives at the `tagRuleInst` slot of the cascade.  Its
input pair `a = Pair tagCode_ruleInst (Pair (Pair varCode tCode) y_h)`
encodes `ruleInst x t pf` where `pf : Deriv P` is encoded as the
sub-proof `y_h` whose `thmT y_h_reified = reify (codeFormula P)`.
The body computes `subT(<varCode, tCode>, thmT y_h)` to get the code
of `substF x t P`.

Consumers of the closed `thmTDispRuleInst_param` (currently 9 call
sites — see `grep "thmTDispRuleInst_param" BRA/`):
  - `BRA/Thm12/Param/RuleInst.agda`: foundation Thm 12 plumbing.
  - `BRA/Thm14SubLemma.agda`, `BRA/Thm14Step4Test.agda`,
    `BRA/SbRuntime.agda`, `BRA/Th12I.agda`, `BRA/Th12Z.agda`:
    closed-form witness assembly (the inner-check witness should be
    discharged via local Deriv inputs that show `thmT y_h_reified`
    has the right encoded shape).
  - `BRA/Th14Step4.agda`: Phase C step 4, lifted under PrAtX x.
    Likely needs a `thmTDispRuleInst_param_l` (lifted variant) +
    consumer rewrite mirroring the mp pattern.

## Tasks (target order)

### Step 1C-3a — Verifying body combinator + eval proofs

Mirror the `BRA/SoundMpProto.agda` + `BRA/SoundMpVProof.agda` pair:

1. New file `BRA/SoundRuleInstProto.agda` (~120 LoC, target <0.2s solo):
   ```agda
   body_ruleInst_v : Fun2
   body_ruleInst_v = Post verifierRIF1 Pair
   ```
   where `verifierRIF1` extracts `thmT y_h` from `b`'s payload,
   checks it is `Pair _ _`-shaped via the standard
   `IfLf (TreeEq (Fst (thmT y_h)) Fst-of-Pair-stub) ...` trick (or a
   simpler "fst-not-O" predicate), and either runs the existing
   `Fan args (thmT y_h_extractor) subT` on pass or returns codeTriv.

   The key design choice: what predicate to verify.  The simplest
   check is **`Fst (thmT y_h) ≠ O`** (i.e., thmT y_h is `Pair _ _`,
   not a leaf).  Implement via
   `treeEq (Fst (thmT y_h)) something_nonzero` or — better —
   `IfLf (Fst (thmT y_h))` which returns the second branch when the
   first arg is `Pair _ _` and the first branch when it's `O`.

   ASCII only.  camelCase identifiers.

2. New file `BRA/SoundRuleInstVProof.agda` (~250 LoC, target <0.3s
   solo):
   ```agda
   body_ruleInst_v_eval_pass :
     (a bb : Term) (varCode tCode y_h th_y_h fst_part snd_part : Term) ->
     Deriv (atomic (eqn (ap1 Fst (ap1 Snd a)) (ap2 Pair varCode tCode))) ->
     Deriv (atomic (eqn (ap1 Snd bb) -- distH for ruleInst payload
                         (ap2 Pair (ap1 thmT (Pair varCode tCode))
                                    (ap1 thmT y_h)))) ->
     Deriv (atomic (eqn (ap1 thmT y_h) (ap2 Pair fst_part snd_part))) ->
     -- (the inner-check witness: thmT y_h is Pair-shaped)
     Deriv (atomic (eqn (ap2 body_ruleInst_v a bb)
                         (ap2 subT (ap2 Pair varCode tCode)
                                    (ap2 Pair fst_part snd_part))))
   ```

   Mirror `body_mp_v_eval_pass`'s section structure: A (extractors
   through t = Pair a bb), B (verification reduction), C (output =
   subT-on-pass), wrapping in axPost.

3. New file `BRA/SoundRuleInstVProofLifted.agda` OR extend
   `BRA/SoundRuleInstVProof.agda` with `body_ruleInst_v_eval_pass_l`
   (lifted under arbitrary P), mirroring the mp version's mechanical
   `liftAxiom P` / `liftedRuleTrans P` / `liftedCong* P` lift.

Per-file budget: each <1s solo.

### Step 1C-3b — Swap body_ruleInst -> body_ruleInst_v in ThmT.agda

In `BRA/Thm/ThmT.agda`:

1. Add imports near the top:
   ```agda
   open import BRA.SoundRuleInstProto using (body_ruleInst_v)
   open import BRA.SoundRuleInstVProof using
     ( body_ruleInst_v_eval_pass ; body_ruleInst_v_eval_pass_l )
   ```

2. Change `body_ruleInst = Fan ... subT` to
   `body_ruleInst = body_ruleInst_v` at line ~371.

3. Update `body_ruleInst_eval` (line 9009), `body_ruleInst_eval_param`
   (line 9227), and `body_ruleInst_eval_proj` (if present) to take
   the new inner-check `dh : thmT y_h_reified = Pair _ _` hypothesis
   and route through `body_ruleInst_v_eval_pass`.

4. Update `thmTDispRuleInst` (line 9108), `thmTDispRuleInst_param`
   (line 9320), `thmTDispRuleInst_proj` (if present) signatures to
   thread the new dh hypothesis.

5. Add `thmTDispRuleInst_param_l` (lifted dispatcher) mirroring
   `thmTDispMp_param_l`'s implementation.  Uses the existing
   `prefixClosed` factoring + `thmTDistrib_param_l` +
   `body_ruleInst_v_eval_pass_l` pattern.

### Step 1C-3c — Update thmTDispRuleInst_param consumers

For each call site (9 files listed above), add the inner-check
hypothesis.  Most have a closed witness available
(`d_h : thmT y_h_reified = reify (codeFormula P)` already provides a
Pair-shaped RHS for non-trivial P; the `Fst _ ≠ O` shape is then
derivable via `axFst` on the encoded form).  For
`BRA/Th14Step4.agda` (lifted under PrAtX x), use
`thmTDispRuleInst_param_l` with the closed witness lifted.

The mp pattern was: `dh = step1_l x` (lifted) bridged via
`corCGBridge`.  ruleInst is simpler — most of its consumers already
have the encoded shape witness directly.

### Step 1C-3d — Smoke-test

`time /opt/homebrew/bin/agda BRA/GoedelIIFull.agda` should still
succeed and produce `godelII : Deriv Con -> Deriv bot`.  Per-file
budgets:
- `Thm/ThmT.agda`: ~1s cached.
- `Th14Step3.agda` / `Th14Step4.agda` / `Th14Step5.agda`: <1s each.
- `GoedelIIFull.agda`: <1s cached.

If any consumer slows past 1s solo, **stop and re-architect**.

## Step 2 outline (next handoff after 1C-3)

The seven other premise-consuming dispatchers also accept their
sub-proof premises silently:

| Tag | Body | Sub-proof premise(s) | Verification target |
|--|--|--|--|
| ruleSym | body_ruleSym | one Deriv-encoding | thmT y is `eqn`-shaped (Pair t1 t2) |
| ruleTrans | body_ruleTrans | two Deriv-encodings | both eqn-shaped, middle term shared |
| cong1 | body_cong1 | one Deriv-encoding | eqn-shaped |
| congL | body_congL | one Deriv-encoding | eqn-shaped |
| congR | body_congR | one Deriv-encoding | eqn-shaped |
| ruleIndBT | body_ruleIndBT | base + step Derivs | base = P[0:=O], step is impl-shaped |
| ruleInst2 | body_ruleInst2 | one Deriv-encoding | base shape ok |

Each follows the SoundMpProto/_VProof template.  Step 2 is roughly
twice the size of Step 1C-3 (7 dispatchers × 800 LoC ≈ 5500 LoC
total) but mostly mechanical given the mp/ruleInst patterns.

## Methodology reminders

* No `with`-abstraction, no dot patterns, no postulates, no holes.
* No new `Deriv` constructors.
* Reuse `liftAxiom` / `liftedRuleTrans` / `liftedCong*` from
  `BRA/Thm/EvalHelpers.agda`.
* camelCase for every let-binding (mid-identifier `_` parses as a
  mixfix hole and breaks parsing).  Snake_case is fine for top-level
  names that are in scope as full identifiers.
* Verify each new file typechecks <1s solo before composing.
* Fast typecheck = correct math; slowness signals math mismatch.

## Files to read first

1. **This file**.
2. `BRA/SOUND-THMT-FINDINGS.md` — original audit.
3. `BRA/SoundMpProto.agda` + `BRA/SoundMpVProof.agda` — the template
   pattern to mirror.  ~120 + 700 LoC.  Verify both still typecheck
   in your fresh session before starting.
4. `BRA/Thm/ThmT.agda` lines 5552-5730 — current
   body_mp_eval / _param / _proj wrappers around
   body_mp_v_eval_pass.  This is the integration template to mirror
   for body_ruleInst.
5. `BRA/Thm/ThmT.agda` lines 9009-9425 — current
   body_ruleInst_eval / _param + thmTDispRuleInst / _param
   definitions to update.
6. `BRA/Th14Step4Final.agda` — uses `thmTDispRuleInst_param` under
   PrAtX x; needs the lifted dispatcher variant.
7. `BRA/Th14Step3.agda` lines 494-790 — example of corCGBridge-style
   bridging in the mp consumer rewrite (template for any ruleInst
   consumer that needs PrAtX-lifted innerL witnesses).
8. `BRA/Thm12/Param/RuleInst.agda` — closed-form ruleInst dispatch
   used by Theorem 12 plumbing; the simplest consumer to update.

## Files NOT to touch

* `BRA/Thm/Parts/*.agda` (the truly tautological bodies).
* `BRA/Thm12*.agda` non-Param files, `BRA/Thm11*.agda`,
  `BRA/Thm13*.agda` (these consume the abstract dispatchers, not
  the concrete ones).
* `BRA/Sub.agda`, `BRA/SubT.agda`, `BRA/Cor.agda`,
  `BRA/CodeCommutes.agda` (substitution machinery).
* `BRA/GoedelII.agda`, `BRA/GoedelIIFull.agda` (verification
  cascades through the dispatcher upgrade).

## Done when

1. `body_ruleInst = body_ruleInst_v` in `BRA/Thm/ThmT.agda`.
2. `body_ruleInst_eval` / `_param` / `_proj` route through
   `body_ruleInst_v_eval_pass`.
3. `thmTDispRuleInst` / `_param` / `_proj` thread the inner-check.
4. `thmTDispRuleInst_param_l` exists and works under PrAtX x.
5. All 9 closed-call-site consumers updated.
6. `BRA/Th14Step4.agda` (the only PrAtX-lifted consumer) uses
   `thmTDispRuleInst_param_l`.
7. `BRA/GoedelIIFull.agda` typechecks, still proves
   `godelII : Deriv Con -> Deriv bot`, with `thmT` now soundness-
   verified at the **mp AND ruleInst** dispatch layers.

After this, Step 2 (the seven other premise-consuming dispatchers)
is the natural next handoff.
