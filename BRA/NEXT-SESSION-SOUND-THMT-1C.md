# Next session - Sound thmT Step 1C/1D (body_mp_v swap + consumer rewrites)

## State at handoff

Step 1B is **done** (this session, validated):

* `BRA/Thm/ThmT.agda` now contains `thmTDispMp_param_l` (lifted under
  an arbitrary auxiliary formula P) plus three supporting lemmas
  (`stepProto_else_l`, `thmTDistrib_param_l`, `body_mp_eval_param_l`).
  All four take an `_innerL` hypothesis but it is currently unused -
  the underlying `body_mp` is still the non-verifying
  `Post (Comp (Comp Snd (Comp Snd Fst)) (Comp Snd Snd)) Pair`.
  Step 1C makes `_innerL` load-bearing.

Step 1C-1 is **done**:

* `BRA/TreeEqReflParam.agda` (~145 LoC, 0.15s solo) provides
  `treeEqReflParam : (t : Term) -> Deriv (atomic (eqn (ap2 TreeEq t t) O))`
  via `ruleIndBT` on the motive `atomic (eqn (TreeEq (var 0)(var 0)) O)`.
  The step case uses `liftAxiomTwo` / `liftedRuleTransTwo` /
  `liftedCongLTwo` from `BRA.Thm.EvalHelpers` plus an inline
  `idImp Q = mp(mp axS (axK ...))(axK Q Q)` to thread IH2.

Step 1C-2 is **partially done**:

* `BRA/SoundMpVProof.agda` now exports both
  `body_mp_v_eval_pass` (closed) and `body_mp_v_eval_pass_l`
  (lifted under P).  The lifted version mirrors the closed proof
  step-for-step, replacing each `ruleTrans / cong / axiom` with the
  corresponding `liftedRuleTrans / liftedCong* / liftAxiom P` helper
  from `BRA.Thm.EvalHelpers`.  ~370 LoC, 2.5s solo build.

* The actual body_mp swap (`body_mp = body_mp_v`) was attempted but
  **reverted** because the consumer rewrites (Th14Step3, Th14Step5)
  need additional bridging that this session's scope did not cover.
  See "Why deferred" below.

`BRA/Thm/ThmT.agda`'s body_mp definition explicitly notes the
soundification target and the deferred work.  Baseline still passes:
`time /opt/homebrew/bin/agda BRA/GoedelIIFull.agda` = 0.73s cached,
producing `godelII : Deriv Con -> Deriv bot` unchanged.

## Why Step 1C-2 / 1D was deferred

When `body_mp` is swapped to `body_mp_v`, every consumer of the mp
dispatcher must supply a third hypothesis
`dh : Deriv (atomic (eqn (ap1 thmT y2T) pT))`.  In
`Th14Step3.agda` and `Th14Step5.agda`, the consumers are working
under `PrAtX x = atomic (eqn (thmT x) cG)` and the only available
`dh` witnesses come from the lifted helpers `step1_l`, `step2_l`,
`step3_l`, `K_part_l` (in `Th14Constr5.agda` / `Thm14Constr5Final.agda`).

The mismatch: those witnesses give RHS `codeFTeq1Hyp f x cG` (which
contains `ap1 cor cG`), but the existing `target_c x` /
`target_h x` use `antec1 = Pair (encoded_th_x_at x) (reify (code cG))`
(closed-Tree form).  Bridging requires a new lemma
`corCGBridge : Deriv (atomic (eqn (ap1 cor cG) (reify (code cG))))`
exploiting `cG = reify (codeFormula G)` and `BRA.Cor.corOfReify`.

This is a tractable but non-trivial chain change: at least four
consumer call sites (Th14Step3 inner/outer, Th14Step5 inner/outer)
need rewrite to use `thmTDispMp_param_l`, and `target_c` /
`target_h` may need parallel `_l` variants whose Pair-positions hold
`codeFTeq1Hyp ...` instead of `antec1`.  Two days of careful
surgery, not one session.

## Tasks (target order for next session)

### Step 1C-2a - Build the cor cG bridge

New file `BRA/CorCGBridge.agda` (~30 LoC):

```agda
open import BRA.Cor using (corOfReify)
open import BRA.GoedelII using (cG ; G)

corCGBridge : Deriv (atomic (eqn (ap1 cor cG) (reify (code cG))))
corCGBridge =
  -- cG = reify (codeFormula G) by definition.
  -- corOfReify (codeFormula G) :
  --   Deriv (atomic (eqn (ap1 cor (reify (codeFormula G)))
  --                       (reify (code (reify (codeFormula G))))))
  -- Both sides reduce definitionally to the desired form
  -- (code (reify t) = t for closed Tree t).
  corOfReify (codeFormula G)
```

Verify <0.5s solo.  If `code (reify ...)` doesn't reduce
definitionally, build the bridge via explicit code-section lemmas.

### Step 1C-2b - Swap body_mp definition

In `BRA/Thm/ThmT.agda`, change:

```agda
body_mp : Fun2
body_mp = Post (Comp (Comp Snd (Comp Snd Fst)) (Comp Snd Snd)) Pair
```

to:

```agda
body_mp : Fun2
body_mp = body_mp_v
```

Update `body_mp_eval`, `body_mp_eval_param`, `body_mp_eval_param_l`
to use `body_mp_v_eval_pass` / `body_mp_v_eval_pass_l` (already
proved in `BRA/SoundMpVProof.agda`).  Each of these gains a 3rd
hypothesis `dh : (P imp)? atomic (eqn (thmT y2T) pT)`.

`body_mp_eval_proj` and `thmTDispMp_proj` either grow the `dh` arg
or get deleted; `Th14MpProjSmoke.agda` is the only consumer and is
not in the godelII chain.

### Step 1C-2c - Update unlifted thmTDispMp + thmTDispMp_param

Add `dh` to both signatures.  `thmTDispMp` already takes a third arg
`d2 : Deriv (atomic (eqn (thmT (reify y2)) (reify (codeFormula P))))`
that it currently discards via `_`; rename it to `dh` and pass to
`body_mp_eval`.

`thmTDispMp_param` does NOT currently take `dh`.  Add it as the 9th
arg and thread to `body_mp_eval_param`.  Update
`thmTDispMp_param_l` similarly to use `_innerL` (rename to
`innerL`).

### Step 1D - Rewrite Th14Step3.agda / Th14Step5.agda

Switch both files from `thmTDispMp_param` (closed) to
`thmTDispMp_param_l` (lifted under `PrAtX x`).  Witness map:

| Call site | Inner-check witness pre-bridge | After corCGBridge |
|--|--|--|
| Th14Step3 inner | `step1_l x` (codeFTeq1Hyp form) | bridged to `antec1` form |
| Th14Step3 outer | `step2_l x` (codeFTeq2Hyp form) | bridged to `antec2` form |
| Th14Step5 inner | `step3_l x` (already in `Pair (encoded_th_x_at x) encoded_sub_ii` form, no bridge needed) | as-is |
| Th14Step5 outer | `K_part_l x` (codeFormula bot form) | as-is |

For Th14Step3, you may instead choose to redefine `target_c` /
`step3_canon` so that the inner Pair positions use `codeFTeq*Hyp`
forms directly (avoiding the bridge but rippling through Stage A/B/C
of `Th14Step3Canon.agda`).  Decide based on which path keeps the
chain shorter.

### Step 1E - Smoke-test

`time /opt/homebrew/bin/agda BRA/GoedelIIFull.agda` should still
succeed and produce `godelII : Deriv Con -> Deriv bot`.  Per-file
budgets:
- `Thm/ThmT.agda`: ~1.5s cached.
- `Th14Step3.agda` / `Th14Step5.agda`: <1s each cached.
- `GoedelIIFull.agda`: <1s cached.

## Methodology reminders

* No `with`-abstraction, no dot patterns, no postulates, no holes.
* No new `Deriv` constructors; reuse `liftAxiom` /
  `liftedRuleTrans` / `liftedCong*` from `BRA/Thm/EvalHelpers.agda`.
* camelCase for every let-binding (mid-identifier `_` parses as a
  mixfix hole and breaks parsing).
* Verify each new file typechecks <1s solo before composing.
* If any consumer slows past 1s solo, **stop and re-architect** -
  slowness signals math mismatch.

## Files to read first

1. **This file**.
2. `BRA/SOUND-THMT-FINDINGS.md` - original audit.
3. `BRA/SoundMpVProof.agda` - both closed and lifted forms ready.
4. `BRA/Thm/ThmT.agda` lines 350-365 (body_mp comment),
   5825-5960 (thmTDispMp_param), 6100-6240 (thmTDispMp_param_l).
5. `BRA/Th14Step3.agda` lines 494-633 (step3_l, two mp dispatches).
6. `BRA/Th14Step5.agda` lines 191-305 (step5_l, two mp dispatches).
7. `BRA/Th14Constr5.agda` lines 148-164 (step1_l, step2_l templates).

## Files NOT to touch

* `BRA/Thm/Parts/*.agda` (the truly tautological bodies).
* `BRA/Thm12*.agda`, `BRA/Thm11*.agda`, `BRA/Thm13*.agda`.
* `BRA/Sub.agda`, `BRA/SubT.agda`, `BRA/Cor.agda`,
  `BRA/CodeCommutes.agda`.
* `BRA/GoedelII.agda`, `BRA/GoedelIIFull.agda` (verification
  cascades through the dispatcher upgrade).

## Done when

1. `body_mp = body_mp_v` in `BRA/Thm/ThmT.agda`.
2. `body_mp_eval` / `body_mp_eval_param` /
   `body_mp_eval_param_l` use `body_mp_v_eval_pass`
   (closed/lifted).
3. `thmTDispMp` / `thmTDispMp_param` / `thmTDispMp_param_l` thread
   the inner-check `dh` hypothesis.
4. `Th14Step3.agda` / `Th14Step5.agda` use the lifted dispatcher.
5. `BRA/GoedelIIFull.agda` typechecks, still proves
   `godelII : Deriv Con -> Deriv bot`, with `thmT` now
   soundness-verified at the mp dispatch layer.
