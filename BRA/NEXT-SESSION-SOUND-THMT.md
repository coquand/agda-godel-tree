# Next session — verify body_mp and body_ruleInst

## TL;DR

Modify `BRA/Thm/ThmT.agda` so that `body_mp` and `body_ruleInst`
**verify the shape** of their `thmT y_h` premise before projecting
the conclusion. On shape-mismatch, output `codeTriv = reify
(codeFormula (atomic (eqn O O)))` (the encoded TRUE formula 0=0,
derivable via axRefl O).

After this change:
* `BRA/GoedelIIFull.agda` should still typecheck (in <1s solo) and
  produce `godelII : Deriv Con -> Deriv bot`.
* `K_part_l` (in `BRA/Th14Step4Final.agda`) becomes load-bearing —
  the verifying outer mp at `constr5_final` now genuinely requires
  the antecedent's `Deriv` value, which `K_part_l` provides.

This is **Step 1 of 2** in a soundness push.  Step 2 (verify
`ruleSym`, `ruleTrans`, `cong1`, `congL`, `congR`, `ruleIndBT`,
`ruleInst2`) is deferred to a follow-up session.

## Project context (read first)

* Agda 2.8 (`/opt/homebrew/bin/agda`).  `--safe --without-K
  --exact-split` on every file.  ASCII only, no unicode, no
  postulates, no holes, no `with`-abstraction, no dot patterns.
* The project prelude is described in `CLAUDE.md` at the project
  root; in particular: equality is `Eq` (`refl/eqSym/eqTrans/eqCong/
  eqSubst`), no mixfix.  BRA-internal Deriv equations use `ruleSym`,
  `ruleTrans`, `cong1/congL/congR`.
* Build any single file with: `/opt/homebrew/bin/agda BRA/<file>.agda`
  from `/Users/coquand/CHWISTEK`.  Per-file solo typecheck **must
  stay under 1 second**.  Slow typecheck = math mismatch (see
  `Methodology` section).

## Read first (in order)

1. **This file**.
2. `BRA/SoundMpProto.agda` — prototype of `body_mp_v` (combinator
   wiring confirmed; the evaluation proof is what this session
   produces).
3. `BRA/Thm/Parts/Mp.agda` — the **current** `body_mp` definition and
   `body_mp_eval` proof inside the `abstract` block.  This is the
   target file for the rewrite.
4. `BRA/Thm/Parts/RuleInst.agda` — same for `body_ruleInst`.
5. `BRA/Thm/ThmT.agda` lines 5698–5911 — `body_mp_eval_param` and
   `thmTDispMp_param`, the lemmas downstream of `body_mp` that the
   rewrite cascades through.
6. `BRA/Th14Step4Final.agda` and `BRA/Th14Step5.agda` — where the
   `thmTDispMp_param` callers live, to gauge how the
   verification-hypothesis change ripples.
7. `BRA/godelI-II-summary.tex` — the big-picture summary (Gödel I &
   II in BRA, completed in the previous session).

## Soundness goal (informal)

For all `x : Term`,
```
forall F.  thmT x = reify (codeFormula F)  ->  Deriv F.
```

**Step 1 scope** establishes this for inputs that pass through the
`mp` and `ruleInst` dispatchers; the seven other premise-consuming
rule dispatchers (`ruleSym`, `ruleTrans`, `cong1`, `congL`, `congR`,
`ruleIndBT`, `ruleInst2`) remain unverified after this session and
will be addressed in Step 2.

The 31 *truly tautological* bodies (algebraic axioms `axI`, `axFst`,
..., `axComp2`, `axTreeRec*`, `axIfLf*`, `axTreeEq*`, `axGoodstein`,
`axRefl`, plus the 4 safe-defaults; plus the propositional/equational
axioms `axK`, `axS`, `axNeg`, `axExFalso`, `axContrapos`,
`axEqTrans`, `axEqCong*`) are **not** modified — their conclusions
are tautologies parametric in their slots.

## The verifying combinator (from `BRA/SoundMpProto.agda`)

```agda
codeTriv : Term
codeTriv = reify (codeFormula (atomic (eqn O O)))
-- definitionally equal to ap2 Pair O O = falseT (a notational
-- coincidence; codeTriv is the code of a TRUE formula).

private
  -- thmT y1T = Fst (Snd b)
  get_d1   = Comp Fst Snd
  -- thmT y2T = Snd (Snd b)
  get_d2   = Comp Snd Snd
  -- Fst (thmT y1T) = head; should be tagImp.
  get_head = Comp Fst (Comp Fst Snd)
  -- pT = antecedent slot of thmT y1T's imp encoding.
  get_pT   = Comp Fst (Comp Snd (Comp Fst Snd))
  -- qT = consequent slot.
  get_qT   = Comp Snd (Comp Snd (Comp Fst Snd))

body_mp_v : Fun2
body_mp_v =
  Fan
    (Fan
      (Fan (Lift get_head) (Lift (KT (reify tagImp))) TreeEq)  -- outer check
      (Fan
        (Fan (Lift get_d2) (Lift get_pT) TreeEq)               -- inner check
        (Lift (KT falseT))                                       -- short-circuit
        Pair)
      IfLf)
    (Fan
      (Lift get_qT)                                              -- pass branch
      (Lift (KT codeTriv))                                       -- fail branch
      Pair)
    IfLf
```

The combinator typechecks; see `BRA/SoundMpProto.agda`.

## Tasks

1. **`BRA/Thm/Parts/Mp.agda`**: replace `body_mp` with `body_mp_v`.
   Prove **two** evaluation lemmas (inside the existing `abstract`
   block, mirroring `body_mp_eval`):

   ```agda
   body_mp_v_eval_pass :
     (y1T y2T pT qT : Term) (b : Term) ->
     -- Hypotheses: shape checks pass.
     Deriv (atomic (eqn (ap1 Fst y1T) (ap2 Pair _ _))) ->         -- shape of y1T
     Deriv (atomic (eqn (ap1 Snd b)
                          (ap2 Pair (ap2 Pair (reify tagImp) (ap2 Pair pT qT))
                                     pT))) ->                       -- thmT y1T imp-shape, thmT y2T = pT
     Deriv (atomic (eqn (ap2 body_mp_v
                               (ap2 Pair tagCode_mp (ap2 Pair y1T y2T)) b)
                          qT))

   body_mp_v_eval_fail :
     (y1T y2T : Term) (b : Term) ->
     -- Hypothesis: outer or inner check fails.
     Deriv (atomic (eqn <relevant TreeEq> falseT)) ->
     Deriv (atomic (eqn (ap2 body_mp_v
                               (ap2 Pair tagCode_mp (ap2 Pair y1T y2T)) b)
                          codeTriv))
   ```

   Each chain is `axFan` -> `axLift` -> `axComp` projections ->
   `axIfLf*` to dispatch.  Use the existing
   `pairOfFan_eval`/`pairOfConst_eval` helpers in
   `BRA/Thm/EvalHelpers.agda` for the inner extractors.

2. **`BRA/Thm/Parts/RuleInst.agda`**: replace `body_ruleInst` with
   a verifying version.  The verification check is: `Fst (thmT y_h)`
   must have a code-of-formula head (one of `tagAtomic` shapes,
   tagImp, tagNeg).  *Simpler version*: check that `thmT y_h` is at
   least `Pair _ _` shaped (i.e., not `O`, since codeFormulas are
   never lf).  This catches the "y_h returns garbage O" case.  More
   discriminating checks can be added later.

   Note: `subT` is invoked **only on the pass branch**, so the existing
   `subT` machinery is unchanged.

3. **`BRA/Thm/ThmT.agda`**: update `body_mp_eval_param` and
   `thmTDispMp_param` (lines 5698–5911) to use the verifying body.
   The new `thmTDispMp_param` takes an additional inner-check
   hypothesis:

   ```agda
   thmTDispMp_param :
     (y1T y2T : Term) (y1' x' : Term) (pT qT : Term) ->
     Deriv (atomic (eqn (ap1 Fst y1T) (ap2 Pair x' y1'))) ->     -- existing shape
     Deriv (atomic (eqn (ap1 thmT y1T)
                          (ap2 Pair (reify tagImp) (ap2 Pair pT qT)))) ->  -- existing d1
     Deriv (atomic (eqn (ap1 thmT y2T) pT)) ->                    -- NEW: inner check
     Deriv (atomic (eqn (ap1 thmT (ap2 Pair tagCode_mp (ap2 Pair y1T y2T))) qT))
   ```

   Same for `thmTDispRuleInst_param`: add a hypothesis that
   `thmT y_h` is a valid codeFormula (or weaker: is `Pair _ _` shaped).

4. **`BRA/Th14Step4Final.agda`** (the consumer of `K_part_l`) and
   **`BRA/Th14Step5.agda`** (the consumer of `step3_l`, `K_part_l`,
   `h_part_skel_l`): the existing callers already have the
   pT-equation `Deriv` available — wire it as the new hypothesis to
   `thmTDispMp_param`.  In `step5_l`'s outer mp:
   `K_part_l x` is exactly the new third hypothesis.

5. **Smoke-test**: `/opt/homebrew/bin/agda BRA/GoedelIIFull.agda`
   should typecheck, with all per-file solo times under 1s (modulo
   `BRA/Thm/ThmT.agda`'s ~20s baseline).

## Methodology (carry over from the Gödel II push)

* **Fast typecheck = correct math.** If a file slows past ~1s solo,
  stop and re-architect.  Do not patiently retry — slowness signals
  the math is mismatched (typically: a meta-Eq forcing Agda to unfold
  an opaque definition like `codeFormula G`).

* **Use `abstract` blocks** for any new lemma whose body Agda
  shouldn't unfold at call sites.  The existing `abstract` block in
  `BRA/Thm/ThmT.agda` and `BRA/Th14SubTLeaf.agda` are exemplars.

* **The verifying body's `_eval_pass` proof** is a chain of small
  Deriv equations: `axFan` -> `axComp` -> `axLift` -> `axIfLf*` ->
  `congL/R IfLf` to bridge intermediate forms.  See
  `BRA/Thm/Parts/Mp.agda` (current version) for the structure of
  the existing `body_mp_eval` proof — the verifying version adds
  three layers of `IfLf` bridging on top.

* **For the outer-check `Deriv`-witness** in `body_mp_v_eval_pass`:
  `Deriv (eqn (TreeEq tagImp tagImp) O)` follows from `treeEqRed
  tagImp tagImp + boolCase true`.  Routine.

## Done when

`/opt/homebrew/bin/agda BRA/GoedelIIFull.agda` exits cleanly with
zero errors, and the new `body_mp_v` / `body_ruleInst_v` are in
place.  The chain still produces:

```agda
godelII : Deriv Con -> Deriv bot
```

with the *partially* sound `thmT` (sound through `mp` and
`ruleInst`).  Note in the file header that Step 1 is complete and
Step 2 (the other 7 rule dispatchers) is the next handoff.

## Constraints

* ASCII only.
* `--safe --without-K --exact-split` everywhere.
* No postulates, no holes, no `with`-abstraction, no dot patterns.
* No new Deriv constructors.
* No new ThmT primitive lemmas (only new uses of existing
  `axFan`, `axComp`, `axLift`, `axIfLf*`, `treeEqRed`, etc.).
* Per-file solo typecheck under 1s with cache, <10s fresh.

## Files to modify

* `BRA/Thm/Parts/Mp.agda` (replace `body_mp` and `body_mp_eval`).
* `BRA/Thm/Parts/RuleInst.agda` (replace `body_ruleInst` and
  `body_ruleInst_eval`).
* `BRA/Thm/ThmT.agda` (update `body_mp_eval_param`,
  `thmTDispMp_param`, `body_ruleInst_eval_param`,
  `thmTDispRuleInst_param`; add inner-check hypotheses).
* `BRA/Th14Step5.agda` (wire `K_part_l` and `g_part_l` outputs as
  inner-check hypotheses to the new `thmTDispMp_param` calls).
* (Optionally) `BRA/Thm14SubLemma.agda` for `thmTSubLemma` updates.

## Files NOT touched

* All other `BRA/Thm/Parts/*.agda` (the 31 truly tautological bodies).
* `BRA/Th14Step3*.agda`, `BRA/Th14Step4*.agda`,
  `BRA/Th14Step5HPart.agda` (structural canonicalization unaffected).
* `BRA/Thm12.agda`, `BRA/Thm13.agda`, `BRA/Thm11*.agda` (Theorem
  12/13/Goedel I closure unaffected).
* `BRA/Sub.agda`, `BRA/SubT.agda`, `BRA/Cor.agda`,
  `BRA/CodeCommutes.agda` (substitution machinery unchanged).
* `BRA/GoedelIIFull.agda`, `BRA/GoedelII.agda` (no changes expected
  — the verification kicks in at the dispatcher level, transparently
  upstream of these files).

## Pitfalls (from prior sessions)

1. **Don't put `codeFormula G` in any goal type.**  See
   `feedback_no_codeformula_g_in_goal_types` in MEMORY.md.
2. **`cor x` in subT targets requires `subT_to_meta` +
   `codedSubstT_code_thmT_var1`** (in `BRA/Th14SubTLeaf.agda`).
   Unchanged from previous session.
3. **Agda's reduction may not unfold `Snd (reify (natCode k))`
   to the (k-1)-tail Pair**.  Use `axSnd` explicitly.  See
   `shape_inner_pair_bridge` in `BRA/Th14Step3.agda` for the pattern.
4. **`abstract` blocks**: don't accidentally re-export an abstract
   definition's body via `using` — the unfolded body breaks fast
   typecheck.
