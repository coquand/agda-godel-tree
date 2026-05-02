# Next session — `thmT` parametric Definition 12 line 2 (structural fix)

## Why this exists (and why it's weird)

We were supposed to follow Guard 1963, Theorem 14, line by line.  Guard's
Definition 12 (p.16) defines `th` by the parametric equations

    th(4y)   = ax(y)
    th(4y+1) = sb(KKy, LKy, th(Ly))
    th(4y+2) = mp(th(Ky), th(Ly))
    th(4y+3) = ind(th(Ky), th(Ly))

These hold for **any** `y`, with no shape side condition.  Guard treats them
as defining equations of `th`.

In our Agda port, `thmT : Fun1` is built as `Rec stepProtoWrapped` over a
40-level `IfLf` cascade.  For closed canonical inputs the cascade reduces
correctly and Definition 12 line 2 is provable as `thmTDispRuleInst`.  For
**open** inputs (a `Term` variable like `var 1`), the cascade is stuck
because `stepProto` discriminates on `Fst (Fst a)` — and that `Fst` does
not reduce on a variable.

Concretely: in `BRA/Thm/ThmT.agda`, `body_ruleInst`'s `CODEP_extractor`
(`Post (Comp (Comp Fst Snd) (Comp Snd Snd)) Pair`) evaluates to
`Fst (Snd (thmT payT))`.  By outer `axRecNd` + the right-branch reduction,
`thmT payT = Pair (thmT varCode) (thmT (Pair y tT))`.  So we end up at
`Fst (thmT (Pair y tT))`.  By `axRecNd` again,
`thmT (Pair y tT) = stepProto (Pair y tT) (Pair (thmT y) (thmT tT))` —
and `stepProto` fires on `Fst y`.  Stuck.

The hypothesis `thmT y = codeP` does **not** fix this: it tells us about
`thmT y`, not about which `IfLf` branch `stepProto` takes.

The issue does not appear in Guard because Guard treats Definition 12
line 2 as a primitive parametric equation, not as something to be derived
from a tree-recursion implementation.  Our cascade implementation does not
satisfy the parametric equation directly for open inputs — only for closed
canonical inputs (where `Fst y` reduces).

This is why the obstruction "is weird": the math is Guard's, but the
Agda-implementation of `thmT` does not honour Guard's parametric
defining equations on open Terms.  Goedel I works (encode's recursion
always produces closed proof-indices), but Goedel II's step 4
(`K_part(x)` with proof-index `x` = a free variable) hits the gap.

## Status (committed in session 2026-05-02)

  * `BRA/Thm14Numerals.agda` (commit `60b3119`) — Phase A: closed
    encoded transitivity / ex-falso witnesses (`t_term`, `t'_term` and
    their `t_witness`, `t'_witness`).  170 LoC, 0.33s.

  * `BRA/Thm14Constr5Final.agda` (commit `8b11e3b`) — Phase B: closed
    Fun1 definitions for `f_part`, `g_part`, `K_part`, `h_part`,
    `constr5`, parametric in `r12_th`, `r12_sub`.  266 LoC, 0.61s.

  * `BRA/Thm14SubLemma.agda` (commit `041794c`) — `thmTSubLemma`
    parametric Def 12 line 2, **with an `xShape` precondition** (the
    shape vestige inherited from `thmTDispRuleInst_param`).  Useful for
    the f_part / g_part / h_part chain layers where the proof-index is
    Pair-shaped via `Comp2 Pair` wrappers.

  * `BRA/NEXT-SESSION-THM14-PHASE-C.md` — Phase C blocker analysis;
    documents the three structural fix routes.

## Goal for this session

Decide on, and execute, a **structural fix** to `thmT` (or its
infrastructure) so that Definition 12 line 2 holds parametrically in
y — i.e., no `xShape` precondition.  Once that lands, Phase C
(`step3_l..step5_l`) follows mechanically using `thmTSubLemma`
(shape-free) + `thmTDispMp` chain manipulations.

## Three routes — pick one before writing code

### Route 1 — Mutual block: `body_ruleInst` references `thmT`

Change `body_ruleInst`'s CODEP_extractor from
`Post (Comp (Comp Fst Snd) (Comp Snd Snd)) Pair`
(reads recs, requires inner thmT-distrib) to
`Lift (Comp thmT (Comp Fst (Comp Snd Snd)))`
(reads y from `a` directly and applies `thmT` externally).

Then `body_ruleInst (a, recs)` evaluates to
`subT (Pair varCode tT) (thmT y)` — no recs-distrib needed.

**Cost**:  `body_ruleInst` is at line 347 of `BRA/Thm/ThmT.agda`,
inside an `abstract` block, BEFORE `thmT = Rec stepProtoWrapped` at
line 728.  Making `body_ruleInst` reference `thmT` requires either:
  - an Agda `mutual` block enclosing both definitions, or
  - moving `body_ruleInst`'s definition AFTER `thmT` (but the cascade,
    which references `body_ruleInst`, must be defined before `thmT`).

The cleanest fix is a `mutual` block.  Re-prove `body_ruleInst_eval`
(closed form) with the new structure; remove `xShape` from
`body_ruleInst_eval_param`.  The closed form continues to work for
encode/Goedel I.

**Risk**:  encode is the load-bearing function for Goedel I.  If
re-proving `body_ruleInst_eval` introduces any subtle change, Goedel
I's typecheck breaks.  Need careful regression check on
`BRA.Thm.ThmT.WithDispatch.encode`.

**Estimate**:  ~6-10 hours of careful surgery + regression checks.

### Route 2 — Add Deriv axiom

Add to `BRA/Deriv.agda` (or a new shared file) a constructor

```agda
axThmTSub :
  (n : Nat) (tT y codeP : Term) ->
  Deriv (atomic (eqn (ap1 thmT y) codeP)) ->
  Deriv (atomic (eqn (ap1 thmT (ap2 Pair tagCode_ruleInst
                                 (ap2 Pair (reify (code (var n)))
                                           (ap2 Pair y tT))))
                     (ap2 subT (ap2 Pair (reify (code (var n))) tT) codeP)))
```

This is Definition 12 line 2 stated as a primitive — exactly Guard's
treatment.  Justified because it IS the definition.

**Cost**:  `BRA/Deriv.agda` does not import `thmT` (`BRA.Thm.ThmT`) or
`subT` (`BRA.SubT`).  Either:
  - move thmT's and subT's definitions into `Deriv.agda` (huge refactor),
  - or create a new file `BRA/AxThmTSub.agda` after both are defined,
    stating the equation as a postulate (against `--safe`),
  - or add the axiom in `BRA/Thm/ThmT.agda` itself as a new top-level
    Deriv inhabitant.  This works if we can safely add to the Deriv
    constructor list "after the fact" — we cannot, since Deriv is a
    closed inductive type.

The realistic version of this route: make `Deriv` an OPEN definition
parameterised over additional axioms supplied by clients.  Big refactor.

**Estimate**:  ~10-15 hours, plus broader risk to the entire codebase
(everything that pattern-matches on Deriv constructors).

### Route 3 — New tag + body in cascade

Add `tagSb` (a 41st tag) with a `body_sb` that uses
`Lift (Comp thmT (Comp Fst (Comp Snd Snd)))` (or equivalent).
Re-encode K_part etc. to use `tagSb` instead of `tagRuleInst`.

**Cost**:  Add to `BRA/Thm/Tag.agda` (one new tag), `BRA/Thm/TagCodes.agda`
(one new code), and to `BRA/Thm/ThmT.agda`: extend the cascade by one
level (~40 lines of cascade structure), add 40 new `skipAtTag`
invocations (one in each existing dispatch lemma).  Add a new dispatch
lemma `thmTDispSb` analogous to `thmTDispRuleInst`.

`tagSb`'s body would also need to satisfy the same mutual-block
constraint as Route 1 (referencing thmT).  So this route inherits
Route 1's structural complication.

**Estimate**:  ~8-12 hours.

## Recommended route

Route 1 (mutual block) is the closest to faithful Guard transcription.
It treats Definition 12 line 2 as a derivable fact (parametric in y)
rather than as a new axiom, matching Guard's framework.

The mutual-block restructuring is mechanical — Agda accepts mutual
blocks for inductive types and definitions.  The risk is small if
`body_ruleInst_eval` is carefully re-proved.

Recommended:

1. **(1 hr)** Read `BRA/Thm/ThmT.agda:300-1000` (the abstract block
   defining the cascade + body_ruleInst).  Map out exactly which
   definitions need to live inside the `mutual` block (likely:
   stepProto, stepProtoWrapped, all body_X bodies, dispatch, branches,
   thmT itself).
2. **(30 min)** Sketch the new `body_ruleInst` definition with
   `Lift (Comp thmT (Comp Fst (Comp Snd Snd)))`.
3. **(2 hr)** Restructure ThmT.agda to use a `mutual` block; ensure
   the file still typechecks unchanged otherwise.
4. **(2 hr)** Re-prove `body_ruleInst_eval` (closed form) with new
   structure.  Verify encode still works.
5. **(1 hr)** Replace `body_ruleInst_eval_param` with shape-free
   variant.  Drop `xShape` from `thmTDispRuleInst_param` and
   `thmTSubLemma`.
6. **(15 min)** Confirm `BRA.GoedelII` still typechecks.

Then Phase C (`step3_l..step5_l`) is pure mechanical chain
construction (~600-800 LoC, several hours), and Phase D is one line.

## Alternative "stop-gap"

If the structural fix is too risky for one session: ship a hybrid
where K_part is special-cased.  The closure ruleInst-s Con at
`constr5(var 1)` — but the closure could equivalently ruleInst at a
slightly-augmented Term that wraps `var 1` in a Pair-shape.  This
requires introducing an `xShape (var 1)` derivation via... actually,
this doesn't work: `Fst (var 1)` has no axiom.  So the stop-gap is
NOT viable.  The structural fix is mandatory.

## Why this matters

`godelII : Deriv Con -> Deriv bot` is the main deliverable.  Phase A
+ B + the structural fix + Phase C + Phase D delivers it
unconditionally.  Without the fix, Goedel II remains parametric over
the constr5/step5 contracts — which is the current state of
`BRA.GoedelII`.

## Constraints

  * ASCII only.
  * `{-# OPTIONS --safe --without-K --exact-split #-}` everywhere.
  * No postulates, no holes, no with-abstraction, no dot patterns.
  * Route 1 is allowed (mutual blocks are permitted under `--safe`).
  * Route 2 is gated on a design discussion: adding to `Deriv` is a
    significant philosophical change.

## See also

  * `BRA/NEXT-SESSION-THM14-PHASE-C.md` — Phase C plan (consumed once
    the structural fix lands).
  * `BRA/THM14-OBSTRUCTIONS.md` — historical pitfalls.
  * `guard15.pdf` p.16 Definition 12 — Guard's parametric equations.
  * `BRA/Thm/ThmT.agda:347` — `body_ruleInst` definition.
  * `BRA/Thm/ThmT.agda:8511` — `body_ruleInst_eval` closed form.
  * `BRA/Thm/ThmT.agda:8729` — `body_ruleInst_eval_param` (the
    over-engineered parametric form with xShape).
  * `BRA/Thm14SubLemma.agda` — `thmTSubLemma` with xShape (current);
    becomes shape-free after Route 1 lands.
