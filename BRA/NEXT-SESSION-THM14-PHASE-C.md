# Next session — Theorem 14 Phase C (precise blocker + paths)

## Status from previous session (2026-05-02)

Phase A and Phase B of `BRA/NEXT-SESSION-THM14-CONSTR5.md` are
landed and typecheck:

  * **Phase A** — `BRA/Thm14Numerals.agda` (170 LoC, 0.33s).
    Closed encoded witnesses `t_term + t_witness` (transitivity) and
    `t'_term + t'_witness` (ex-falso).

  * **Phase B** — `BRA/Thm14Constr5Final.agda` (266 LoC, 0.61s).
    Closed Fun1 definitions for `f_part, g_part, K_part, h_part,
    constr5` parametric in `r12_th, r12_sub`.

## Phase C blocker — precise diagnosis

**The obstruction is in `body_ruleInst`'s CODEP_extractor design.**

Currently in `BRA/Thm/ThmT.agda:347`:
```agda
body_ruleInst = Fan
                  ARGS_extractor                                       -- works on `a`
                  (Post (Comp (Comp Fst Snd) (Comp Snd Snd)) Pair)     -- works on `recs`
                  subT
```

`ap2 body_ruleInst a recs` evaluates the second arg to
`Fst(Snd(Snd recs)) = Fst(Snd(thmT payT))` where `payT = Pair varCode
(Pair y tT)`.  By the cascade reasoning (varCode is closed Pair-shape),
`thmT payT = Pair (thmT varCode) (thmT (Pair y tT))`.  So we end up at
`Fst(thmT(Pair y tT))` — and to identify this with `thmT y` requires
distributing thmT through `(Pair y tT)`, which requires `Fst y =
Pair _ _` (xShape on y).

**Why no shape on y is available**:  In the closure
(`Thm14Abstract.GodelII.closureToG`), `step5` is applied at `x := var
(suc zero)`.  That `var 1` flows into K_part, h_part, etc. as the
proof-index `y` of the sb-encoded ruleInst trees.  `Fst (var 1)` does
not reduce; no axiom gives it Pair-shape.

**Why the hypothesis doesn't bridge**:  The hypothesis we have is
`thmT (var 1) = cG` (= the antecedent of step5's internal implication,
or the lifted `PrAtX x` Carneiro hypothesis).  This is a fact about
`thmT y`, not about `Fst y`.  Distributing thmT through `(Pair y tT)`
needs xShape on y, which the hypothesis does not provide.

**Why Guard has no analogous blocker**:  Guard's Definition 12 line 2
(`th(4y+1) = sb(KKy, LKy, th(Ly))`) is a parametric defining equation,
stated for ANY `y`, with no shape hypothesis.  Our `thmT` (built via
`Rec stepProtoWrapped`) does NOT satisfy this equation parametrically
in `y` — only for closed `y` whose Fst-shape is derivable.

## Three viable fixes (each substantial)

### Fix 1: Modify `body_ruleInst`'s CODEP_extractor (cleanest mathematically)

Replace
```agda
body_ruleInst =
  Fan ARGS_extractor
      (Post (Comp (Comp Fst Snd) (Comp Snd Snd)) Pair)    -- uses recs
      subT
```
with
```agda
body_ruleInst =
  Fan ARGS_extractor
      (Lift (Comp thmT (Comp Fst (Comp Snd Snd))))         -- uses a + thmT
      subT
```

Then `ap2 body_ruleInst a recs = subT (extracted args) (thmT y)`
where `y = Fst(Snd(Snd a))` — bypassing the recs entirely.

**Closed-form correctness**:  For closed y_h with `thmT (reify y_h) =
reify (codeFormula P)` (encode's recursion), the new extractor still
gives `thmT (reify y_h)` — same value as the old extractor.  So
`thmTDispRuleInst` (closed form) and `encodeRich` continue to work.

**Parametric correctness**:  For open `y` with hypothesis `thmT y =
codeP`, the new extractor gives `thmT y` directly, then
`ruleTrans (cong refl ...) hyp` rewrites to `codeP`.  No shape on y
needed.

**Blocker**:  `body_ruleInst` is defined at line 347 of `ThmT.agda`,
inside the abstract block, BEFORE `thmT = Rec stepProtoWrapped` at
line 728.  The current scoping has `thmT` reference `body_ruleInst`
via the cascade, so making `body_ruleInst` reference `thmT` creates
a cycle.

**Resolution**:  Use a `mutual` block (or equivalent forward
declaration) for `body_ruleInst` and `thmT`.  Agda accepts this
because Fun1/Fun2 expressions are finite — the cycle is at the level
of NAMES, not at the level of values (which both unfold to finite
syntax trees).

**Cost**:  Restructure the abstract block around lines 100-1000 of
`ThmT.agda` to put `thmT` and `body_ruleInst` in a mutual block.
Re-prove `body_ruleInst_eval` (closed form) with the new structure
(~50 LoC change).  Re-derive `thmTDispRuleInst_param` without xShape
(~80 LoC).  Total: ~200-300 LoC of careful surgery.

### Fix 2: Add `axThmTSub` as a Deriv axiom

Add to `BRA.Deriv.agda`:
```agda
axThmTSub :
  (n : Nat) (tT y codeP : Term) ->
  Deriv (atomic (eqn (ap1 thmT y) codeP)) ->
  Deriv (atomic (eqn
    (ap1 thmT (ap2 Pair tagCode_ruleInst
                (ap2 Pair (reify (code (var n))) (ap2 Pair y tT))))
    (ap2 subT (ap2 Pair (reify (code (var n))) tT) codeP)))
```

This is Definition 12 line 2 stated as a Deriv constructor.  Justified
because it IS the definition (Guard treats it as primitive).

**Blocker**:  `Deriv.agda` currently imports only `BRA.Term` and
`BRA.Formula`.  `thmT` lives in `BRA.Thm.ThmT` and `subT` in
`BRA.SubT`.  To state the axiom in `Deriv.agda`, we'd need to move
`thmT`'s and `subT`'s definitions into `Deriv.agda` (or create a
shared base file).  Major refactor.

**Alternative**:  Define `axThmTSub` as an `abstract` lemma in a new
file `BRA/AxThmTSub.agda` after thmT/subT are defined.  But the body
must DERIVE it — which is the original blocker (impossible without
xShape).  So this option requires either (a) postulating (against
`--safe`), (b) leveraging Fix 1, or (c) reverting to the closed-form
restriction.

### Fix 3: Add new tag + body to the cascade

Add `tagSb` (a 41st tag) with `body_sb` using the Lift+Comp(thmT, ...)
form.  Re-encode K_part etc. to use `tagSb` instead of `tagRuleInst`.

**Cost**:  Add to `BRA/Thm/Tag.agda` (one new tag), `BRA/Thm/TagCodes.agda`
(one new code), and to `BRA/Thm/ThmT.agda`: extend the cascade by one
level (~40 lines), add 40 new `skipAtTag` invocations (one in each
existing dispatch lemma), prove the new dispatch lemma.  Total:
~500-800 LoC.

## Recommended path

**Fix 1** is the cleanest and most faithful to Guard's mathematics.
The resolution (mutual block) is straightforward in principle but
requires care in re-proving body_ruleInst_eval.

**Fix 2** is conceptually simplest (just add an axiom) but blocked by
the import structure of `Deriv.agda`.

**Fix 3** is most conservative (no existing code changes) but most
verbose.

I recommend Fix 1.  Estimated effort: one focused 4-6 hour session
for the surgery + re-proofs.  After Fix 1 lands, Phase C's
`step3_l..step5_l` chain follows mechanically (~600-800 LoC) and Phase
D is one line.

## What's already in place

  * `BRA/Thm14Numerals.agda` (committed 60b3119) — Phase A.
  * `BRA/Thm14Constr5Final.agda` (committed 8b11e3b) — Phase B.
  * `BRA/Th14Constr5.agda` — `step1_l, step2_l` already lifted.
  * `BRA/SbRuntime.agda` — `Df_F1_I_runtime` exhibits the pattern
    with closed proof-index (where xShape is trivially derivable).
  * `BRA/Thm14Step4Test.agda` — confirms the xShape obstruction
    exists for parametric proof-index.

## Constraints

  * ASCII only.
  * `{-# OPTIONS --safe --without-K --exact-split #-}` .
  * No postulates, no holes, no with-abstraction, no dot patterns.
  * Fix 1 is allowed (it does not add new Deriv axioms; only
    restructures existing code).
  * Fix 2 would require lifting "no new Deriv axioms" — discuss
    before committing.

## See also

  * `BRA/THM14-OBSTRUCTIONS.md` — historical pitfalls.
  * `BRA/Thm/ThmT.agda:347` — `body_ruleInst` definition.
  * `BRA/Thm/ThmT.agda:8511` — `body_ruleInst_eval` (closed form,
    needs re-proof under Fix 1).
  * `BRA/Thm/ThmT.agda:8729` — `body_ruleInst_eval_param` (parametric
    with xShape, removed under Fix 1 in favor of shape-free version).
  * `BRA/Thm/ThmT.agda:8838` — `thmTDispRuleInst_param` (the
    xShape-requiring lemma; replaced under Fix 1).
