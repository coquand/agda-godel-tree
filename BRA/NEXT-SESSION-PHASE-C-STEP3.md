# Next session — DELIVER step 3 of Theorem 14 (REVISED 2026-05-03 v2)

## Goal

**Complete step 3 of Guard's Theorem 14 proof in BRA, by the end of the
next session.**  Specifically: produce `step3_l : (x : Term) ->
Deriv (PrAtX x imp atomic (eqn (ap1 thmT (ap1 g_part x))
(Pair (encoded_th_x_at x) encoded_sub_ii)))`.

## Approach: direct derivation (NOT general lemma)

For step 3 we have ONE concrete instance:
  * t_formula = `(x_0 = x_2) imp ((x_1 = x_2) imp (x_0 = x_1))` — known.
  * Substituents (Approach A, post-inversion):
    - var 2 → `sub_ii_subst` (= reify (code cG)).
    - var 1 → `encoded_sub_ii` (= reify (code (sub i i))).
    - var 0 → `encoded_th_x_at x` (= Pair tagAp1 (Pair codeF1_thmT (cor x))).
  * Expected canonicalized RHS: known explicit Pair structure (worked out
    by hand-trace below).

**Don't write a general `subT_into_codeFormula` lemma**.  Don't
parametrize over arbitrary Formula.  Just derive the substitution-equality
directly for THIS instance, applying existing lemmas at known arguments.

Each step is a one-line invocation; no structural recursion on Formula.

## Read first (in order)

1. **This file**.
2. `BRA/PHASE-C-INVESTIGATION-2026-05-02.md` — diagnosis of why earlier
   sessions stalled (sb-order inversion + substituent mis-design).
3. `BRA/PHASE-C-SIDE-BY-SIDE-2026-05-02.md` — Guard-vs-BRA comparison.
4. `BRA/Thm14Constr5Final.agda` — `f_part`, `g_part`, `g_part_inner`,
   `D_thmT`, `D_sub_at_ii`, `encoded_th_x`, `encoded_sub_ii`,
   `sub_ii_subst`.
5. `BRA/Th14Step3.agda` — `step3_pre`, `f_part_unfold`,
   `f_part_inner1_unfold`, `f_part_inner2_unfold`, `encoded_th_x_at`,
   `encoded_th_x_unfold`.
6. `BRA/Th14SubTPushthrough.agda` — `subT_codeFormula_imp` (line 503),
   `subT_codeFormula_atomic` (line 1023), `subT_codeFormula_neg`,
   `subT_node_match` (line 151), `subT_node_no_match` (line 280),
   `subT_dist_Pair_tagImp` (line 639), `subT_dist_Pair_inner_via_TreeEq`
   (line 835), `treeEq_codeVar_tag*Head` (lines 422+), `natEqIsFalse_of_diff`
   (line 382).
7. `BRA/Th14Constr5.agda` — `step1_l` (line 148), `step2_l` (line 158)
   for the mp dispatch arguments.

## Status

  * Goedel I, Theorems 12, 13: complete.
  * Points 1, 2 of Theorem 14: complete (`step1_l`, `step2_l`).
  * `step3_pre`: gives `thmT(f_part x) = subT^3 (...) (reify (codeFormula t_formula))`.
  * Approach A: substituents are Guard-faithful encoded mixed-form Pairs.
  * sb-order inversion: var 0 outermost, so cor x is introduced LAST
    (only at varCode0T MATCH positions).
  * All files typecheck.

## What we need to derive (the target)

```agda
step3_canon : (x : Term) -> Deriv (atomic (eqn
  (ap2 subT (ap2 Pair varCode0T (encoded_th_x_at x))
    (ap2 subT (ap2 Pair varCode1T encoded_sub_ii)
      (ap2 subT (ap2 Pair varCode2T sub_ii_subst)
        (reify (codeFormula t_formula)))))
  target_form))
```

where `target_form` (the canonicalized explicit Pair structure) is:

```
Pair (reify tagImp)                                  -- outer imp
  (Pair (Pair (encoded_th_x_at x) sub_ii_subst)         -- antec1 (= D_thmT match)
        (Pair (reify tagImp)                            -- inner imp
              (Pair (Pair encoded_sub_ii sub_ii_subst)   -- antec2 (= D_sub match)
                    (Pair (encoded_th_x_at x) encoded_sub_ii))))  -- conseq
```

Then `step3_l` chains step3_pre + step3_canon + 2 mp dispatches.

## Direct-derivation plan (CONCRETE STEPS)

### Stage A: innermost subT — `subT (vc2, sub_ii_subst) (reify (codeFormula t_formula))`

t_formula structure: `(eq02) imp ((eq12) imp (eq01))`.

**A.1**: Apply `subT_codeFormula_imp 2 sub_ii_subst eq02 (eq12 imp eq01)`.
  Gives `Pair tagImp (Pair (subT eq02_code) (subT (eq12 imp eq01)_code))`.

**A.2**: Apply `subT_codeFormula_atomic 2 sub_ii_subst x0 x2` to canonicalize
  subT applied to `reify (codeFormula eq02)`.  Gives `Pair (subT (reify (code x0))) (subT (reify (code x2)))`.

**A.3**: Resolve `subT (vc2, sub_ii_subst) (reify (code (var 0)))`:
  = `varCode0T` (preserved).  Use `subT_node_no_match 2 sub_ii_subst tagVar lf`
  with witness `natEqIsFalse_of_diff 2 0 refl` (after some bridging) +
  closed canonicalization through `nd tagVar lf` Tree.

**A.4**: Resolve `subT (vc2, sub_ii_subst) (reify (code (var 2)))`:
  = `sub_ii_subst` (match).  Use `subT_node_match 2 sub_ii_subst`.

**A.5**: Apply `subT_codeFormula_imp 2 sub_ii_subst eq12 eq01` recursively
  for the inner imp.

**A.6**: Repeat A.2-A.4 patterns for eq12 (var 1, var 2) and eq01 (var 0, var 1).
  Specifically need:
    * subT vc2 (reify (code (var 1))) = varCode1T preserved.
    * subT vc2 varCode2T = sub_ii_subst (match).
    * subT vc2 varCode0T = varCode0T preserved.
    * subT vc2 varCode1T = varCode1T preserved.

**Output of Stage A** (named `stage_a` : Deriv ...):
```
subT (vc2, sub_ii_subst) (reify (codeFormula t_formula))
  =
Pair tagImpT (Pair (Pair varCode0T sub_ii_subst)
                   (Pair tagImpT (Pair (Pair varCode1T sub_ii_subst)
                                       (Pair varCode0T varCode1T))))
```

### Stage B: middle subT — `subT (vc1, encoded_sub_ii) (Stage A's RHS)`

The target is now NOT of `reify (codeFormula F)` form — it's a partially-substituted
Pair structure.  Use `subT_dist_Pair_tagImp` + `subT_dist_Pair_inner_via_TreeEq`
with closed TreeEq witnesses.

**B.1**: Apply `subT_dist_Pair_tagImp 1 encoded_sub_ii ...` on the outer
  Pair tagImpT (...).  Result: `Pair tagImpT (subT (vc1, encoded_sub_ii) (...))`.

**B.2**: Push subT through the inner `Pair (Pair varCode0T sub_ii_subst) (Pair tagImpT ...)` via
  `subT_dist_Pair_inner_via_TreeEq` with witness `TreeEq vc1 (Pair _ _) = falseT`.

**B.3-B.6**: Apply subT to each child:
  * subT (vc1) (Pair varCode0T sub_ii_subst): distribute, then subT vc1 varCode0T = preserved,
    subT vc1 sub_ii_subst = preserved (closed canonicalization through reify (code cG)).
    Result: Pair varCode0T sub_ii_subst.
  * subT (vc1) (Pair tagImpT ...): distribute via subT_dist_Pair_tagImp, recurse.

**Output of Stage B** (named `stage_b` : Deriv ...):
```
subT (vc1, encoded_sub_ii) (Stage A's RHS)
  =
Pair tagImpT (Pair (Pair varCode0T sub_ii_subst)
                   (Pair tagImpT (Pair (Pair encoded_sub_ii sub_ii_subst)
                                       (Pair varCode0T encoded_sub_ii))))
```

### Stage C: outer subT — `subT (vc0, encoded_th_x_at x) (Stage B's RHS)`

Same pattern as Stage B but with substituent encoded_th_x_at x.  This is
the ONLY layer where cor x is introduced — at varCode0T MATCH positions.

**C.1-C.7**: Push subT through, distributing at each Pair node.  At varCode0T
  leaves: MATCH, substitute encoded_th_x_at x.  At varCode1T leaves: preserved.
  At sub_ii_subst / encoded_sub_ii: preserved (closed reify).

**Output of Stage C** (= step3_canon's RHS):
```
Pair tagImpT (Pair (Pair (encoded_th_x_at x) sub_ii_subst)
                   (Pair tagImpT (Pair (Pair encoded_sub_ii sub_ii_subst)
                                       (Pair (encoded_th_x_at x) encoded_sub_ii))))
```

### Composing: step3_canon

```agda
step3_canon : (x : Term) -> Deriv (atomic (eqn (RHS of step3_pre) target_form))
step3_canon x =
  let stage_a = ...  -- closed (no x dependency at this stage's RHS)
      stage_b = ...  -- closed
      stage_c = ...  -- depends on x via encoded_th_x_at x
      bridge_b = congR subT (vc1_pair encoded_sub_ii) stage_a
      bridge_c = congR subT (vc0_pair (encoded_th_x_at x)) (ruleTrans bridge_b stage_b)
  in ruleTrans bridge_c (... apply stage_c)
```

Or (simpler): build the chain inside-out using ruleTrans.

### step3_l (~80 LoC)

```agda
step3_l : (x : Term) ->
  Deriv (PrAtX x imp
          atomic (eqn (ap1 thmT (ap1 g_part x))
                      (ap2 Pair (encoded_th_x_at x) encoded_sub_ii)))
step3_l x =
  let
    -- 1. Lift step3_pre under PrAtX x.
    pre_lifted = liftAxiom (PrAtX x) (step3_pre x)

    -- 2. Lift step3_canon under PrAtX x.
    canon_lifted = liftAxiom (PrAtX x) (step3_canon x)

    -- 3. Compose: thmT(f_part x) = (target_form).
    fpart_canon = liftedRuleTrans (PrAtX x) ... pre_lifted canon_lifted

    -- 4. Inner mp at g_part_inner: y1T = f_part x, y2T = D_thmT x.
    --    d1 = fpart_canon (= thmT(f_part x) = Pair tagImp (Pair antec1 inner_rest)).
    --    Need shape: Fst (f_part x) = Pair x' y1' for some x', y1'.
    --      Fst (f_part x) = tagCode_ruleInst (closed) — derive via f_part_unfold + axFst.
    --    Output: thmT(g_part_inner x) = inner_rest.
    --    Use thmTDispMp_param at the encoded mp form.
    --    Bridge thmT(g_part_inner_encoding) = thmT(g_part_inner x) via cong1 thmT (g_part_inner_unfold x).
    inner_mp = ...

    -- 5. Outer mp at g_part: y1T = g_part_inner x, y2T = D_sub_at_ii x.
    --    d1 = inner_mp's output (= Pair tagImp (Pair antec2 conseq)).
    --    Output: thmT(g_part x) = conseq = Pair (encoded_th_x_at x) encoded_sub_ii.
    outer_mp = ...

  in outer_mp
```

## Auxiliary lemmas to build first

These are the leaf-level closed canonicalizations needed in Stages A-C:

### Aux 1: `subT_preserves_varCode_at_diff_n` for SPECIFIC n, k

For our case we need only the closed instances:
```agda
sub_v2_v0 : (A : Term) -> Deriv (atomic (eqn (subT (vc2_pair A) varCode0T) varCode0T))
sub_v2_v1 : (A : Term) -> Deriv (atomic (eqn (subT (vc2_pair A) varCode1T) varCode1T))
sub_v1_v0 : (A : Term) -> Deriv (atomic (eqn (subT (vc1_pair A) varCode0T) varCode0T))
sub_v0_v1 : (A : Term) -> Deriv (atomic (eqn (subT (vc0_pair A) varCode1T) varCode1T))
sub_v0_v2 : (A : Term) -> Deriv (atomic (eqn (subT (vc0_pair A) varCode2T) varCode2T))
sub_v1_v2 : (A : Term) -> Deriv (atomic (eqn (subT (vc1_pair A) varCode2T) varCode2T))
```

Each is ~15-25 LoC: subT_node_no_match at the outer (nd tagVar (natCode k))
with `natEqIsFalse_of_diff` witness, then closed canonicalization through
the inner Tree structure.

### Aux 2: `subT_preserves_sub_ii_subst` and `subT_preserves_encoded_sub_ii`

```agda
sub_v2_subii : Deriv (atomic (eqn (subT (vc2_pair sub_ii_subst) sub_ii_subst) sub_ii_subst))
   -- and similar for vc1, vc0 / encoded_sub_ii
```

These close-canonicalize sub_ii_subst (= reify (code cG)) under any
varCode_n substitution — since cG contains no varCode_n at any leaf
(cG is a closed reify-of-Tree representing the encoded formula G,
which has var 1 inside but at the codeFormula level — see below).

**WAIT**: cG = reify (codeFormula G) = reify (codeFormula (not (atomic (eqn (thmT (var 1)) (sub i i))))).
This contains var 1 INSIDE codeFormula G as a varCode1T leaf!  So
`subT (vc1, _) (reify (codeFormula G))` would HIT this varCode1T.

But we substitute on `sub_ii_subst = reify (code cG)` — which is the
CODE OF cG, ONE LEVEL HIGHER.  At this level, cG is treated as a
NUMERAL (a closed Tree), not as a Formula with var 1 free.  So
`code cG` is a Tree with no `nd tagVar (natCode k)` children at the
top level (it's `nd tagAp1 (nd codeF1_reify (code (codeFormula G)))`
or similar — closed structure all the way down at the meta level).

So `sub_ii_subst` is closed at the outer level (no varCode_n leaves
extensionally), and subT preserves it.  ~30 LoC each.

### Aux 3: `subT_preserves_encoded_th_x_at` (NOT NEEDED for step 3)

The substituent encoded_th_x_at x has cor x at the leaf — but it's
only USED as a substituent (Snd of vc0_pair), never as a TARGET, by
the Approach A design.  So we never need subT applied to it.

## Total estimated effort

- Aux 1 (6 specific varCode preservation lemmas): ~120 LoC.
- Aux 2 (3 closed-reify preservation lemmas): ~90 LoC.
- Stage A: ~50 LoC.
- Stage B: ~40 LoC.
- Stage C: ~40 LoC.
- step3_canon composition: ~20 LoC.
- step3_l: ~80 LoC.

**Total ~440 LoC.**

But this is concrete, mechanical work — each lemma is a small fixed
chain of subT_node_no_match / subT_node_match / closed TreeEq witnesses.
No recursion, no general parameters.

## PITFALLS — read before coding

1. **Don't try to write a general `subT_into_codeFormula` lemma.**
   Direct derivation is more concrete and shorter for this one instance.

2. **Don't introduce cor x as content of any subT TARGET**.  Cor x
   appears ONLY as substituent in encoded_th_x_at x, used as the
   var-0 substituent in Stage C.  All TreeEq comparisons in stages
   A, B are CLOSED.

3. **encoded_sub_ii = reify (code (sub i i))** — closed reify-of-Tree.
   subT preservation lemmas work because of this canonical form.

4. **sub_ii_subst = reify (code cG)** — also closed reify-of-Tree.
   Same reasoning.

5. **subT_node_no_match needs `Eq` (meta-level) treeEq mismatch**.
   For varCode comparisons use `natEqIsFalse_of_diff`.  For
   tag-vs-varCode mismatches use the existing `treeEq_codeVar_tag*Head`
   lemmas.

6. **At each subT_node_no_match application, the children's subT-applications
   need further canonicalization**.  Be ready to nest.  Don't try to
   "close" with one application.

7. **Verify each Aux lemma compiles solo** before composing into Stages.
   Per `feedback_guard_fast_typecheck`.

8. **Stages A, B, C should each be in their own private `where` block**
   in the same file or split across files for clarity.  Aim for
   <1s solo typecheck per stage.

## Soundness check

If subT correctly encodes substitution (which subDef proves for closed
reified inputs), then ALL the canonicalization equalities here are
derivable.  If any specific Aux/Stage lemma gets stuck on a TreeEq
that doesn't fire, that means the substituent / target arrangement
is wrong (not Approach-A-compliant).  Fix the arrangement, don't fight
the canonicalization.

## After step 3

Once step3_l is built and typechecks:
  * Apply same pattern (3 stages of direct derivation + mp dispatches)
    to:
    - step4_l_canonical (1 sb-step + 1 canonicalization, much shorter).
    - h_part_canon + h_part_l (2-deep instead of 3-deep, so ~70% the work).
    - step5_l (2 outer mp dispatches, no subT canonicalization).
  * Plug into BRA.GoedelII.Compose for godelII.

## Constraints (unchanged)

  * ASCII only.
  * `--safe --without-K --exact-split` everywhere.
  * No postulates, no holes, no with-abstraction, no dot patterns.
  * No new Deriv constructors.
  * No new ThmT lemmas.
  * Per-file solo typecheck under 1s with cache, <10s fresh.

## Done when

`step3_l` exists and typechecks.  We have step 3 of Guard's Theorem 14
proof reproduced in BRA.

## Files to create / modify

- CREATE `BRA/Th14Step3Canon.agda` — replaces the current scaffold;
  contains Aux 1, Aux 2, Stages A/B/C, step3_canon.
- EXTEND `BRA/Th14Step3.agda` — add step3_l after step3_pre.
- (Possibly create) `BRA/Th14SubTLeaf.agda` — if Aux 1 + Aux 2 lemmas
  warrant their own file (~200 LoC).

## Files NOT touched

- BRA/Thm/ThmT.agda
- BRA/Th14SubTPushthrough.agda (existing; just used)
- BRA/Thm12.agda, BRA/Thm13.agda
- BRA/GoedelII.agda
- BRA/SubT.agda
- BRA/Thm14Constr5Final.agda (Approach A redesign already done)
