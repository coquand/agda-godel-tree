# Next session — Theorem 14 Phase C continuation (V2)

## Read first (in order)

  1. **This file** (you're reading it) — current state + work plan.
  2. `BRA/NEXT-SESSION-PHASE-C-CONTINUE.md` — V1 plan.  Items now
     landed are noted in the Status section below; remaining items
     (lifted-step3_l, lifted-h_part_l, step5_l, plug-in) carry forward.
  3. `BRA/COR-AT-SB-LOAD-BEARING.md` — cor's role at sb-substitution
     sites.
  4. `CLAUDE.md` (project root) — ASCII-only / explicit-arg conventions.

## Status (2026-05-02 session — Opus 4.7 1M, second pass)

V1 of Phase C delivered: thmTDispMp_param, step3_pre, step4_l, the
core subT-canonicalization toolkit (subT_codeFormula_imp,
subT_dist_Pair_tagImp, subT_dist_Pair_inner_via_TreeEq,
subT_node_match, subT_preserves_tagImp).

**This session continues V1 with:**
  * V1 (A) — `subT_codeFormula_atomic` + `subT_codeFormula_neg`
    (+ `subT_preserves_tagNeg`) added to `Th14SubTPushthrough.agda`.
  * V1 (C2 partial) — `BRA/Th14Step4Canonical.agda` delivers
    `step4_l_neg` exposing the tagNeg head.
  * **NEW** `BRA/Th14HUnfolds.agda` — h_part Pair unfold lemmas
    (h_part_inner1 / h_part_skel / h_part_thxLayer / h_part).
  * **NEW** `BRA/Th14StepHPre.agda` — closed h_part_pre (2-sb-step
    prefix on t'_term).
  * **NEW** `BRA/Th14GPartUnfolds.agda` — g_part_inner / g_part Pair
    unfold lemmas.
  * `BRA/GoedelII.agda` re-exports `G_unfold` for downstream consumers.

**Strict invariant honoured:** all touched / new files typecheck
under 1 second solo (with cache).  Confirmed:
  * `Th14SubTPushthrough.agda` — 0.14s solo
  * `Th14Step4Canonical.agda` — 0.67s solo
  * `Th14HUnfolds.agda`        — 0.67s solo
  * `Th14StepHPre.agda`        — 0.67s solo
  * `Th14GPartUnfolds.agda`    — 0.69s solo
  * `GoedelII.agda`            — 0.40s solo

## Delivered files this session

  1. **`BRA/Th14SubTPushthrough.agda`** (1043 LoC, +130 this session) —
     three new lemmas:
       * `subT_preserves_tagNeg` — closed passthrough for tagNeg.
       * `subT_codeFormula_neg` — outer no-match split on (tagNeg, codeFormula P).
       * `subT_codeFormula_atomic` — outer no-match split on (code a, code b).

  2. **`BRA/GoedelII.agda`** — added `G_unfold` to public exports.

  3. **`BRA/Th14Step4Canonical.agda`** (185 LoC) — `step4_l_neg`:
     bridges step4_l 's RHS through G_unfold + subT_codeFormula_neg
     to expose the tagNeg head.

  4. **`BRA/Th14HUnfolds.agda`** (245 LoC) — h_part_inner1_unfold,
     h_part_skel_unfold, h_part_thxLayer_unfold, h_part_unfold.
     Mechanical Comp2 Pair tower unfolds.

  5. **`BRA/Th14StepHPre.agda`** (115 LoC) — `h_part_pre`: closed
     2-sb-step prefix on  t'_term .  Mirrors `step3_pre` (3-sb on
     t_term ).

  6. **`BRA/Th14GPartUnfolds.agda`** (108 LoC) — g_part_inner_unfold,
     g_part_unfold.  Pair-of-Comp2 unfolds for the g_part chain.

## What's still remaining

The lifted versions (under PrAtX x antecedent) and the final mp-chain
combination.  All require canonicalizing the post-subT result to a
`Pair tagImp ...` form for thmTDispMp_param 's input.

### (V1 C1) `step3_l` — file `BRA/Th14Step3.agda` (extend)  [~250 LoC]

The lifted version of step3_pre under PrAtX x with two
`thmTDispMp_param` dispatches threading the canonicalization chain.

**Substantive obstacle:** the post-subT^3 form
`subT^3 (reify (codeFormula t_formula))` needs to be canonicalized
to `Pair tagImp (Pair pT qT)` for the inner mp dispatch.

Plan:
  * Apply `subT_codeFormula_imp` on the innermost subT:  exposes the
    outer  Pair tagImp (Pair X Y)  shape (X = subT(...) (reify (codeFormula eq02)),
    Y = subT(...) (reify (codeFormula (eq12 imp eq01)))) .
  * Apply `subT_dist_Pair_tagImp` on the middle subT:  preserves
    tagImp head.
  * Apply `subT_dist_Pair_inner_via_TreeEq` to push the middle subT
    INTO the inner (Pair X Y).  Requires deriving
    `Deriv (TreeEq varCode1T (Pair X Y) = falseT)`  parametrically
    in X, Y.  By axTreeEqNN: TreeEq (Pair tagVar (natCode 1)) (Pair X Y)
    = IfLf (TreeEq tagVar X) (Pair (TreeEq (natCode 1) Y) (Pair O O)).
    For X = subT(varCode0, cor x)(reify (codeFormula eq02)) — its outer
    structure (after subT_codeFormula_atomic-style reduction) IS a Pair
    `Pair (cor x) varCode1T`-ish form, so TreeEq with tagVar mismatches
    at the head.  Need a structural lemma (~30 LoC) showing this for
    parametric x.
  * Same applies for the outer subT.

Once canonicalization is done, two thmTDispMp_param applications
(g_part_inner mp + g_part mp) chain.  Use `g_part_inner_unfold` /
`g_part_unfold` from Th14GPartUnfolds.agda for shape obligations.

### (V1 C3) `h_part_l` — file `BRA/Th14StepH.agda` (new)  [~250 LoC]

Mirror step3_l on h_part_pre + h_part_inner1_unfold +
h_part_skel_unfold + h_part_thxLayer_unfold + h_part_unfold (all
already provided in Th14HUnfolds.agda + Th14StepHPre.agda).  2-sb-step
chain → 2 mp dispatches.  Same canonicalization obstacle as step3_l.

### (V1 C4) `step5_l` — file `BRA/Th14Step5.agda` (new)  [~250 LoC]

Combine `step3_l + step4_l_neg + h_part_l` via two outer
`thmTDispMp_param` dispatches.  Use `constr5_unfold` /
`constr5_inner_unfold` (write analogous to g_part_unfold) for shape.

The two outer mp 's at constr5 layer:
  * Inner: y1T = h_part(x), y2T = g_part(x).  Need
    `thmT(h_part x) = Pair tagImp (Pair P_enc R_enc)`  where  P_enc
    matches step3_l's RHS (= encoded "th(cor x) = sub(i,i)") and
    R_enc = `Pair tagImp (Pair (encoded "not P") (encoded "0=1"))` .
    Output: `thmT(constr5_inner x) = R_enc`.
  * Outer: y1T = constr5_inner(x), y2T = K_part(x).  Need
    `thmT(constr5_inner x) = Pair tagImp (Pair (Pair tagNeg P_enc) (encoded "0=1"))`.
    Output: `thmT(constr5 x) = encoded "0=1" = reify (codeFormula bot)`.

### (V1 C5) Plug-in — extend `BRA/GoedelII.agda`  [~10 LoC]

```agda
module Final =
  BRA.GoedelII.Compose
    (Th14Constr5Final.constr5 r12_th r12_sub)
    (Th14Step5.Th14Step5.step5_l r12_th r12_sub)

godelIIUnconditional :
  (r12_th  : Thm12_F1_Result thmT)
  (r12_sub : Thm12_F2_Result sub) ->
  Deriv Con -> Deriv bot
godelIIUnconditional r12_th r12_sub = Final.godelII
```

## Pitfalls (LEARNED across V1 + V2 sessions — read before coding)

  1. **`KT` only reduces on `reify <closed-tree>`.**  See V1.

  2. **Don't change the abstract block in `BRA/Thm/ThmT.agda` unless
     necessary.**  See V1.

  3. **When `subT` doesn't reduce, check the second-arg shape.**  See V1.

  4. **Internal-implication form needs `axImpRefl` for self-hypotheses.**
     See V1.

  5. **Solo typecheck with cache.**  Target < 1s.  See V1.

  6. **Abstract constants stop reduction** — `j`, `cG`, `G`,
     `codeFormula G` are abstract (BRA/Thm11Diagonal.agda's abstract
     block).  Outside, Agda will NOT unfold them.  Use `G_unfold`
     to bridge.  See `Th14Step4Canonical.agda:90 cG_to_neg_form`.

  7. **For step3_l / h_part_l canonicalization**: the
     `subT_dist_Pair_inner_via_TreeEq` step requires deriving the
     TreeEq-falseT witness PARAMETRICALLY in the inner Pair-content
     (because the post-subT inner form is parametric in x, hence
     doesn't reduce at the meta level).  This is the V2 session's
     blocker for the lifted versions; address it via a structural
     lemma that exploits the post-subT_codeFormula_atomic form.

## Estimated effort (revised after this session)

  * (C1) `step3_l`           : ~250 LoC.  Builds on subT canonicalization
                                 + thmTDispMp_param twice.
  * (C3) `h_part_l`          : ~250 LoC.  Mirrors step3_l with one fewer
                                 sb-step.
  * (C4) `step5_l`           : ~250 LoC.  Two outer mp dispatches.
  * (C5) Plug-in             : ~10 LoC.

Total: ~760 LoC remaining.  ~1.5 focused sessions.

**The substantive infrastructure is now complete.**  All canonicalization
tools, all Pair-unfold lemmas, both closed sb-prefixes (step3_pre +
h_part_pre), and the canonicalized step4_l_neg are in place.

## Files NOT touched

(Unchanged.)

## Constraints honoured

  * ASCII only.
  * `{-# OPTIONS --safe --without-K --exact-split #-}` everywhere.
  * No postulates, no holes, no with-abstraction, no dot patterns.
  * No new Deriv constructors.
  * Per-file solo typecheck under 1s with cache.

## Done when

`BRA/GoedelII.agda` exports
```
godelIIUnconditional :
  (r12_th  : Thm12_F1_Result thmT)
  (r12_sub : Thm12_F2_Result sub) ->
  Deriv Con -> Deriv bot
```
that does not take any Thm 14 contracts.  `agda --safe BRA/GoedelII.agda`
succeeds.

## See also

  * `BRA/NEXT-SESSION-PHASE-C-CONTINUE.md` — V1 plan (consumed).
  * `BRA/COR-AT-SB-LOAD-BEARING.md` — cor's specification use sites.
  * `BRA/Th14SubTPushthrough.agda` — full subT canonicalization toolkit.
  * `BRA/Th14Step3.agda` — step3_pre (closed; needs lifted step3_l).
  * `BRA/Th14Step4.agda` — step4_l (closed-RHS).
  * `BRA/Th14Step4Canonical.agda` — step4_l_neg with tagNeg head exposed.
  * `BRA/Th14HUnfolds.agda` — h_part Pair-of-Comp2 unfolds.
  * `BRA/Th14StepHPre.agda` — closed h_part_pre (2-sb-step prefix on t').
  * `BRA/Th14GPartUnfolds.agda` — g_part Pair-of-Comp2 unfolds.
  * `BRA/Thm14Constr5Final.agda` — f_part / g_part / K_part / h_part /
    constr5 definitions.
  * `BRA/Thm14Numerals.agda` — t_term / t_witness / t'_term / t'_witness.
  * `BRA/Th14Constr5.agda` — step1_l / step2_l (lifted Theorem 13).
