# TreeEq Phase 4 — path forward via Theorem 12 for IfLf

## Earlier "blocker" claim was wrong

An earlier version of this doc claimed the cor-on-IfLf opacity was a
genuine obstacle that required new axioms.  That was wrong.  The
correct path uses Theorem 12 for IfLf as a chain-Df slot, which the
existing infrastructure already supports.

## The key insight

`thmTDispRuleTrans_param` (`BRA/Thm/ThmT.agda:10635`) requires a
shape proof **only on `y1T`**, not on `y2T`.  This means we can use
an **opaque BRA-applied form** as `y2T` in a chain composition,
provided we have a Deriv giving its thmT-image.

In particular: `y2T = ap2 D_IfLf (TreeEq v1 v3)(Pair (TreeEq v2 v4)(Pair O O))`
is opaque (no axIfLf reduction at variable args), but
`Th12_F2_IfLf` (`BRA/Th12IfLf.agda`) instantiated via `ruleInst` at
those Terms gives:

```
thmT(D_IfLf X Y) = Pair (mkAp2T cifLf (cor X)(cor Y))(cor (IfLf X Y))
```

where `X = TreeEq v1 v3`, `Y = Pair (TreeEq v2 v4)(Pair O O)`.  Used
as `d2` in `thmTDispRuleTrans_param`, this composes with a `y1T`
ending at `mkAp2T cifLf (cor (TreeEq v1 v3))(cor (Pair (TreeEq v2 v4)(Pair O O)))`
to yield `Pair (LHS_target)(cor (IfLf (TreeEq v1 v3)(Pair ...)))`.

The outer BRA bridge `cor (IfLf ...) = cor (TreeEq pp pp)` follows
from `cong1 cor (ruleSym (axTreeEqNN v1 v2 v3 v4))`.

## Why this works

- `Th12_F2_IfLf` is the universal Theorem 12 for IfLf (already
  proved via `D_correct2_IfLf_univ` using nested ruleIndBT).  It
  applies to *any* (X, Y) including opaque ones.
- The chain Df composition via `tagCode_ruleTrans` works at the
  encoded-equation layer; `cor`'s opacity on applied IfLf at variable
  args is no problem because we never derive a BRA equation between
  `mkAp2T cifLf (cor _)(cor _)` and `cor (IfLf _ _)` — instead we
  transit through the encoded equation Term `thmT(D_IfLf X Y)`.
- The pattern is exactly analogous to Th12RecP/RecPPairCase where
  `ih_s_bra` is supplied as a parameter.  For TreeEq's NN case, the
  caller-supplied bridge IS `Th12_F2_IfLf` at the right Terms.

## Foundational piece delivered

`BRA/Th12TreeEqDfFun.agda` (101 LoC, typechecks):

- `Df_F2_TreeEq : Fun2 = Fan (Lift (KT tagCode_ruleTrans)) D_TreeEq Pair`
- `Df_F2_TreeEq_reduce_outer x v` : ap2 Df_F2_TreeEq x v BRA-reduces
  to `Pair tagCode_ruleTrans (ap2 D_TreeEq x v)`.
- `shape_at x v` : `Fst (ap2 Df_F2_TreeEq x v) = tagCode_ruleTrans`.
- `Df_F2_TreeEq_closed` : closure under substF2.

This is the standard outer-wrapping pattern used by Df_F1_Rec_zs and
Df_F2_RecP_s.  However, *for the simple basePP_imp construction
described above, this wrapping is not strictly required* — see the
"Simpler path" section below.  The wrapping is preserved for
uniformity and future use (e.g., if we want IH packaging records).

## Simpler path (no wrapping needed)

The existing `P_Th12_TreeEq` (`BRA/Th12TreeEqBaseLN.agda:39`) uses
`D_TreeEq` directly.  After `ruleIndBT2`'s substF reduction, the IHs
in basePP_imp have form:

```
h1 : Deriv (atomic (eqn (ap1 thmT (ap2 D_TreeEq (var v1)(var v3)))
                         (codeFTeq2_TreeEq (var v1)(var v3))))
```

This is *exactly* what `thmTDispRuleTrans_param` expects as `d2` with
`y2T = ap2 D_TreeEq (var v1)(var v3)`.  No shape proof required on
y2T.  So we can use the IH-Deriv directly without packaging.

## Concrete plan for basePP_imp

**Step 1**: redesign `D_TreeEq_NN_fun` to emit, at NN input, a chain
Df of the form `Pair tagCode_ruleTrans (Pair Df_step1 Df_step2)`,
where:

- `Df_step1` is a chain Df Term whose thmT-image is `Pair LHS_target M`,
  with `LHS_target = mkAp2T cf2 (cor (Pair v1 v2))(cor (Pair v3 v4))`
  and `M = mkAp2T cifLf (cor (TreeEq v1 v3))(cor (Pair (TreeEq v2 v4)(Pair O O)))`.

- `Df_step2 = ap2 D_IfLf (TreeEq v1 v3)(Pair (TreeEq v2 v4)(Pair O O))`
  as an opaque Fun2-applied Term.

`Df_step2` is constructible as a Fun2 expression: e.g.,
`Post (Comp2 D_IfLf treeEq_v1v3_extr ifLf_arg2_extr) Pair` (~50 LoC
including reduction lemma).

`Df_step1` is a multi-step chain Df.  Its construction needs:

  - axTreeEqNN encoded dispatch at `(cor v1, cor v2, cor v3, cor v4)`.
  - corOfPair-based bridges for the LHS slot (mkAp2T pCT (cor _)(cor _) → cor (Pair _ _)).
  - IH1 / IH2 substitution at the encoded sub-mkAp2T-cf2 slots inside
    the encoded RHS form.  This uses `thmTDispCongL_param`
    (`BRA/Thm/ThmT.agda:12155`) with `y_h_T = ap2 D_TreeEq v1 v3`
    (the IH-Df, opaque) and image = `h1` directly.

  ⚠ Note: thmTDispCongL_param requires shape on y_h_T.  Since
  `Fst (ap2 D_TreeEq v1 v3)` is opaque (no IfLf cascade fires at
  variables), this would fail.  *This is where the wrapping trick
  matters.*

**Two ways to fix the shape requirement**:

**(a) Use Df_F2_TreeEq instead of D_TreeEq in P_Th12_TreeEq.**
  - Reformulate P_Th12_TreeEq to use Df_F2_TreeEq (the wrapped form
    delivered in this session).
  - IH-Df becomes `ap2 Df_F2_TreeEq v1 v3` whose Fst BRA-reduces to
    `tagCode_ruleTrans` (via `shape_at`).
  - All baseLL/LN/NL must be re-derived in the new formulation; this
    is mechanical but ~150 LoC of eqSubst plumbing.
  - Current `Th12TreeEqBaseLN.agda` and `Th12TreeEqBaseNL.agda` need
    to be updated.

**(b) Avoid thmTDispCongL_param entirely, use only thmTDispRuleTrans_param.**
  - Compose the chain Df via repeated ruleTrans steps where each
    step has a Pair-shape `y1T` (with provable shape via axFst on
    tag) and an opaque-but-image-known `y2T`.
  - The IHs feed into the chain via `y2T = ap2 D_TreeEq v1 v3` with
    image = `h1`.
  - This sidesteps the cong-substitution and may be simpler in
    practice.

Recommend **(b)** as the simpler implementation path; keep
`Df_F2_TreeEq` as a future extensibility point.

## Estimated scope

- `D_TreeEq_NN_fun` redesign (cor-encoded args, multi-step chain
  output): ~250 LoC.
- Reduction lemmas for the new D_TreeEq_NN_fun at NN input: ~200 LoC.
- `Df_step1` chain Df construction (multi-step ruleTrans nesting):
  ~400 LoC.
- `Df_step2` extractor construction + reduction lemma: ~80 LoC.
- basePP_imp body (BRA Deriv chain, ~10-15 ruleTrans steps): ~200 LoC.
- Lift to ruleIndBT2-imp form (axK + B_combinator + lifted equational
  rules): ~100 LoC.

Total: ~1200-1400 LoC.  Realistic budget: 2 focused sessions.

## What NOT to do

- Do NOT add `axCorIfLf` / `axCorTreeEq` axioms.  They are
  inconsistent universally.  See the
  `feedback_no_treeeq_inconsistent_cor_axiom` rule (added this
  session).
- Do NOT try to derive `mkAp2T cifLf (cor X)(cor Y) = cor (IfLf X Y)`
  as a BRA Deriv.  It's not BRA-derivable.  The chain Df bridge
  through `Th12_F2_IfLf` is the only sound route.

## Files inspected this session

- `BRA/Th12RecP.agda` (819 LoC) — Th12RecP pattern reference.
- `BRA/Th12RecUniv.agda` (1500 LoC) — toIH1Rec packaging mechanism.
- `BRA/Th12RecPUniv.agda` (1470 LoC) — wrapped Df_F2_RecP_s, IfLf-form
  bridge, basePair structure.
- `BRA/Thm12/Parts/IfLf.agda` (990 LoC) — D_IfLf, bridges,
  D_correct2_IfLf_univ, codeFTeq2_IfLf.
- `BRA/Thm12/Parts/TreeEq.agda` (829 LoC) — D_TreeEq construction,
  bridges, parametric NN_pt.
- `BRA/Th12IfLf.agda` (42 LoC) — Th12_F2_IfLf re-export.
- `BRA/Thm/ThmT.agda` (~16500 LoC) — thmTDispRuleTrans_param,
  thmTDispCong{L,R,1}_param signatures.
- `BRA/Deriv.agda` (297 LoC) — ruleIndBT2 contract, IfLf/TreeEq
  axioms.

## Files delivered this session

- `BRA/Th12TreeEqDfFun.agda` (101 LoC) — Df_F2_TreeEq wrapping +
  outer reduction + shape_at + closure.  Typechecks.
- This document.
