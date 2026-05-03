# Phase C: Guard vs BRA — side-by-side chain comparison

## Setup (both share)

  * `j` = Goedel sentence's numeral; `cG = reify (codeFormula G)` in BRA;
    `j = "th(x_1) ≠ sub(i,i)"` in Guard, with `i = "j"` (the diagonalising
    numeral).
  * `bot` = `atomic (eqn O O)` in BRA; `"0 = 1"` in Guard.
  * `t_term, t_formula` = transitivity numeral / formula
    (`(x_0 = x_2) ⊃ . (x_1 = x_2) ⊃ x_0 = x_1`).
  * `t'_term, t'_formula` = ex-falso numeral / formula
    (`(x_0 = x_1) ⊃ . (x_0 ≠ x_1) ⊃ 0 = 1`).
  * `Pr(x) = atomic (eqn (ap1 thmT x) cG)` in BRA;
    `th(x) = j` in Guard.

## The five chain steps

| # | Guard (p.16-17) | BRA analog | Status |
|---|---|---|---|
| 1 | `th(x) = j ⊢ th(Dth(x)) = "th(x_) = j"` by Theorem 13 with f=th, y=j | `step1_l x : Pr(x) ⊢ thmT(D_thmT x) = encoded "thmT(num x) = sub_ii_subst"` via Theorem 12 + cong1 cor + corOfReify | NOT YET BUILT (planned in Th14Constr5; trivial via Theorem 13) |
| 2 | `th(sub(i,i)) = "sub(i,i) = j"` by Theorem 13 (closed) | `step2_l : thmT(D_sub_at_ii) = encoded "sub(i,i) = sub_ii_subst"` (closed) via Theorem 12 + closed corOfReify | NOT YET BUILT |
| 3a (sb) | `th(fx) = "(th(x_) = j) ⊃ ((sub(1,1) = j) ⊃ (th(x_) = sub(1,1)))"` by 3 sb's on transitivity numeral t | `step3_pre x : thmT(f_part x) = subT^3(...) (reify(codeFormula t_formula))` | DONE (post-inversion) |
| 3a' (canon) | (no analog — Guard's sb returns the encoded formula directly) | `step3_canon`: push subT^3 through Pair structure to expose explicit Pair tagImp | NOT YET BUILT — but should now work after inversion |
| 3b (mp) | `th(x) = j ⊢ th(gx) = "th(x_) = sub(1,1)"` via 2 mp's | `step3_l x : Pr(x) ⊢ thmT(g_part x) = encoded "th(cor x) = sub_ii_subst"` via 2 thmTDispMp_param dispatches | NOT YET BUILT |
| 4 (sb) | `th(x) = j ⊢ th(K(x)) = "th(x_) ≠ sub(1,1)"` by 1 sb on j | `step4_l x : Pr(x) ⊢ thmT(K_part x) = subT(vc1, cor x) cG`. Then `step4_l_canonical`: bridge via subT_codeFormula_neg + atomic | step4_l DONE; step4_l_canonical NOT YET BUILT |
| 4' (sb) | `th(h(x)) = "(th(x_) = sub(1,1)) ⊃ ((th(x_) ≠ sub(1,1)) ⊃ (0 = 1))"` by 2 sb's on t' | `h_part_pre x` (closed) + `h_part_canon`: push subT^2 through to explicit Pair | h_part_pre DONE (post-inversion); canon NOT YET BUILT |
| 4'' (mp) | (Guard combines step 4 + 4' implicitly into step 5) | `h_part_l x : Pr(x) ⊢ thmT(h_part x) = canonicalized encoded formula` via 2 thmTDispMp_param dispatches | NOT YET BUILT |
| 5 (mp) | `th(x) = j ⊢ th(constr5(x)) = "0 = 1"` via 2 outer mp's | `step5_l x : Pr(x) ⊢ thmT(constr5 x) = reify(codeFormula bot)` via 2 thmTDispMp_param dispatches | NOT YET BUILT |
| Closure | (Guard's final paragraph: substitution + Theorem 11 contradiction) | `closureToG : Deriv Con -> Deriv bot` via GoedelII.Compose | DONE — abstracted, just needs constr5 + step5 plug-in |

## The core asymmetry — where Guard's chain doesn't have BRA's obligation

### Guard's sb axiom (Exercise 24 [4], p.14):

```
sb(J("A", n), "P") = "S^x_n_A P|"
```

The RHS `"S^x_n_A P|"` IS the Gödel number of the substituted formula, expressed
as a closed numerical expression in terms of "A" (which may itself contain
`num x` symbolically as a sub-expression).

**This means Guard's sb returns the substituted encoded formula DIRECTLY**, with
no intermediate "stuck" form.  When the substituent A = "th(x_underlined)"
contains `num x`, the result `"S^..._A P|"` contains `num x` at the substituted
positions — but the SHAPE of the result (J-pair tree with numerical leaves)
is completely determined.

### BRA's subT (`BRA/SubT.agda`):

```
subT = RecP stepSubT
stepSubT = Fan checkEqSubT contSubT IfLf
checkEqSubT = ... TreeEq ...  -- compares varCode head with target
contSubT = ... -- distributes recursively if no match
```

`subT (Pair varCode tT) target` recurses into `target`'s structure via
`axRecPNd`, calling `TreeEq` at each internal node to decide match vs distribute.

**When TreeEq's first arg has shape `cor x` (= `ap1 cor x`, neither lf nor Pair),
the comparison stalls** — no defining equation of TreeEq fires, IfLf doesn't fire,
and the whole subT computation halts symbolically.

### The exact BRA step that introduces the obligation

**Step 3a (sb chain delivery)**: thmT(f_part x) = subT^3(...).

In Guard: `th(fx)` IS the encoded formula `"(th(x_) = j) ⊃ ..."`, expressed
as a closed numeric expression.  No further "canonicalization" needed because
Guard's sb directly produces the encoded formula.

In BRA: thmT(f_part x) = `subT^3 (codeFormula t_formula)`.  This is a
SYMBOLIC expression that REPRESENTS the encoded formula but doesn't
extensionally REDUCE to it without further canonicalization steps using
`subT_codeFormula_imp` / `subT_dist_Pair_*` / etc.

**This is where the extra obligation enters.**  Guard's sb axiom is
"intensional" enough that the result IS the encoded formula; ours requires
additional canonicalization.

## Why this used to be a problem (pre-inversion)

In our PRE-INVERSION design, the chronological subT order was:
  1. subT (vc0, cor x) on closed `codeFormula t_formula` → introduces cor x as
     CONTENT of the result.
  2. subT (vc1, sub_ii) on a target now containing cor x at varCode0T
     positions → recurses into Pairs containing cor x → TreeEq stalls
     on `TreeEq tagVarT (cor x)` → BLOCKER.
  3. subT (vc2, i) — would also blocker.

So the canonicalization obligation from step 3a' WAS unrecoverable: subT
couldn't push through Pairs containing cor x as content.

## Why the inversion dissolves it

Post-inversion, the chronological subT order is:
  1. subT (vc2, i) on closed `codeFormula t_formula` → CLOSED canonicalized
     result A (no cor x).
  2. subT (vc1, sub_ii) on A (CLOSED) → CLOSED canonicalized result B.
  3. subT (vc0, cor x) on B (CLOSED) — applies LAST to a closed
     canonicalized target.  Recurses into B's CLOSED Pair structure;
     all TreeEq comparisons are between closed Trees on both sides
     (no cor x ANYWHERE except as the substituent that gets placed at
     varCode0T leaves).  Result: B with cor x at varCode0T leaves.
     NO FURTHER subT applied.

For the OUTER subT (vc0, cor x) applied to closed canonicalized B:
  * `TreeEq vc0 (any-subterm-of-B)` is between two CLOSED Pair structures
    (cor x is NOT in B's tree — it's only the substituent).  All TreeEq
    comparisons fully canonicalize via axTreeEqNN cascades to closed
    mismatch / match results.
  * Match cases substitute cor x at the leaves; non-match cases distribute
    and recurse into closed children.
  * No symbolic stall.

So the canonicalization obligation from step 3a' IS now dischargeable using
`subT_codeFormula_imp` / `subT_dist_Pair_tagImp` / `subT_dist_Pair_inner_via_TreeEq`
+ closed TreeEq witnesses.

## Bottom line

**Guard's chain has no extra obligation because Guard's sb axiom returns the
encoded formula directly.  Ours has it because subT is a recursive function
that requires canonicalization to "deliver" the encoded form.**

**The inversion makes this canonicalization possible** because cor x (the only
symbolic substituent) is introduced LAST — at varCode0T leaves of an already
closed canonicalized structure — so subT never has to recurse THROUGH cor x.

## Remaining concrete work (~6-8 lemmas)

Now that the architectural blocker is dissolved:

  * `step1_l` + `step2_l` (~80 LoC): Theorem 13 instantiations + cong1 cor +
    corOfReify bridges.  No canonicalization needed (just lift Theorem 12
    outputs).
  * `step3_canon` (~150 LoC): push subT^3 through `reify(codeFormula t_formula)`
    using `subT_codeFormula_imp` (3x) + `subT_codeFormula_atomic` (4x for the
    inner equations).  All TreeEq comparisons are closed.
  * `step3_l` (~100 LoC): two `thmTDispMp_param` dispatches with d1 from
    `step3_canon`'s output.
  * `step4_l_canonical` (~80 LoC): push subT through cG via
    `subT_codeFormula_neg` + `subT_codeFormula_atomic`.
  * `h_part_canon` + `h_part_l` (~200 LoC): mirror step3_canon + step3_l for
    h_part.
  * `step5_l` (~100 LoC): two outer `thmTDispMp_param` dispatches.
  * Plug-in to `GoedelII.Compose` (~10 LoC).

Total estimate: ~720 LoC, all using existing infrastructure (no new
primitives, no new Deriv constructors, no new ThmT lemmas needed).
