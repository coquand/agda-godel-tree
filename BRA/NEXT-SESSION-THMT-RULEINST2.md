# thmT.tagRuleInst2 dispatch — Stages 1-5 DONE

## Status

All five stages of the `thmT`-extension for simultaneous double substitution
typecheck in BRA. `BRA/Thm/ThmT.agda` types in **6.9s**.

* **Stage 1**: `tagRuleInst2 = suc tagAxIfLfNL` (= 44) in `BRA/Thm/Tag.agda`.
* **Stage 2**: `BRA/Thm/Parts/RuleInst2.agda` — `encRuleInst2` and `outRuleInst2`.
* **Stage 3**: `body_ruleInst2 : Fun2`, `tagCode_ruleInst2`,
  `checkTag_ruleInst2` in ThmT abstract block.
* **Stage 4**: cascade — `branch_axIfLfNL` falls through to `next_axIfLfNL` →
  `branch_ruleInst2`. `hitAtTag` call sites updated.
* **Stage 5** (this commit):
  * `BRA/Sb2.agda`: added `codedSubst2 : Tree -> Tree -> Tree -> Tree -> Tree -> Tree`
    (Tree-valued analog of `codedSubstT2`), `reify_boolCase` helper,
    `codedSubstT2_reify` (Eq commutation), and `subTDef2` (Tree-args
    wrapper around `subTDef_term2`).
  * `BRA/Thm/ThmT.agda`: added `body_ruleInst2_eval` (~150 LoC) and
    `thmTDispRuleInst2` (~120 LoC, 43-skip cascade + hit + body_eval).

## thmTDispRuleInst2 signature

```agda
thmTDispRuleInst2 : (xA xB : Nat) (tA tB : Term) (P : Formula)
                    (y_h : Tree) (y_h' : Term) ->
  Deriv (atomic (eqn (ap1 Fst (reify y_h)) (ap2 Pair O y_h'))) ->
  Deriv (atomic (eqn (ap1 thmT (reify y_h))
                     (reify (codeFormula P)))) ->
  Eq (codeFormula (substF xA tA (substF xB tB P)))
     (codedSubst2 (code tA) (code tB) (code (var xA)) (code (var xB))
                  (codeFormula P)) ->
  Deriv (atomic (eqn (ap1 thmT (reify (encRuleInst2 xA xB tA tB y_h)))
                     (reify (outRuleInst2 xA xB tA tB P))))
```

The third argument is the **codeCommutesFormula2** Eq: codeFormula commutes
with simultaneous double substitution at the formula level. This is the
load-bearing meta-level fact whose proof was deferred to the caller.

## Design choice: parametric on codeCommutesFormula2

Rather than implementing the full `codeCommutesFormula2 : (xA xB : Nat) (tA
tB : Term) (P : Formula) -> ...` lemma (~600 LoC of mutual induction
mirroring `BRA/CodeCommutes.agda`), the dispatch lemma takes the Eq as an
explicit hypothesis. Concrete callers discharge it however suits them:

* For closed inputs (concrete xA, xB, tA, tB, P), Agda often computes
  the Eq by `refl`.
* For the Th12_F1_Fst use case (substituents are `cor v1`, `cor v2` for
  fresh v1, v2), the substitution is non-overlapping (codes of cor have
  no `code(var xA)` subtrees), so a "swap-disjoint" lemma proves the Eq
  in 1-2 lines via two applications of `codeCommutesFormula`.
* If a fully universal `codeCommutesFormula2` is needed later, it can
  be written in `BRA/CodeCommutes2.agda` and supplied at the call site.

## Use in Theorem 12 for Fst/Snd Pair-cases

The intended use: at Pair-case of Theorem 12 for shape-dispatched
primitives, encode the runtime application of `axFst v1 v2` (or
`axSnd v1 v2`) as `encRuleInst2 0 1 (cor v1) (cor v2) (encAxFst)`.
Then `thmTDispRuleInst2` reduces:

```
thmT (reify (encRuleInst2 0 1 (cor v1) (cor v2) encAxFst))
  = reify (codeFormula (substF 0 (cor v1) (substF 1 (cor v2) axFstFormula)))
```

The output is the codeFormula of the doubly-substituted axFst, which
after further `cor` reductions (`corOfPair`, `corOfFstPair`) yields the
asymmetric Theorem 12 form `codeFTeq1Asym Fst (ap2 Pair v1 v2)`.

## File changes in this commit

* `BRA/Thm/Tag.agda` — `tagRuleInst2`.
* `BRA/Thm/Parts/RuleInst2.agda` — NEW (encRuleInst2, outRuleInst2).
* `BRA/Sb2.agda` — `codedSubst2`, `reify_boolCase`, `codedSubstT2_reify`,
  `subTDef2`.
* `BRA/Thm/ThmT.agda` — `tagCode_ruleInst2`, `body_ruleInst2`,
  `checkTag_ruleInst2`, `branch_ruleInst2`, `next_axIfLfNL`; updated
  `branch_axIfLfNL`; updated 2 `hitAtTag` call sites; new
  `body_ruleInst2_eval` + `thmTDispRuleInst2`.

## What's next (separate session)

1. **Th12_F1_Fst at Pair-case**: build `Df_F1_Fst_pair` using
   `encRuleInst2`, prove the codeCommutes Eq for the specific
   substituents, glue with `corOfPair` + `corOfFstPair` to reach
   `codeFTeq1Asym Fst (ap2 Pair v1 v2)`.
2. **Th12_F1_Fst full**: combine `Th12_F1_Fst_at_lf` + the new Pair-case
   via `fromBaseAndPair`.
3. **Th12_F1_Snd full**: mirror.
