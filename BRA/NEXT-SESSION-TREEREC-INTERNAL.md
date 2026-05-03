# Next session — close `thm12_F2 (treeRec f s)` into a true closed term

## The global theorem this session closes

After this session, `thm12_F1` and `thm12_F2` (mutually recursive in
`BRA/Thm12.agda`) become genuinely closed Agda terms with the types:

```agda
thm12_F1 : (f : Fun1) -> Thm12_F1_Result f
thm12_F2 : (g : Fun2) -> Thm12_F2_Result g

record Thm12_F1_Result (f : Fun1) : Set where
  field
    Df    : Fun1
    proof : (x : Term) ->
      Deriv (atomic (eqn (ap1 thmT (ap1 Df x)) (codeFTeq1 f x)))

record Thm12_F2_Result (g : Fun2) : Set where
  field
    Dg    : Fun2
    proof : (x v : Term) ->
      Deriv (atomic (eqn (ap1 thmT (ap2 Dg x v)) (codeFTeq2 g x v)))
```

Reading this as Guard's Theorem 12: for every BRA functor (unary `f` or
binary `g`), there exists a witness `Df` / `Dg` such that for all Term
arguments,

```
  thmT (Df x)    = code-of-the-equation  "(f x) = cor (f x)"
  thmT (Dg x v)  = code-of-the-equation  "(g x v) = cor (g x v)"
```

— where `codeFTeq1 / codeFTeq2` is the Pair (encoded-LHS) (cor-of-RHS)
representation of an atomic equation in BRA's metatheory:

```agda
codeFTeq1 f x =
  ap2 Pair
    (ap2 Pair (reify tagAp1) (ap2 Pair (reify (codeF1 f)) (ap1 cor x)))
    (ap1 cor (ap1 f x))

codeFTeq2 g x v =
  ap2 Pair
    (ap2 Pair (reify tagAp2)
              (ap2 Pair (reify (codeF2 g)) (ap2 Pair (ap1 cor x) (ap1 cor v))))
    (ap1 cor (ap2 g x v))
```

This is the binary tree-based transcription of Guard's "Theorem 12 for
primitive recursive functions" (unary case) and his extension to `R f g`
(binary case, our `treeRec`) needed for Goedel II's diagonalisation.

Today, all cases of `thm12_F1` / `thm12_F2` are internal **except**
`treeRec`, which is still parametric over six `FromBridges` items.  This
session closes those parameters — at which point both `thm12_F1` and
`thm12_F2` stand as closed terms of the types above, and Theorem 12
holds unconditionally in the Agda formalisation.

## Success criterion (read this FIRST)

This task is **complete** when both of the following hold:

### (A) The type of `thm12_F2 (treeRec f s) .proof` is exactly:

```agda
(p x : Term) ->
  Deriv (atomic (eqn (ap1 thmT (ap2 D2_treeRec_fs p x))
                     (codeFTeq2 (treeRec f s) p x)))
```

i.e. unfolding `codeFTeq2`:

```agda
(p x : Term) ->
  Deriv (atomic (eqn
    (ap1 thmT (ap2 D2_treeRec_fs p x))
    (ap2 Pair
      (ap2 Pair (reify tagAp2)
                (ap2 Pair (reify (codeF2 (treeRec f s)))
                          (ap2 Pair (ap1 cor p) (ap1 cor x))))
      (ap1 cor (ap2 (treeRec f s) p x)))))
```

This is Guard's Theorem 12 for `R f g`, transcribed to our binary
tree-based BRA with `cor` in place of `num`:
**`thmT (D f s p x) = code-of-the-equation "(treeRec f s) p x = cor ((treeRec f s) p x)"`**.

### (B) `thm12_F2 (treeRec f s)` is a closed Agda term

Its `where`-block uses only `rf = thm12_F1 f` and `rs = thm12_F2 s`
(plus possibly structural closure lemmas like `Fun1_closed`,
`Fun2_closed`).  **No** `FromBridges` parameter is consumed by the
`treeRec` case.  Concretely, after the work, none of these names should
appear in the where-clause or in `FromBridges`:

* `apf_corLemma_for`
* `D2_treeRec_NN_fun`
* `D_correct2_treeRec_NN_pt`
* `D2_treeRec_NN_fun_closed_for`
* `treeRec_fs_closed_for`
* `treeRec_xeq1`

A final `grep -E "apf_cor|treeRec_xeq1|D2_treeRec_NN|treeRec_fs_closed_for"
BRA/Thm12.agda` should return nothing (or only stale comments).

### Both (A) and (B) are required.

Type-correct but parametric is not done; closed term but with the wrong
type is not done either.  The two together = success.

## Goal

Make `thm12_F2 (treeRec f s)` in `BRA/Thm12.agda` a closed Agda term —
eliminate every `treeRec`-specific `FromBridges` parameter.  The result
type stays as prescribed:

```agda
thm12_F2 (treeRec f s) : Thm12_F2_Result (treeRec f s)
```

with

```agda
record Thm12_F2_Result (g : Fun2) : Set where
  field
    Dg    : Fun2
    proof : (x v : Term) ->
      Deriv (atomic (eqn (ap1 thmT (ap2 Dg x v)) (codeFTeq2 g x v)))
```

This is Guard's Theorem 12 statement for `R f g`, transcribed to our
binary tree-based BRA with `cor` in place of `num`.  Do not change the
result type, do not change `Thm12_F1_Result` / `Thm12_F2_Result`, and
do not touch any of the other Fun2 cases.  The only case under analysis
is `treeRec`.

## What's already in place (DO NOT redo)

From prior sessions, the substitution-cascade infrastructure is solved:

* `BRA/SubstClosure.agda` — `subst_reify` and `substF1_KT_of_reify`
  (proved by `Tree` induction).
* `BRA/Cor.agda` — `stepCor_closed` and `cor_closed`.
* `BRA/Thm12/Parts/TreeRec.agda` — `D2_treeRec_fs_closed` derived from
  the user-supplied `D2_treeRec_NN_fun_closed` plus the new lemmas
  above; schema-form `D_correct2_treeRec_fs_univ : Deriv P_Th12_treeRec`
  via `ruleIndBT`; universal-form wrapper `D_correct2_treeRec_fs (p x : Term)
  (xeq1 : ...) -> Deriv ...`.

This typechecks today.  But the wrapper still depends on five
`FromBridges` parameters (lines 99–138 of `BRA/Thm12.agda`):

1. `D2_treeRec_NN_fun : Fun1 -> Fun2 -> Fun2`
2. `D_correct2_treeRec_NN_pt` — pointwise correctness at `(p, Pair a b)`.
3. `D2_treeRec_NN_fun_closed_for` — substitution-closure helper.
4. `treeRec_fs_closed_for` — substitution-closure of `treeRec f s` itself.
5. `apf_corLemma_for` — leaf-case bridge.
6. `treeRec_xeq1` — the substitution-closure on `x` introduced by
   `ruleInst` in the universal-form wrapper.

These six must all be eliminated.

## Why "no bridges" is achievable

The user's clarification (after several false starts):

* Internal `bridgeO` / `bridgeN` style helper functions inside the proof
  are fine — they're sound structural lemmas.
* The constraint is on the **interface**: `thm12_F2 (treeRec f s)` must
  be a closed term, not parametric over `FromBridges` items.
* The proof can use `thm12_F1 f .proof` and `thm12_F2 s .proof` (the
  genuine recursive IHs), `ruleIndBT` cross-IHs, all BRA primitives
  (`axTreeRecLf`, `axTreeRecNd`, `parDispAxTreeRecLf`, `parDispAxTreeRecNd`,
  `parDispRuleTrans`, `parEncCongL` / `parEncCongR`, etc.), and any
  internal helper lemmas.

## The plan

### Step 1: Restructure `D2_treeRec_fs` to use the IHs directly

Currently the leaf case in `Parts/TreeRec.agda` uses
`parEncAxTreeRecLf fT sT (cor p)` and bridges via `apf_corLemma`.
The cleaner construction:

```
ap2 D2_treeRec_fs p O = parEncRuleTrans (parEncAxTreeRecLf fT sT (cor p))
                                          (ap1 Df_f p)
```

where `Df_f = r_f.Df` from `thm12_F1 f`.  Then via `parDispRuleTrans`
applied to:

* `parDispAxTreeRecLf fT sT (cor p)` — gives `thmT (parEncAxTreeRecLf …)
  = parOutAxTreeRecLf …` whose Snd is `Pair tagAp1 (Pair fT (cor p))`.
* `r_f.proof p` — gives `thmT (Df_f p) = codeFTeq1 f p` whose Fst is the
  same `Pair tagAp1 (Pair fT (cor p))` and Snd is `cor (f p)`.

`parDispRuleTrans` composes these (the matching `u2 = u3` pattern) and
yields `thmT (D2_treeRec_fs p O) = Pair (encoded-LHS-treeRec) (cor (f p))`.

A final `congR Pair _ (ruleSym (cong1 cor (axTreeRecLf f s p)))` bridges
`cor (f p)` to `cor (ap2 (treeRec f s) p O)`, giving `codeFTeq2 (treeRec f s)
p O` exactly.

The shape proof `Fst y1 = Pair _ _` for `parDispRuleTrans`'s shape
hypothesis is `axFst tagCode_axTreeRecLf _` — `tagCode_axTreeRecLf` is a
closed natCode-encoded Term, so this reduces.

This eliminates `apf_corLemma_for`.

### Step 2: Step case via `ruleIndBT` with cross-IHs

Currently the step case uses parametric `D_correct2_treeRec_NN_pt`.
Replace with internal proof at `(p, Pair (var v1) (var v2))` using:

```
ap2 D2_treeRec_fs p (Pair t u) =
  parEncRuleTrans
    (parEncAxTreeRecNd fT sT (cor p) (cor t) (cor u))
    (parEncRuleTrans
       (parEncCongR s <encoded-pair-with-cross-IH-t-substituted> ...)
       (parEncRuleTrans
          (parEncCongR s <encoded-pair-with-cross-IH-u-substituted> ...)
          (ap2 Df_s (Pair p (Pair t u)) (Pair (treeRec f s p t) (treeRec f s p u)))))
```

where `Df_s = r_s.Dg` from `thm12_F2 s`.  The chain mirrors `Comp2.agda`
and `Fan.agda` style: each `parDispCongR s` substitutes one of the
cross-IH outputs (`Snd` of `thmT (D2_treeRec_fs p t)` and `… p u`)
into the encoded `s`-application slot.

The cross-IHs come from `ruleIndBT`'s step antecedents:
`Deriv (substF zero (var v1) P_Th12_treeRec)` and `… v2 …`.  They must
be **consumed**, not discharged via `axK` as the current code does at
`Parts/TreeRec.agda` line ~595.

The `parDispAxTreeRecNd` step has the encoded `s`-application using
syntactic `codeF`-form (the `parOutAxTreeRecNd` second component, lines
40–62 of `BRA/Thm12/Param/AxTreeRecNd.agda`).  `thm12_F2 s .proof X V`
uses `cor`-form (via `codeFTeq2`).  Bridging requires showing the two
encodings agree at the relevant points — this is structural via `Pair
tagAp2 _` shape matching, plus `corOfReify` if any closed sub-Term
appears in syntactic form.  Watch for this carefully; it's the source
of most of the Pair-case complexity in `Comp2.agda` / `Fan.agda`.

### Step 3: Eliminate `treeRec_xeq1`

Currently the universal wrapper `D_correct2_treeRec_fs` uses
`ruleInst zero x` then `ruleInst (suc zero) p`, picking up
`subst (suc zero) p x = x` as a closure obligation.

Solution: do the `ruleInst`s in the **other order** —
`ruleInst (suc zero) p` first, then `ruleInst zero x`.  Then no
`subst` walks `x` (since `var 0` only appears at the inducted-on slot,
not introduced by `var 1 → p` substitution).

If reversing the order doesn't cleanly eliminate the closure, fall
back to: take an internal closure derivation from the structure of
`D2_treeRec_fs` (since `D2` is built from `Df_f`, `Df_s`, and closed
combinators, its substitution-closure is structurally provable —
probably via `Df_f_closed` and `Df_s_closed` derived from the structure
of `thm12_F1 f` / `thm12_F2 s` outputs, both of which produce only
closed Funs).

### Step 4: Internal closure proofs for `Df_f` and `Df_s`

Add `closure of any thm12_F1 / thm12_F2 output Fun` as a generic lemma
(or derive from the structure of each Fun's `Df`).  These are needed
for the new `D2_treeRec_fs_closed` (since `D2`'s structure now includes
`Df_f` and `Df_s`).

This eliminates `D2_treeRec_NN_fun_closed_for` and `treeRec_fs_closed_for`.

### Step 5: `treeRec_fs_closed`

`treeRec f s` itself appears inside `codeFTeq2_treeRec_fs`.  The closure
on it follows from `f_closed` and `s_closed` (closures of the Fun1/Fun2
arguments to treeRec).  These are the substitution-closures of the
abstract `f`, `s` — supplied at the `Construction` level.

For `f`, `s` being arbitrary Fun1/Fun2 arguments (not constructed by
`thm12_F1` / `thm12_F2`), we need them closed.  This means the
`Construction` module takes `f_closed` and `s_closed` as parameters —
but these can be supplied from `Thm12.agda`'s `where`-clause via a
single generic lemma `Fun1_closed : (g : Fun1) -> ...` (provable by
structural recursion on `Fun1` — its grammar contains no `var`, so
substitution is the identity by case-analysis on the Fun1 constructor).
Same for `Fun2_closed`.

Add these two structural lemmas (probably 10 lines each) to
`BRA/SubstClosure.agda` or directly inside `Term.agda`.

### Step 6: Update `Thm12.agda`'s `where`-clause

```agda
thm12_F2 (treeRec f s) = mkR2 R.D2_treeRec_fs R.D_correct2_treeRec_fs
  where
    rf = thm12_F1 f
    rs = thm12_F2 s
    module R = BRA.Thm12.Parts.TreeRec.Construction
                 f s
                 (Thm12_F1_Result.Df rf) (Thm12_F1_Result.proof rf)
                 (Thm12_F2_Result.Dg rs) (Thm12_F2_Result.proof rs)
```

(plus possibly the `f_closed`, `s_closed` args from the generic
structural lemmas).  No `D2_treeRec_NN_fun`, no `apf_corLemma_for`,
no `treeRec_xeq1`, no closure parameters.

Drop those parameters from `FromBridges` (lines 99–138 of
`BRA/Thm12.agda`).

## Files to edit

1. `BRA/SubstClosure.agda` — add `Fun1_closed`, `Fun2_closed` (structural
   substitution-closure for any Fun1, Fun2).  ~30 LoC.
2. `BRA/Thm12/Parts/TreeRec.agda` — restructure `Construction` module:
   * Replace `apf_corLemma`, `D2_treeRec_NN_fun`, etc. with
     `Df_f`, `proof_f`, `Df_s`, `proof_s`.
   * Restructure `D2_treeRec_fs` to use `Df_f`, `Df_s`.
   * Rewrite `D2_treeRec_fs_reduce_O`, `D2_treeRec_fs_reduce_Nd` for the
     new structure.
   * Rewrite `bridgeO` to use `parDispRuleTrans` + `proof_f`.
   * Add `bridgeNd` for the step case using `parDispAxTreeRecNd` +
     `parDispCongR` chains + `proof_s` + cross-IH usage.
   * Rewrite `D2_treeRec_fs_closed` for the new structure (depends on
     `Df_f_closed`, `Df_s_closed` from `Fun1_closed` / `Fun2_closed`).
   * Re-thread the `ruleIndBT` step proof to **consume** cross-IHs
     instead of `axK`-discharging.
   * Re-derive the universal `(p, x) -> Deriv ...` wrapper without
     `xeq1`.
3. `BRA/Thm12.agda` — drop the six `treeRec`-specific `FromBridges`
   parameters; update `thm12_F2 (treeRec f s)` clause.

## Estimated size

Total new code: 800–1500 LoC, mostly in `Parts/TreeRec.agda`.

## Verification targets

* `~/.cabal/bin/agda-2.9.0 BRA/SubstClosure.agda` — green
* `~/.cabal/bin/agda-2.9.0 BRA/Thm12/Parts/TreeRec.agda` — green
* `~/.cabal/bin/agda-2.9.0 BRA/Thm12.agda` — green; verify the
  `FromBridges` parameter list no longer mentions `treeRec`-specific items
* `~/.cabal/bin/agda-2.9.0 BRA/GoedelII.agda` — green
* `~/.cabal/bin/agda-2.9.0 BRA/Thm14.agda` — green

## Headline output

After the work, run:

```bash
echo "=== thm12_F2 (treeRec f s) clause ==="
sed -n '/^  thm12_F2 (treeRec/,/^$/p' BRA/Thm12.agda | head -10
echo
echo "=== FromBridges parameters mentioning treeRec ==="
grep -A3 "treeRec\|apf_cor" BRA/Thm12.agda | head -30
```

Expected: clean `mkR2 …` invocation in the `thm12_F2 (treeRec f s)`
clause, with the `where`-block taking only `rf = thm12_F1 f` and
`rs = thm12_F2 s` (plus any structural closure lemmas) — no
`FromBridges`-supplied parameters.

## Constraints

* ASCII only; `--safe --without-K --exact-split` on every file.
* No postulates, no holes, no `with`-abstraction, no dot patterns.
* Do **not** change `Thm12_F1_Result` / `Thm12_F2_Result` types.
* Do **not** touch any other Fun2 cases (Pair, Const, Lift, Post, Fan,
  IfLf, TreeEq).  IfLf and TreeEq still have their `*_xeq1` `FromBridges`
  parameters from prior sessions; those are out of scope for this task.
* Do not introduce new `FromBridges` parameters; the goal is to
  eliminate the existing `treeRec`-specific ones.

## Reading list before starting

1. `BRA/Thm12.agda` lines 99–230 — current `FromBridges` and
   `thm12_F2 (treeRec f s)` clause.
2. `BRA/Thm12/Parts/TreeRec.agda` — current `Construction` module
   (~700 LoC), especially `bridgeO`, `D_correct2_treeRec_fs_O`, the
   universal-proof block, and the wrapper.
3. `BRA/Thm12/Parts/Comp2.agda` and `BRA/Thm12/Parts/Fan.agda` — the
   `parDispCongR s` chain pattern is exactly what's needed for
   `treeRec`'s step case.
4. `BRA/Th12TreeEqClose.agda` — analogous closure file for TreeEq;
   structurally similar minus the `Df_f` IH dependency.
5. `BRA/Thm12/Param/AxTreeRecLf.agda` and `AxTreeRecNd.agda` — the
   encoded forms `parEnc*`, `parOut*`, and dispatch `parDisp*` lemmas.
6. `BRA/Thm12/Param/RuleTrans.agda` and `BRA/Thm12/Param/CongR.agda`
   — the `parDispRuleTrans` and `parDispCongR` lemmas used in the chain.

## Pitfalls to avoid

* The `parOutAxTreeRecNd` second component uses syntactic `codeF`-form
  (via `reify (leftT (codeF2 (treeRec I IfLf)))` etc.), while
  `codeFTeq2` and `thm12_F2 s .proof` use `cor`-form.  The
  `parDispCongR s` chain bridges by substituting `Snd (thmT (D2_treeRec
  p t))` (which equals `cor (treeRec f s p t)` via the cross-IH) for the
  syntactic `treeRec`-encoding in `parOutAxTreeRecNd`'s second
  component.  Get the substitution direction right.

* `parDispRuleTrans` requires a `Fst y1 = Pair _ _` shape proof.  For
  `y1 = parEncAxTreeRecLf …`, this is `axFst` on the `tagCode_axTreeRecLf`
  prefix, which reduces because `tagCode_axTreeRecLf` is a closed
  `natCode`-encoded Term.  Same for `parEncAxTreeRecNd`.

* The schema-form proof at `(p = var (suc zero), x = var zero)`
  computes `D2_treeRec_fs (var (suc zero)) (var zero)` — be careful with
  variable indices not collinding with `v1IndNat = 2`, `v2IndNat = 3`
  used by `ruleIndBT`.

## Acceptable to break

None.  This is the final piece; everything must stay green.

## End-of-session deliverable

Show the user:

1. The `thm12_F2 (treeRec f s)` clause (clean, no `FromBridges`
   parameters in its where-clause).
2. The diff of `FromBridges`'s parameter list (six items removed).
3. A final `grep` confirming no `apf_cor`, `treeRec_xeq1`,
   `D2_treeRec_NN`, `treeRec_fs_closed_for` references remain in
   `BRA/Thm12.agda`.
4. Green build for all five verification targets.
