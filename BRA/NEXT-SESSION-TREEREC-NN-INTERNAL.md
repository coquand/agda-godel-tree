# Next session — eliminate `D2_treeRec_NN_fun` + `D_correct2_treeRec_NN_pt`

## What's already done (DO NOT redo)

The previous session (see `NEXT-SESSION-TREEREC-INTERNAL.md` for context)
eliminated 4 of the 6 originally listed `treeRec`-specific FromBridges
parameters:

* `apf_corLemma_for` — derived from `thm12_F1 f .proof` via
  `parDispRuleTrans` chaining at the leaf.
* `D2_treeRec_NN_fun_closed_for` — derived from the new
  `BRA.SubstClosure.Fun2_closed` (Fun1/Fun2 contain no `var`).
* `treeRec_fs_closed_for` — derived from `Fun2_closed`.
* `treeRec_xeq1` (and its rename `treeRec_peq0`) — eliminated via the
  **Pair-encoding ruleInst trick**: three `ruleInst`s at a fresh
  `bigNat = 2` (Snd, Fst, then `Pair p x`), bridged at the Deriv level
  via `axFst` / `axSnd`.

The current `Construction` interface in
`BRA/Thm12/Parts/TreeRec.agda` takes:

```
f : Fun1
s : Fun2
Df_f : Fun1
proof_f : (q : Term) -> Deriv (...codeFTeq1-style at f, q...)
D2_treeRec_NN_fun : Fun2
D_correct2_treeRec_NN_pt : (p a b : Term) -> Deriv (...codeFTeq2 ... f s p (Pair a b))
```

and produces

```
D2_treeRec_fs : Fun2
D_correct2_treeRec_fs : (p x : Term) -> Deriv (...codeFTeq2 ... f s p x)
                                         -- NO closure args.
```

`Thm12.agda`'s `FromBridges` still threads `D2_treeRec_NN_fun` and
`D_correct2_treeRec_NN_pt` parametrically (per `Fun1, Fun2`).  The
universal wrapper is closed.  All five verification targets typecheck.

## The global theorem this session closes

`thm12_F2 (treeRec f s)` becomes a **fully closed Agda term** —
the `where`-block consumes only `rf = thm12_F1 f` and `rs = thm12_F2 s`
(plus structural Fun-closure lemmas).  After this session, `FromBridges`
contains no treeRec-specific parameters at all, and the grep

```
grep -E "apf_cor|treeRec_xeq1|treeRec_peq0|D2_treeRec_NN|treeRec_fs_closed_for" BRA/Thm12.agda
```

returns at most stale comments.

## Success criterion (read this FIRST)

This task is **complete** when both of the following hold:

### (A) The type of `thm12_F2 (treeRec f s) .proof` is exactly:

```agda
(x v : Term) ->
  Deriv (atomic (eqn (ap1 thmT (ap2 D2_treeRec_fs x v))
                     (codeFTeq2 (treeRec f s) x v)))
```

i.e., unfolding `codeFTeq2`:

```agda
(x v : Term) ->
  Deriv (atomic (eqn
    (ap1 thmT (ap2 D2_treeRec_fs x v))
    (ap2 Pair
      (ap2 Pair (reify tagAp2)
                (ap2 Pair (reify (codeF2 (treeRec f s)))
                          (ap2 Pair (ap1 cor x) (ap1 cor v))))
      (ap1 cor (ap2 (treeRec f s) x v)))))
```

(The signature is **identical to what the previous session
delivered** — this session does not change the type.)

### (B) `thm12_F2 (treeRec f s)` is a fully closed Agda term

Its `where`-block uses only:

* `rf = thm12_F1 f`
* `rs = thm12_F2 s`

plus, optionally, the structural closure lemmas `Fun1_closed` /
`Fun2_closed` from `BRA.SubstClosure`.

**No `FromBridges` parameter is consumed by the `treeRec` case.**
Concretely, after the work, none of the following names appear in the
treeRec where-clause or as `FromBridges` parameters in `Thm12.agda`:

* `apf_corLemma_for`        (already gone)
* `D2_treeRec_NN_fun`        (this session)
* `D_correct2_treeRec_NN_pt` (this session)
* `D2_treeRec_NN_fun_closed_for`  (already gone)
* `treeRec_fs_closed_for`    (already gone)
* `treeRec_xeq1` / `treeRec_peq0` (already gone)

A final
`grep -E "apf_cor|treeRec_xeq1|treeRec_peq0|D2_treeRec_NN|treeRec_fs_closed_for" BRA/Thm12.agda`
returns nothing (or only stale comments).

### Both (A) and (B) are required.

## Goal

Construct, internally to `Construction` in `BRA/Thm12/Parts/TreeRec.agda`,
a **closed Fun2** that handles the Pair-input case of `D2_treeRec_fs`
and a closed proof of its pointwise correctness — then drop both
`D2_treeRec_NN_fun` and `D_correct2_treeRec_NN_pt` from `FromBridges`
and from the `Construction` parameter list.

The path is the **IfLf-form trick**: define `D2_treeRec_fs` so that
the Pair-case content is produced by an *internal* `treeRec` recursion
(self-reference avoided because `treeRec`'s recursion happens at runtime,
threading the Df-shaped recursive results through `recs`).

## CRITICAL — verify before adapting

The closest precedent in the codebase is
`BRA/Th12RecPUniv.agda` (1470 LoC) + `BRA/Th12RecP.agda` (819 LoC),
which builds the analogous structure for `RecP s = treeRec Z s`.

**Probably usable as a structural template, but I am NOT certain the
adaptation is mechanical.**  Before porting structure, verify these
three points by *reading the actual files*, not memory or this prompt:

1. **Output type alignment.**  Does `Th12_F2_RecP_s_concrete`
   (`BRA/Th12RecPUniv.agda` line 1464) really output a `Deriv` whose
   formula matches *our* `codeFTeq2 (RecP s) (var 1) (var 0)` — i.e.
   the symmetric Pair-encoding we use, not just `codeFTeq2Asym` or
   some other variant?  Compare:

     * `codeFTeq2` (BRA/Thm12.agda lines 61-67).
     * `codeFTeq2Asym` (BRA/Thm14CodeFTeqAsym.agda lines 69-72).

   If they differ at any structural Pair position, plan the bridge
   before importing the Th12RecPUniv chain.

2. **Hidden parametric dependencies.**  Does the
   `Th12RecPUnivCase` module (line 56) actually produce
   `Th12_F2_RecP_s_concrete` *unconditionally*, or does the chain
   route through a `basePair_param` (line 1416) or some closure
   parameter that has to be supplied externally?  Trace the
   `WithBasePairParam` (line 1347) vs the concrete instantiation.
   If anything is "parametric on basePair_param", determine whether
   it's discharged inside the same module (look for the body of
   `basePair_param` at line 1420) or left to the consumer.

3. **`f` arbitrary vs `f = Z`.**  RecP's leaf chain is just `O` (the
   constant-leaf encoding), so `f_lf` in Th12RecPUniv (line 127)
   doesn't need an IH-on-f.  treeRec's leaf chain references
   `Df_f` (the IH on `f`).

   Read `BRA/Th12RecPUniv.agda` lines 700–1470 carefully and trace
   what's load-bearing about the constant-leaf assumption:

     * Does `f_lf` only emit `lf_inner_at p` (line 127), and would
       a treeRec analog need to emit a `parEncRuleTrans`-shaped
       chain that mentions `Df_f p`?
     * Does the leaf-case Sigma assembly (look for
       `Th12_F2_RecP_s_at_lf` in `BRA/Th12RecP.agda`) thread the
       leaf-equation correctness through `axRecPLf` only, or in a way
       that the `Df_f`-based chain (the `parEncRuleTrans
         (parEncAxTreeRecLf fT sT (cor p))
         (ap1 Df_f p)`
       form) already-built in `D2_treeRec_fs_reduce_O` could
       drop into directly?
     * Are the `emit_*` Fun2 combinators in Th12RecPUniv (lines
       136–241) generic enough to accept a `Df_f`-dependent leaf, or
       do they bake in the constant-O choice?

   **The third point is the one I'm most uncertain about.**  If the
   constant-leaf assumption is load-bearing in non-obvious ways
   (e.g., `axRecPLf` reductions inside `Df_F2_RecP_s_at_O` that
   don't generalise to `axTreeRecLf` + IH-on-f), the adaptation
   may need substantive new design work, not just renames.

## Reading list before starting

1. `BRA/Thm12/Parts/TreeRec.agda` — the current state, in particular:
   * The `Construction` parameter list (lines ~63-78).
   * `D2_treeRec_fs` (lines ~131-138) and the existing
     `D2_treeRec_fs_reduce_O` / `D2_treeRec_fs_reduce_Nd` reductions.
   * `D_correct2_treeRec_fs_O` (uses `parDispRuleTrans`-with-`Df_f`
     chain) — note the LEAF case is already self-contained with
     `proof_f`.
   * `D_correct2_treeRec_fs_univ` — the schema-form proof using
     `ruleIndBT` with `axK`-discharged cross-IHs.  This needs to be
     rebuilt to **consume** the cross-IHs (via `mp`, not `axK`) once
     the Pair-case is internalised.
   * The new `D_correct2_treeRec_fs` universal wrapper using the
     Pair-encoding ruleInst trick (no closure args).

2. `BRA/Thm12.agda` — current `FromBridges` parameter list and
   `treeRec` `where`-clause (lines ~95-120, 195-205).

3. `BRA/Thm12/Parts/Comp2.agda` and `BRA/Thm12/Parts/Fan.agda` —
   the `parDispCongR s` chain pattern (used in the Th12RecPUniv
   `step_inner`).  Inspect how cross-IH-on-s is woven through.

4. `BRA/Th12RecPUniv.agda` lines 1–300, then 700–1470 — the
   IfLf-form pattern.  **Before porting, do the three verifications
   in CRITICAL.**

5. `BRA/Th12RecP.agda` — the lf-case Sigma proof skeleton (`Th12RecPCase`
   module).  Same caveat: verify the constant-leaf assumption.

6. `BRA/Thm12/Param/AxTreeRecLf.agda` and `AxTreeRecNd.agda` — encoded
   forms `parEnc*`, `parOut*`, dispatch `parDisp*`.

7. `BRA/Thm12/Param/CongR.agda` and `RuleTrans.agda` — `parDispCongR`,
   `parDispRuleTrans`.

## The plan (sketch — the reading list above may force changes)

### Step 1: define `D2_treeRec_fs` to use internal `treeRec`-recursion

Replace the current `dispatchFun = Fan lfPart D2_treeRec_NN_fun Pair`
with one that uses an internal `treeRec` for the Pair-case content:

```agda
dispatchFun = Fan lfPart (treeRec lf_emitter step_emitter) Pair
```

where `lf_emitter : Fun1` produces the leaf chain (depends on `Df_f`)
and `step_emitter : Fun2` consumes `(orig, recs)` at runtime — `orig`
is `Pair p (Pair a b)`, `recs` is `Pair (D2-result-at-p-a) (D2-result-at-p-b)`.
The recursive `D2`-results are exactly the cross-IH-shaped Df values.

This bypasses self-reference at the Fun2-grammar level: `treeRec`
takes Fun arguments, not `Fun2 = D2_treeRec_fs` (which would be
circular).

### Step 2: rewrite `D_correct2_treeRec_fs_univ`

Currently the step-case discharges cross-IHs via `axK`.  Rewrite it
to **consume** them via `mp` (the IfLf-form pattern in Th12RecPUniv).
The proof at `(p, Pair (var v1) (var v2))` chains:

```
parEncRuleTrans
  (parEncAxTreeRecNd fT sT (cor p) (cor v1) (cor v2))
  (parEncRuleTrans
     (parEncCongR s ENC_first cross_IH_at_v1)
     (parEncRuleTrans
        (parEncCongR s ENC_second cross_IH_at_v2)
        (Df_s_app)))
```

with bridges to `cor (treeRec f s p (Pair v1 v2))` via `axTreeRecNd`
+ `cong1 cor`.

### Step 3: drop the `FromBridges` parameters

In `Thm12.agda`:
* Remove `D2_treeRec_NN_fun` and `D_correct2_treeRec_NN_pt` from the
  `FromBridges` parameter list.
* Update the `thm12_F2 (treeRec f s)` clause to:

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

(The `Construction` interface gains `Df_s : Fun2` + `proof_s`
parameters and loses the NN-bundle parameters.)

### Step 4: drop the `Construction` NN-bundle parameters

In `BRA/Thm12/Parts/TreeRec.agda`:
* Remove `D2_treeRec_NN_fun : Fun2` and `D_correct2_treeRec_NN_pt`
  from the `Construction` parameter list.
* Add `Df_s : Fun2` and `proof_s : (x v : Term) -> ...` parameters.
* Define `D2_treeRec_fs` with internal `treeRec lf_emitter step_emitter`.

## Estimated size

* If Th12RecPUniv adapts cleanly:  ~1500-2000 LoC of new code.
* If the constant-leaf assumption is load-bearing and needs redesign:
  add ~500-1500 LoC.

Plan for ~2000-3500 LoC total, 1-3 sessions.

## Verification targets

* `~/.cabal/bin/agda-2.9.0 BRA/SubstClosure.agda` — green
* `~/.cabal/bin/agda-2.9.0 BRA/Thm12/Parts/TreeRec.agda` — green
* `~/.cabal/bin/agda-2.9.0 BRA/Thm12.agda` — green
* `~/.cabal/bin/agda-2.9.0 BRA/GoedelII.agda` — green
* `~/.cabal/bin/agda-2.9.0 BRA/Thm14.agda` — green

## Headline output

After the work, run:

```bash
echo "=== thm12_F2 (treeRec f s) clause ==="
sed -n '/^  thm12_F2 (treeRec/,/^$/p' BRA/Thm12.agda | head -10
echo
echo "=== grep for old treeRec FromBridges names ==="
grep -E "apf_cor|treeRec_xeq1|treeRec_peq0|D2_treeRec_NN|treeRec_fs_closed_for" BRA/Thm12.agda || echo "(none — clean!)"
```

Expected: clean `mkR2 …` invocation in the `thm12_F2 (treeRec f s)`
clause, with the `where`-block taking only `rf = thm12_F1 f` and
`rs = thm12_F2 s`.  The grep returns nothing (or only stale comments).

## Constraints

* ASCII only; `--safe --without-K --exact-split` on every file.
* No postulates, no holes, no `with`-abstraction, no dot patterns.
* Do **not** change `Thm12_F1_Result` / `Thm12_F2_Result` types.
* Do **not** change the universal-wrapper interface
  `D_correct2_treeRec_fs : (p x : Term) -> Deriv ...`  (no closure args
  — already achieved last session).
* Do **not** touch any other Fun2 cases (Pair, Const, Lift, Post, Fan,
  IfLf, TreeEq).  IfLf and TreeEq's `*_xeq1` `FromBridges` parameters
  remain out of scope.
* Do not introduce new `FromBridges` parameters.

## Acceptable to break

None.  Every verification target must stay green.

## Pitfalls to avoid

* The `parOutAxTreeRecNd` second component uses syntactic `codeF`-form
  (via `reify (leftT (codeF2 (treeRec I IfLf)))` etc.), while
  `codeFTeq2` and `proof_s X V` use `cor`-form.  Bridge via
  `parDispCongR s` substituting `Snd (thmT (D2_treeRec_fs p t))`
  (= `cor (treeRec f s p t)` via cross-IH) for the syntactic
  `treeRec`-encoding in `parOutAxTreeRecNd`'s second component.

* `parDispRuleTrans` requires a `Fst y1 = Pair _ _` shape proof.  For
  `y1 = parEncAxTreeRecNd ...`, this is `axFst` on the
  `tagCode_axTreeRecNd` prefix.

* The schema-form proof at `(p = var (suc zero), x = var zero)`
  computes `D2_treeRec_fs (var (suc zero)) (var zero)`; be careful
  with variable indices not colliding with `v1IndNat = 2`,
  `v2IndNat = 3` used by `ruleIndBT`.

* The `bigNat = 2` in the universal wrapper (for the Pair-encoding
  ruleInst trick) is **scoped inside the wrapper**, NOT the schema.
  It does not conflict with `v1IndNat = 2` / `v2IndNat = 3` of
  `ruleIndBT` (those names appear only inside the step-imp proof,
  not in the final `Deriv P_Th12_treeRec`).

## End-of-session deliverable

Show the user:

1. The `thm12_F2 (treeRec f s)` clause (clean, no `FromBridges`-supplied
   params in its where-clause).
2. The diff of `FromBridges`'s parameter list (treeRec-specific items
   removed).
3. The final `grep` confirming no active references.
4. Green build for all five verification targets.
5. The type of `thm12_F2 (treeRec f s) .proof` (matching the
   success-criterion (A) form above).
