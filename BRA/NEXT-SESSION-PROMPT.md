# Next session prompt — close criterion (B) for treeRec NN-internalisation

Read this whole file before starting.  Do not consult prior-conversation
memory; everything you need is here or in the named files.

## Goal — success criterion (B)

After this session, **`thm12_F2 (treeRec f s)` in `BRA/Thm12.agda` must
be a fully closed Agda term** whose `where`-block uses only:

* `rf = thm12_F1 f`
* `rs = thm12_F2 s`

(plus, optionally, the structural closure lemmas `Fun1_closed` /
`Fun2_closed` from `BRA.SubstClosure`).

**No `FromBridges` parameter is consumed by the `treeRec` case.**
Concretely, after the work, none of these names appear in the treeRec
where-clause or as `FromBridges` parameters in `BRA/Thm12.agda`:

```
D2_treeRec_NN_fun         D_correct2_treeRec_NN_pt
apf_corLemma_for          treeRec_xeq1 / treeRec_peq0
D2_treeRec_NN_fun_closed_for                treeRec_fs_closed_for
```

A final `grep -E "apf_cor|treeRec_xeq1|treeRec_peq0|D2_treeRec_NN|treeRec_fs_closed_for" BRA/Thm12.agda` returns nothing (or only stale
comments).

The type of `thm12_F2 (treeRec f s) .proof` must remain:

```agda
(p x : Term) ->
  Deriv (atomic (eqn (ap1 thmT (ap2 D2_treeRec_fs p x))
                     (codeFTeq2 (treeRec f s) p x)))
```

(Criterion (A) — already met; do not change this type.)

## Verification targets

All five must stay green throughout.  Run via `~/.cabal/bin/agda-2.9.0`:

* `BRA/SubstClosure.agda`
* `BRA/Thm12/Parts/TreeRec.agda` (or its replacement; may be retired)
* `BRA/Thm12.agda`
* `BRA/GoedelII.agda`
* `BRA/Thm14.agda`

Plus your in-progress file:
* `BRA/Th12TreeRecInternal.agda`

## What's already built (do not redo)

`BRA/Th12TreeRecInternal.agda` (1143 LoC, currently green):

* Module `Construction (f, s, Df_f, proof_f, Df_s, proof_s)` —
  **target signature**, takes IH-on-f and IH-on-s.
* `D2_treeRec_fs : Fun2 = treeRec lf_emitter step_emitter` (closed).
* `lf_emitter : Fun1`, `step_emitter : Fun2` — fully built (real,
  not placeholders).
* Reductions:
  * `lf_emitter_red`
  * `D2_treeRec_fs_at_O : (p : Term) -> Deriv ...`
  * `step_emitter_red : (p v1 v2 r1 r2 : Term) -> Deriv ...`
  * `D2_treeRec_fs_at_Nd : (p v1 v2 : Term) -> Deriv ...` (uses
    `axTreeRecNd` + `step_emitter_red`)
* All atomic + Tier-2 + composite emit_*_red lemmas (~30 lemmas).
* `D_correct2_treeRec_fs_O : (p : Term) -> Deriv ...` — leaf-case
  Theorem 12 correctness.
* Imports already in place:
  * Doubly-lifted dispatchers: `thmTDispRuleTrans_param_doublelifted`,
    `thmTDispCongL_param_doublelifted`,
    `thmTDispCongR_param_doublelifted`.
  * SKI utilities: `liftAxiom`, `liftAxiomTwo`, `B_combinator`,
    `B_combinatorTwo`, `liftedRuleTrans`, `liftedRuleTransTwo`,
    `liftedCong1`/`liftedCong1Two`, `liftedCongL`/`liftedCongLTwo`,
    `liftedCongR`/`liftedCongRTwo`.
  * `corOfPair` from `BRA/CorOfPair.agda`.

## Background — why the architecture is what it is

The obstruction is structural and applies to any primitive-recursive
scheme on trees (Guard's R, Rose's Rec, BRA's treeRec):

* **Cross-IH at runtime is forced.**  The chain Df at the Pair-input
  case must mention recursive Df-values at the subtrees.  Without
  Deriv-to-Term reflection, the only way to deliver them is to make
  `D2_treeRec_fs` itself recursive in the same scheme.  Hence
  `D2_treeRec_fs = treeRec lf_emitter step_emitter`.

* **`ruleIndBT` + SKI-lifted IHs.**  Universal correctness needs
  ruleIndBT on the recursion variable; the Pair-case step delivers
  doubly-lifted IHs Pv1, Pv2 used inside the chain via the
  doubly-lifted dispatchers.

* **4-step chain.**  `parEncAxTreeRecNd` → cross-IH-driven rewrite on
  s for v1 → cross-IH-driven rewrite on s for v2 → IH-on-s.

* **Deriv-level corOfPair bridges.**  After the encoded chain, the
  RHS still has `enc_X` and `mkAp2T cf2_Pair (cor TR_v1)(cor TR_v2)`
  forms that must bridge to `cor X` and `cor V` to match the
  IH-on-s's first component.  Use `corOfPair` lifted via
  `liftedCong*Two`.

`BRA/Th12RecPUniv.agda` is the closest structural reference (it does
this for `RecP s = treeRec Z s`, where the leaf chain is just constant
`O` instead of `Df_f`-based).  **It does not typecheck** (depends on
`BRA/Th12Rec.agda` which references stale ThmT exports
`tagCode_axRecLf`, `thmTDispAxRecLf_param`, etc.).  Read it as a
**structural template** only — do not import or compile.

Specifically, read these sections of `BRA/Th12RecPUniv.agda`:

* Lines 1100-1200: `WithClosure` module entry, `Th12_at_lf_substF`.
* Lines 1310-1400: `IH2RecP_doublelifted` record + `toIH2RecP_doublelifted`.
* Lines 1368-1410: `BasePair (v1 v2 : Nat)` module — the Pair-case
  Sigma proof skeleton.
* Lines 1416-1470: `basePair_param` (the final wired-up step).

Adapt the structure to treeRec; the leaf chain (already done in
`Th12TreeRecInternal.agda` as `D_correct2_treeRec_fs_O`) handles the
`Df_f` complication.

## What remains for criterion (B)

### Step 3: Pair-case Sigma proof (~400-600 LoC, the only genuinely hard piece)

Add to `BRA/Th12TreeRecInternal.agda` Construction module, after the
existing `D_correct2_treeRec_fs_O` lemma.

**Step 3a — substF closure lemmas (~80 LoC, mechanical):**

```agda
D2_treeRec_fs_closed : (k : Nat) (r : Term) ->
  Eq (substF2 k r D2_treeRec_fs) D2_treeRec_fs
D2_treeRec_fs_closed k r = Fun2_closed k r D2_treeRec_fs

-- Bridge: substF zero r P_Th12_treeRec  =  P_concrete_at r.
formula_eq : (r : Term) -> Eq (substF zero r P_Th12_treeRec) (P_concrete_at r)
formula_eq r = ... (use thClosed, D2_treeRec_fs_closed,
                   subst_reify on tagAp2 / cf2_TR, cor_closed,
                   treeRec_fs_closed)
```

Mirror `BRA/Thm12/Parts/TreeRec.agda` lines 506-600 (the existing
`lhs_eq`, `inner_corPair_eq`, `second_pair_eq`, `encoded_lhs_eq`,
`cor_treeRec_eq`, `rhs_eq`, `formula_eq`).  Pattern is identical.

**Step 3b — base-O cast (~10 LoC):**

```agda
base_O_subst : Deriv (substF zero O P_Th12_treeRec)
base_O_subst = eqSubst Deriv (eqSym (formula_eq O))
                       (D_correct2_treeRec_fs_O (var (suc zero)))
```

**Step 3c — BasePair module (~300-500 LoC, the heart):**

Build the Pair-case proof under doubly-lifted Pv1, Pv2 hypotheses.

```agda
v1IndNat v2IndNat : Nat
v1IndNat = suc (suc zero)
v2IndNat = suc (suc (suc zero))

module BasePair where
  v1T = var v1IndNat
  v2T = var v2IndNat
  pT  = var (suc zero)
  pairT = ap2 Pair v1T v2T

  Pv1 = substF zero v1T P_Th12_treeRec
  Pv2 = substF zero v2T P_Th12_treeRec
  Ppair = substF zero pairT P_Th12_treeRec

  -- After formula_eq, Pv1 ~ atomic(eqn(thmT(D2 pT v1T))(codeFTeq2_TR f s pT v1T))
  -- — exactly the d_h shape needed for parDispCongL Pair (D2 pT v1T) ...

  -- Doubly-lifted IH access derivs.
  dl_Pv1 : Deriv (Pv1 imp (Pv2 imp Pv1))
  dl_Pv1 = axK Pv1 Pv2

  axImpRefl : (Q : Formula) -> Deriv (Q imp Q)
  axImpRefl Q = mp (mp (axS Q (Q imp Q) Q) (axK Q (Q imp Q))) (axK Q Q)

  dl_Pv2 : Deriv (Pv1 imp (Pv2 imp Pv2))
  dl_Pv2 = mp (axK (Pv2 imp Pv2) Pv1) (axImpRefl Pv2)

  -- Cast dl_Pv_i to the underlying atomic-equation form by formula_eq.
  -- (eqSubst on the Deriv imp imp atomic shape.)
  dl_Pv1_atom : Deriv (Pv1 imp (Pv2 imp atomic (eqn
    (ap1 thmT (ap2 D2_treeRec_fs pT v1T))
    (codeFTeq2_treeRec_fs f s pT v1T))))
  dl_Pv1_atom = ... (via eqSubst with formula_eq v1T)

  dl_Pv2_atom : ...

  -- Step 3c.i: 4-step encoded chain via doubly-lifted dispatchers.
  --
  -- Y4 = Df_s_app_term pT v1T v2T
  --    = ap2 Df_s (Pair pT pairT) (Pair (treeRec f s pT v1T)(treeRec f s pT v2T))
  -- Y3 = step2_chain_term pT v1T v2T (ap2 D2_treeRec_fs pT v2T)
  -- Y2 = step1_chain_term pT v1T v2T (ap2 D2_treeRec_fs pT v1T)
  -- Y1 = parEncAxTreeRecNd fT sT (cor pT)(cor v1T)(cor v2T)
  -- chain = parEncRuleTrans Y1 (parEncRuleTrans Y2 (parEncRuleTrans Y3 Y4))
  --
  -- thmT(Y1) image: by liftAxiomTwo Pv1 Pv2 (parDispAxTreeRecNd ...).
  --
  -- thmT(Y2) image: parEncCongR s ... wraps parEncCongL Pair r1 enc_TR_v2.
  --   thmT(parEncCongL Pair r1 enc_TR_v2) via thmTDispCongL_param_doublelifted
  --     with d_h_lifted = dl_Pv1_atom (cross-IH at v1).
  --     Output: thmT(parEncCongL ...) = (mkAp2T cf2_Pair u1_v1 enc_TR_v2,
  --                                       mkAp2T cf2_Pair u2_v1 enc_TR_v2)
  --     where (u1_v1, u2_v1) = (mkAp2T cf2_TR (cor pT)(cor v1T),
  --                              cor (treeRec f s pT v1T)).
  --   Then thmT(Y2) via thmTDispCongR_param_doublelifted s enc_X (parEncCongL ...) ...
  --     Output: thmT(Y2) = (mkAp2T sT enc_X (mkAp2T cf2_Pair u1_v1 enc_TR_v2),
  --                          mkAp2T sT enc_X (mkAp2T cf2_Pair u2_v1 enc_TR_v2)).
  --
  -- thmT(Y3) image: similarly with cross-IH at v2.
  --   parEncCongR Pair r2 (cor TR_v1) — d_h is dl_Pv2_atom.
  --   Then thmT(Y3) = (mkAp2T sT enc_X (mkAp2T cf2_Pair (cor TR_v1) enc_TR_v2),
  --                     mkAp2T sT enc_X (mkAp2T cf2_Pair (cor TR_v1) (cor TR_v2))).
  --
  -- thmT(Y4) image: by liftAxiomTwo Pv1 Pv2 (proof_s X V).
  --   Output: (mkAp2T sT (cor X)(cor V), cor (s X V)).
  --   Where X = Pair pT pairT, V = Pair (treeRec _ _ pT v1T)(treeRec _ _ pT v2T).
  --
  -- thmTDispRuleTrans_param_doublelifted to chain:
  --   (Y1 with shape) o (Y2 with bridge if needed) o (Y3 with bridge) o (Y4 with bridge).
  --
  -- The chain expects u2 = u3 at each level.  Bridge mismatches via
  -- ruleTrans on the d2 hypothesis (Deriv-level corOfPair lifts).

  -- Step 3c.ii: Deriv bridges.
  --   LHS: mkAp2T cf2_TR (cor pT)(mkAp2T cf2_Pair (cor v1T)(cor v2T))
  --      → mkAp2T cf2_TR (cor pT)(cor pairT)
  --     via congR-Pair-Pair (cor pT) (ruleSym (corOfPair v1T v2T)),
  --     lifted under (Pv1 imp (Pv2 imp _)) via liftAxiomTwo / liftedCong*Two.
  --
  --   RHS: cor (s X V) → cor (treeRec f s pT pairT)
  --     via cong1 cor (ruleSym (axTreeRecNd f s pT v1T v2T)), lifted.
  --
  --   Bridges from RHS_step3 to mkAp2T sT (cor X)(cor V):
  --     enc_X → cor X via corOfPair (twice, lifted).
  --     mkAp2T cf2_Pair (cor TR_v1)(cor TR_v2) → cor V via corOfPair (lifted).

  basePair_proof : Deriv (Pv1 imp (Pv2 imp Ppair))
  basePair_proof = ... (assemble all the above via lifted ruleTrans chain
                        + cong1 thmT D2_treeRec_fs_at_Nd at the start)
```

**Important: Bridge style for u2 ≠ u3 at each parDispRuleTrans level.**

When chaining Y3 (whose RHS contains `mkAp2T sT enc_X (mkAp2T cf2_Pair
(cor TR_v1)(cor TR_v2))`) with Y4 (whose LHS is `mkAp2T sT (cor X)(cor V)`),
the natural u2 ≠ u3.  Resolve by post-bridging the d_chain123 image:

```agda
-- d_chain123 : ... thmT(Y1Y2Y3) = (LHS_enc, RHS_step3) ...
-- bridge_RHS3_to_LHS4 : Deriv (eqn RHS_step3 (mkAp2T sT (cor X)(cor V)))
--   built from corOfPair X (Pair v1 v2), corOfPair v1 v2, corOfPair TR_v1 TR_v2,
--   composed via congR/congL on mkAp2T's Pair structure.
--
-- d_chain123_bridged = chain via liftedRuleTransTwo with congL-Pair-applied bridge.
-- Then thmTDispRuleTrans_param_doublelifted with d_chain123_bridged + Y4.
```

See `BRA/Th12RecPUniv.agda` `RecPPairCase_doublelifted` (in Th12RecP.agda)
for the analogous bridge construction.

### Step 4 — universal closure (~30 LoC):

```agda
P_Th12_treeRec : Formula
P_Th12_treeRec = atomic (eqn
  (ap1 thmT (ap2 D2_treeRec_fs (var (suc zero)) (var zero)))
  (codeFTeq2_treeRec_fs f s (var (suc zero)) (var zero)))

D_correct2_treeRec_fs_univ : Deriv P_Th12_treeRec
D_correct2_treeRec_fs_univ = ruleIndBT P_Th12_treeRec v1IndNat v2IndNat
                                base_O_subst
                                BasePair.basePair_proof
```

### Step 5 — Pair-encoding ruleInst trick (~150 LoC, mostly copy-pastable):

The wrapper `D_correct2_treeRec_fs : (p x : Term) -> Deriv ...` uses
three nested `ruleInst`s at fresh `bigNat = 2`: `Snd (var 2)`,
`Fst (var 2)`, `Pair p x`.  Then Deriv-level bridges via `axFst` /
`axSnd`.

**Copy pattern wholesale** from `BRA/Thm12/Parts/TreeRec.agda` lines
660-1046 (the `step2_*`, `step3_*`, `pairBridge*`, and final
`D_correct2_treeRec_fs` definitions).  Substitute the relevant
identifiers.  Mostly mechanical.

### Step 6 — wire into Thm12.agda (~10 LoC):

Replace `BRA/Thm12.agda`'s `thm12_F2 (treeRec f s)` clause:

```agda
thm12_F2 (treeRec f s) = mkR2 R.D2_treeRec_fs R.D_correct2_treeRec_fs
  where
    rf = thm12_F1 f
    rs = thm12_F2 s
    module R = BRA.Th12TreeRecInternal.Construction
                 f s
                 (Thm12_F1_Result.Df rf) (Thm12_F1_Result.proof rf)
                 (Thm12_F2_Result.Dg rs) (Thm12_F2_Result.proof rs)
```

Remove `D2_treeRec_NN_fun` and `D_correct2_treeRec_NN_pt` from
`FromBridges` parameter list (lines 112-116).  Add
`open import BRA.Th12TreeRecInternal` to the imports.

Then `BRA/Thm12/Parts/TreeRec.agda`'s `Construction` module is dead;
optionally retire / delete the file (or leave it as `private`).

## Constraints

* ASCII only.  `{-# OPTIONS --safe --without-K --exact-split #-}` on
  every file.
* No postulates.  No holes.  No `with`-abstraction.  No dot patterns.
* Do not change `Thm12_F1_Result` / `Thm12_F2_Result` types.
* Do not change the universal-wrapper interface
  `D_correct2_treeRec_fs : (p x : Term) -> Deriv ...`.
* Do not touch any other Fun2 cases (Pair, Const, Lift, Post, Fan,
  IfLf, TreeEq).

## Acceptable to break

None.  Every verification target must stay green.  If you must commit
mid-proof, do it on a side file or branch; `BRA/Thm12.agda` may not be
modified until you can swap the where-clause atomically.

## Pitfalls

* `parDispRuleTrans`-style chains require `u2 = u3` syntactically at
  each level.  When the natural u2 / u3 differ (always at the Y3 → Y4
  bridge), apply Deriv-level bridges to one of d1 / d2 BEFORE plugging
  into the dispatch.
* `parDispCongR g y_h_T xT u1 u2 d_h` and `parDispCongL g y_h_T xT u1 u2 d_h`:
  the `xT` argument is the term **kept fixed** during the rewrite; the
  rewrite is on the `y_h_T` slot (its image (u1, u2) becomes the
  rewritten slot).  Double-check which is which when laying out
  `enc_X` vs `r_i` etc.
* `cf2_TR = reify (codeF2 (treeRec f s)) = ap2 Pair (reify K) (ap2 Pair fT sT)`
  where `K = leftT (codeF2 (treeRec I IfLf))`.  `parOutAxTreeRecLf` /
  `parOutAxTreeRecNd` both use the `leftT (codeF2 (treeRec I IfLf))`-form
  syntactically; this **equals** `cf2_TR`'s left slot (same constant
  K), but Agda may not reduce them syntactically — bridge with `eqCong`
  on the Pair constructor when needed.  See the existing leaf-case
  proof in `Th12TreeRecInternal.agda` for the pattern.
* The `bigNat = 2` in Step 5's wrapper is **scoped inside the wrapper**
  and does NOT conflict with `v1IndNat = 2` / `v2IndNat = 3` in Step 4
  (those names appear only inside the BasePair / step-imp proof).
* `corOfPair` (in `BRA/CorOfPair.agda`) gives:
  `Deriv (eqn (ap1 cor (ap2 Pair x y)) (mkAp2T (reify (codeF2 Pair)) (ap1 cor x) (ap1 cor y)))`.
  Use `ruleSym corOfPair` to go from the encoded Pair form to the
  cor-of-Pair form.

## Files to read first

1. **This file.**
2. `BRA/Th12TreeRecInternal.agda` (1143 LoC, current state — leaf done,
   step_emitter built, doubly-lifted dispatcher imports done).
3. `BRA/Thm12/Parts/TreeRec.agda` lines 506-600 (formula_eq pattern for
   Step 3a) and lines 660-1046 (Pair-encoding ruleInst trick for
   Step 5).
4. `BRA/Thm/EvalHelpers.agda` (SKI lift utilities: `liftAxiomTwo`,
   `liftedRuleTransTwo`, `liftedCong*Two`).
5. `BRA/CorOfPair.agda` (`corOfPair` for Deriv-level bridges).
6. `BRA/Thm12/Param/AxTreeRecNd.agda` (`parEncAxTreeRecNd`,
   `parOutAxTreeRecNd`, `parDispAxTreeRecNd`).
7. `BRA/Th12RecPUniv.agda` lines 1100-1470 — broken
   USABLE-AS-STRUCTURAL-REFERENCE for the BasePair pattern; do NOT
   compile or import.
8. `BRA/Th12RecP.agda` `RecPPairCase_doublelifted` — also broken;
   read for the bridge construction pattern.

## End-of-session deliverable

After completing Steps 3-6, run:

```bash
echo "=== thm12_F2 (treeRec f s) clause ==="
sed -n '/^  thm12_F2 (treeRec/,/^$/p' BRA/Thm12.agda | head -10
echo
echo "=== grep for old treeRec FromBridges names ==="
grep -E "apf_cor|treeRec_xeq1|treeRec_peq0|D2_treeRec_NN|treeRec_fs_closed_for" BRA/Thm12.agda || echo "(none — clean!)"
echo
echo "=== build verification ==="
~/.cabal/bin/agda-2.9.0 BRA/SubstClosure.agda;       echo SC=$?
~/.cabal/bin/agda-2.9.0 BRA/Thm12.agda;              echo T12=$?
~/.cabal/bin/agda-2.9.0 BRA/GoedelII.agda;           echo G=$?
~/.cabal/bin/agda-2.9.0 BRA/Thm14.agda;              echo T14=$?
```

Expected: clean `mkR2 …` invocation in the `thm12_F2 (treeRec f s)`
clause, where-block taking only `rf = thm12_F1 f` and `rs = thm12_F2 s`.
The grep returns nothing.  All builds exit 0.

Show the user the final type of `thm12_F2 (treeRec f s) .proof` (must
match Step 3 / criterion (A)).
