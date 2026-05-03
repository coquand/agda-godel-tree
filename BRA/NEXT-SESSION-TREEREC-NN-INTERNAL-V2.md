# Next session — finish `D2_treeRec_NN_fun` / `D_correct2_treeRec_NN_pt` elimination

## Status

* All five mainline verification targets green; mainline build untouched.
* `BRA/Thm12.agda`'s `treeRec` clause still consumes `D2_treeRec_NN_fun`
  and `D_correct2_treeRec_NN_pt` from `FromBridges` — success criterion
  (B) NOT met.

## What this session shipped

`BRA/Th12TreeRecInternal.agda` — 1137 LoC, green, additive (does not
touch mainline build):

* `Construction (f, s, Df_f, proof_f, Df_s, proof_s)` — **target signature.**
* Closed `D2_treeRec_fs : Fun2 = treeRec lf_emitter step_emitter`.
  * `lf_emitter : Fun1` — proven by `lf_emitter_red`.
  * `step_emitter : Fun2` — **fully built.**  Composes `EmitPair`,
    `KT2`, `Lift`-of-Fun1 projectors into `emit_chainDf`, which at runtime
    emits `parEncRuleTrans (parEncAxTreeRecNd ...) (parEncRuleTrans
    step1_chain_term (parEncRuleTrans step2_chain_term Df_s_app_term))`.
* `D2_treeRec_fs_at_O` — leaf BRA reduction.
* `D_correct2_treeRec_fs_O` — leaf-case Theorem 12 correctness.
* All atomic + Tier-2 + composite emit_*_red lemmas:
  `EmitPair_red`, `KT2_red`, `KT2_eq_red`, `Lift_red`, `Fst1_red`,
  `v1Fun1_red`, `v2Fun1_red`, `cor_p_F_red`, `cor_v1_F_red`,
  `cor_v2_F_red`, `treeRec_p_v1_F_red`, `treeRec_p_v2_F_red`,
  `emit_p_red`, `emit_v1_red`, `emit_v2_red`, `emit_cor_p_red`,
  `emit_cor_v1_red`, `emit_cor_v2_red`, `emit_TR_p_v1_red`,
  `emit_TR_p_v2_red`, `emit_r1_red`, `emit_r2_red`,
  `emit_cor_TR_p_v1_red`, `emit_cor_TR_p_v2_red`,
  `emit_mkAp2T_Pair_corv1_corv2_red`, `emit_enc_TR_v1_red`,
  `emit_enc_TR_v2_red`, `emit_enc_X_red`,
  `emit_parEncCongL_red`, `emit_parEncCongR_red`,
  `emit_step1_chain_red`, `emit_step2_chain_red`, `emit_Df_s_app_red`,
  `emit_parEncAxTreeRecNd_red`, `emit_chainDf_red`.
* `step_emitter_red : (p v1 v2 r1 r2 : Term) -> Deriv ...` — full
  Pair-case BRA reduction at runtime.
* `D2_treeRec_fs_at_Nd : (p v1 v2 : Term) -> Deriv ...` — combines
  axTreeRecNd with step_emitter_red (cross-IH-shaped recs r_i =
  ap2 D2_treeRec_fs p v_i).
* Doubly-lifted dispatchers imported:
  `thmTDispRuleTrans_param_doublelifted`,
  `thmTDispCongL_param_doublelifted`,
  `thmTDispCongR_param_doublelifted`.
* SKI lift utilities imported from `BRA/Thm/EvalHelpers.agda`.
* `corOfPair` imported from `BRA/CorOfPair.agda`.

All green:
```
~/.cabal/bin/agda-2.9.0 BRA/Th12TreeRecInternal.agda    # 1137 LoC, green
~/.cabal/bin/agda-2.9.0 BRA/SubstClosure.agda           # green
~/.cabal/bin/agda-2.9.0 BRA/Thm12/Parts/TreeRec.agda    # green
~/.cabal/bin/agda-2.9.0 BRA/Thm12.agda                  # green (untouched)
~/.cabal/bin/agda-2.9.0 BRA/GoedelII.agda               # green
~/.cabal/bin/agda-2.9.0 BRA/Thm14.agda                  # green
```

## What remains for criterion (B)

### Step 3: Pair-case Sigma proof under Pv1, Pv2 IHs (~400-600 LoC, the heart)

The doubly-lifted dispatchers + cross-IH unfolding give us the four
parDispRuleTrans cascades:

```
Pv1 = atomic (eqn (ap1 thmT (ap2 D2_treeRec_fs (var 1) (var v1Idx)))
                  (codeFTeq2_treeRec_fs f s (var 1) (var v1Idx)))
Pv2 = atomic (eqn (ap1 thmT (ap2 D2_treeRec_fs (var 1) (var v2Idx)))
                  (codeFTeq2_treeRec_fs f s (var 1) (var v2Idx)))
```

Cross-IH unfolding: each Pv_i directly has the form
`thmT(r_i) = Pair (mkAp2T cf2_TR (cor (var 1))(cor (var v_iIdx)))(cor (treeRec _ _ (var 1) (var v_iIdx)))` — exactly what `parDispCongL_doublelifted` /
`parDispCongR_doublelifted` need as the d_h hypothesis.

**Build BasePair module** (mirror Th12RecPUniv lines 1368-1410):

```agda
module BasePair (v1Idx v2Idx : Nat) where
  v1T = var v1Idx
  v2T = var v2Idx
  pT  = var (suc zero)
  pairT = ap2 Pair v1T v2T
  
  Pv1 = substF zero v1T P_Th12_treeRec
  Pv2 = substF zero v2T P_Th12_treeRec
  Ppair = substF zero pairT P_Th12_treeRec

  -- Doubly-lifted IH derivs.
  dl_Pv1 : Deriv (Pv1 imp (Pv2 imp Pv1))
  dl_Pv1 = axK Pv1 Pv2

  dl_Pv2 : Deriv (Pv1 imp (Pv2 imp Pv2))
  dl_Pv2 = mp (axK (Pv2 imp Pv2) Pv1) (axImpRefl Pv2)

  -- Step 3a: bridge dl_Pv1 / dl_Pv2 to the form expected by
  -- thmTDispCongL/R_param_doublelifted (they want d_h at exact shape
  -- Deriv(P1 imp (P2 imp atomic (eqn (thmT y_h_T)(Pair u1 u2))))).
  -- Use eqSubst on substF closure lemmas (see below for required lemmas).

  -- Step 3b: 4-step chain.  Innermost first.
  -- Y4 = Df_s_app_term (var 1) v1T v2T
  -- Y3 = step2_chain_term (var 1) v1T v2T r2 where r2 = D2 _ v2T
  -- Y2 = step1_chain_term (var 1) v1T v2T r1 where r1 = D2 _ v1T
  -- Y1 = parEncAxTreeRecNd fT sT (cor pT)(cor v1T)(cor v2T)

  -- For each level: apply parDispCongL_param_doublelifted /
  -- parDispCongR_param_doublelifted / thmTDispRuleTrans_param_doublelifted
  -- with the cross-IH d_h.

  -- Step 3c: Deriv-level bridges.
  -- After 4-level cascade, thmT(chain_Df_term) has form:
  --   (mkAp2T cf2_TR (cor pT)(mkAp2T cf2_Pair (cor v1T)(cor v2T)),
  --    cor (s X V))
  -- Bridge LHS: (cor v1T, cor v2T) inner pair → cor (Pair v1T v2T)
  --   via ruleSym (corOfPair v1T v2T), lifted under (Pv1 imp (Pv2 imp _)).
  -- Bridge RHS: cor (s X V) → cor (treeRec _ _ pT pairT)
  --   via cong1 cor (ruleSym (axTreeRecNd f s pT v1T v2T)), lifted.
  -- Need a Deriv-level bridge from RHS_step2 to mkAp2T sT (cor X)(cor V),
  -- so the proof_s X V chain step matches.  Use corOfPair (twice for X,
  -- once for V) lifted via liftedCongLTwo / liftedCongRTwo / etc.

  -- Step 3d: Compose with the LHS bridge (using D2_treeRec_fs_at_Nd):
  --   thmT(D2 (var 1) pairT) = thmT(chain_Df_term ...)  (via cong1 thmT).

  basePair_proof : Deriv (Pv1 imp (Pv2 imp Ppair))
  basePair_proof = ...
```

**Required substF closure lemmas** (~80 LoC, mechanical):
* `D2_treeRec_fs_closed : (k : Nat)(r : Term) -> Eq (substF2 k r D2_treeRec_fs) D2_treeRec_fs` — derived from `Fun2_closed`.
* `formula_eq : (r : Term) -> Eq (substF zero r P_Th12_treeRec) (P_concrete_at r)` — bridge.
* Several closure-and-formula bridges (mirror TreeRec.agda's `lhs_eq`,
  `inner_corPair_eq`, `second_pair_eq`, `encoded_lhs_eq`,
  `cor_treeRec_eq`, `rhs_eq`).

### Step 4: ruleIndBT closure (~30 LoC)

```agda
v1IndNat v2IndNat : Nat
v1IndNat = suc (suc zero)
v2IndNat = suc (suc (suc zero))

P_Th12_treeRec : Formula
P_Th12_treeRec = atomic (eqn
  (ap1 thmT (ap2 D2_treeRec_fs (var (suc zero)) (var zero)))
  (codeFTeq2_treeRec_fs f s (var (suc zero)) (var zero)))

base_O_subst : Deriv (substF zero O P_Th12_treeRec)
base_O_subst = ... (D_correct2_treeRec_fs_O cast via formula_eq O)

D_correct2_treeRec_fs_univ : Deriv P_Th12_treeRec
D_correct2_treeRec_fs_univ =
  ruleIndBT P_Th12_treeRec v1IndNat v2IndNat base_O_subst
            (basePair_proof v1IndNat v2IndNat)
```

### Step 5: Pair-encoding ruleInst trick (~150 LoC, mostly copy-pastable)

Copy from `BRA/Thm12/Parts/TreeRec.agda` (lines 660-1046).  Three
`ruleInst`s at fresh `bigNat = 2`: Snd (var 2), Fst (var 2), Pair p x.
Then Deriv-level bridges via `axFst` / `axSnd` to bridge Fst/Snd of
Pair to its components.

Yields:

```agda
D_correct2_treeRec_fs : (p x : Term) ->
  Deriv (atomic (eqn (ap1 thmT (ap2 D2_treeRec_fs p x))
                     (codeFTeq2_treeRec_fs f s p x)))
```

### Step 6: Wire into Thm12.agda (~10 LoC)

Replace `thm12_F2 (treeRec f s)` clause:

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

Remove `D2_treeRec_NN_fun` / `D_correct2_treeRec_NN_pt` from
`FromBridges` parameter list (lines 112-116).  Optionally retire
`BRA/Thm12/Parts/TreeRec.agda`'s `Construction` module (now dead).

## Remaining LoC estimate

* Step 3: ~400-600 LoC.
* Step 4: ~30 LoC.
* Step 5: ~150 LoC.
* Step 6: ~10 LoC.

**Total: ~590-790 LoC.  ~1-2 sessions of focused work.**

The infrastructure is now in place; Step 3 is the only genuinely hard
remaining piece (cross-IH unfolding through the doubly-lifted dispatch
chain + Deriv-level corOfPair bridges).

## Files to read first next session

1. This doc.
2. `BRA/Th12TreeRecInternal.agda` — current state (1137 LoC, leaf done,
   step_emitter built + reduction proven, doubly-lifted dispatcher imports).
3. `BRA/Thm12/Parts/TreeRec.agda` — existing Pair-encoding ruleInst trick
   (Step 5 — copy-paste-able).
4. `BRA/Thm/EvalHelpers.agda` — SKI lift utilities for Step 3.
5. `BRA/CorOfPair.agda` — `corOfPair` bridge for Step 3 Deriv-level.
6. `BRA/Th12RecPUniv.agda` — broken but USABLE-AS-STRUCTURAL-REFERENCE
   for Step 3 (read its `BasePair` module + the `Df_F2_RecP_s_at_Pair_chain_proven`
   pattern; do NOT compile or import).
