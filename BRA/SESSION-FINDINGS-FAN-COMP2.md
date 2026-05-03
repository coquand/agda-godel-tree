# Session findings — Fan/Comp2 shape elimination

Status: read NEXT-SESSION doc, verified the 11 correct cases typecheck, analyzed three candidate fixes in depth, and wrote findings here for your direction before committing to scope.

## State of the existing infrastructure

`BRA/Thm12.agda` already exists and typechecks cleanly. It defines:

```agda
record Thm12_F1_Result (f : Fun1) where
  field
    Df    : Fun1
    proof : (x : Term) -> Deriv (eqn (thmT (ap1 Df x)) (codeFTeq1 f x))

record Thm12_F2_Result (g : Fun2) where
  field
    Dg    : Fun2
    proof : (x v : Term) -> Deriv (eqn (thmT (ap2 Dg x v)) (codeFTeq2 g x v))
```

Result records have only `Df` + `proof` (matches doc constraint #3). The mutual recursion `thm12_F1` / `thm12_F2` is structured as one-liners per case, but lives inside a `module FromBridges` whose parameters include the rejected `Df_shape` / `D2g_shape` Sigma suppliers.

So the structural form is already there. The work is dropping the `FromBridges` wrapper by discharging its parameters concretely.

## The genuine obstruction (re-verified)

`thmTDispCongL_param` (used by both `parDispCongL` for parametric and `thmTDispCongL` for closed) calls

```agda
distrib2 = thmTDistrib_param y_h_T xT y_h' shape_h
```

where `shape_h : Deriv (eqn (Fst y_h_T) (Pair x' y_h'))`.

Inside `thmTDistrib_param`, this shape drives `stepProto_else`'s `axIfLfN`. The shape is on the bare `y_h_T` (the open IH-output term), and it cannot be replaced by `Fst (thmT y_h_T) = u1`: `stepProto`'s `discComb a b = Fst (Fst a)` reads `Fst y_h_T` directly, and `d_h` does not constrain `y_h_T`'s syntactic head.

I checked `BRA/Thm12/Param/Cong1.agda`'s `parDispCong1` for comparison: it does **not** need a y_h_T shape, because its payload depth is only 2 (`Pair codeF1f y_h_T`), so only the closed `fstReifyCodeF1 f` shape is consumed. The CongL/CongR depth is 3 (`Pair codeF2g (Pair y_h_T xT)`), and that extra inner Pair is exactly where the open subterm sits.

## Three candidate fixes evaluated

### Fix 1 — re-encode parEncCongL (proper but large)

Change the encoding so the open subterm sits at the OUTER Snd:

```agda
parEncCongL g y_h_T xT = Pair tagCongL (Pair (Pair codeF2g xT) y_h_T)
```

Now both layers of distribution use closed-code Fst shapes (`Fst codeF2g`, `Fst (Pair codeF2g xT)`) — both provable.

**Cost.** Touches `body_congL` / `body_congR` combinator structure (their navigation paths change), plus all `body_congL_eval` / `_param` / `_lifted` / `_doublelifted` lemmas, plus `thmTDispCongL_param` / `_lifted` / `_doublelifted` / `thmTDispCongL` (closed), plus the CongR mirror. Plus consumers: `BRA/StepT12.agda` (closed thmTDispCongL), `BRA/Thm12RecCheck.agda` (parametric), `BRA/Thm12/TreeEqNN.agda` (parametric encoding constructors), `BRA/Thm12/Parts/Comp2.agda`, `BRA/Thm12/Parts/Fan.agda`. Estimated 800-1500 LoC of careful changes spread across 5+ files.

**Verdict.** Cleanest fix and closest to the doc's spirit. Out of scope for a single session given the surface area; multi-session work.

### Fix 2 — route via parDispCong1 with Comp2-wrapped Fun1 (BLOCKED)

Treat `congL g xT (IH at y_h_T)` as `cong1 (Comp2 g I (KT xT)) (IH at y_h_T)` (BRA-equivalent via axComp2 + axI + axKT). `parDispCong1` doesn't need shape, and we'd add a parDispRuleTrans bridge from `mkAp1T (codeF1 (Comp2 g I (KT xT))) z` to `mkAp2T (codeF2 g) z xT`.

**Blocker found.** `KT` requires a Tree argument, not a Term. In Fan/Comp2 the substituent `xT = ENC_H2NUM` is a Term constructed at runtime from `(x, v)` (e.g., `ap2 Pair (reify tagAp2) (...)`), not a closed Tree. So `KT xT` is ill-typed. No analog Fun1-builder for "ignore z, return Term-xT" exists in the current syntax.

### Fix 3 — Phase 8a/8b shape lemmas (REJECTED by doc)

Per-Df-family shape lemmas case-splitting on `x` (with ruleIndBT for IfLf-shaped atomic Df like `D_Fst = Comp2 IfLf I dispatchFun`). The doc explicitly says:

> **No shape Sigma-witnesses anywhere.** ... the `Df_shape` / `D2g_shape` parameters of `BRA.Thm12.FromBridges` were rejected. Delete them.

so this is off the table.

## What I think is achievable today vs needs more sessions

**Today (already done):** verified the 11 atomic+Comp/Lift/Post cases typecheck. Confirmed the existing FromBridges in `BRA/Thm12.agda` typechecks. Identified the precise shape obligation site (`thmTDistrib_param` line 10101 → `stepProto_else` line 1850).

**Needs more sessions (Fix 1 path):**
1. Refactor `body_congL` / `body_congR` combinator structure for new encoding (~300-500 LoC in `BRA/Thm/ThmT.agda`).
2. Refactor all `body_congL_eval` / `_param` / `_lifted` / `_doublelifted` lemmas (~200-400 LoC).
3. Refactor `thmTDispCongL` (closed) / `_param` / variants (~200 LoC).
4. Mirror for CongR.
5. Update consumers: `StepT12.agda`, `Thm12RecCheck.agda`, `TreeEqNN.agda`, `Comp2.agda`, `Fan.agda` (~300 LoC).
6. Drop `Df_shape` / `D2g_shape` from `FromBridges`. Drop `FromBridges` entirely once Rec/RecP `z_corLemma_for` is also dischargeable (Task B's body_axRecLf work).

## What I'd like guidance on

The cong1 reroute (Fix 2) was my hope for an "in-session" path that avoids the `body_congL` rewrite. The Tree-vs-Term mismatch on `KT` kills it.

Given that, the realistic options are:
- (A) Commit to Fix 1 across sessions, with this session laying groundwork (an explicit task list, maybe drafting the new `body_congL` structure + reduction lemmas), but **not** completing the refactor or ending up with a clean recursion this session.
- (B) Accept a temporary deviation: keep `Df_shape` / `D2g_shape` as `FromBridges` parameters this session, discharge other FromBridges parameters (concrete NN bundles, universal correctness) so the only remaining obstacles are the shape suppliers. End-state: `thm12_F2 (Fan h1 h2 h)` exists as the desired one-liner, but inside a parametric module that still consumes shape suppliers (bookkeeping deferred).
- (C) Some structural change I'm missing — happy to be redirected.

Either way, eliminating the shape Sigmas without `body_congL` rewrite or new Term→Fun1 lifting primitives appears infeasible to me. If you see a fourth path, please point at it.
