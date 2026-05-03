# Th 14 Carneiro plan — Step 0 architectural blocker

**Date:** 2026-05-02
**Outcome:** The Step 0 of `BRA/NEXT-SESSION-THM14-CARNEIRO.md` (build
concrete `r12_th : Thm12_F1_Result thmT` and `r12_sub : Thm12_F2_Result
sub` via `BRA.Thm12.FromBridges`) is **fundamentally infeasible** with
the codebase as of commit `f2fe93d`.

## The blocker

`BRA/Thm12.agda` line 98--104:

```agda
module FromBridges
  (TreeEq_xeq1 : (x v : Term) -> Eq (subst (suc zero) v x) x)
  (IfLf_xeq1   : (x v : Term) -> Eq (subst (suc zero) v x) x)
  where ...
```

Both parameters claim `subst 1 v x = x` for **arbitrary** `x` and `v`.
This is **inconsistent**: at `x = var (suc zero)` and `v = O`,
`subst 1 O (var 1) = O ≠ var 1`, so `Eq O (var 1)` has no inhabitants.

There is **no top-level instantiation** of `BRA.Thm12.FromBridges`
anywhere in `BRA/`. `BRA/Thm12Final.agda` notes this as an open
"architectural finding" (lines 29--51) and provides only the per-call
restricted closure-arg-parametric forms (e.g. `D_correct2_IfLf x v
xeq1`) where `xeq1` reduces to `refl` at the *specific* concrete inputs
the caller supplies.

## Why both `r12_th` and `r12_sub` trigger it

Tracing the structural recursion on the concrete combinator trees:

* `thmT = Rec stepProtoWrapped = Comp2 (treeRec Z stepProtoWrapped) Z I`.
  - `thm12_F2 stepProtoWrapped = Fan (Lift Snd) (Post Snd Pair) stepProto` (Fan case).
  - `thm12_F2 stepProto = Fan discComb branchesTop IfLf` (Fan case).
  - **needs `thm12_F2 IfLf` — needs `IfLf_xeq1`.**

* `sub = Fan leftSub rightSub subT`.
  - `subT = RecP stepSubT = treeRec Z stepSubT`.
  - `thm12_F2 stepSubT = Fan checkEqSubT contSubT IfLf` (Fan case).
  - **needs `thm12_F2 IfLf` — needs `IfLf_xeq1`.**

Both required Theorem-12 results route through `thm12_F2 IfLf`, which
in turn requires the unsatisfiable `IfLf_xeq1` parameter.

## What's actually proved

`BRA/Thm12/Parts/IfLf.agda` line 966 proves:

```agda
D_correct2_IfLf : (x v : Term) (xeq1 : Eq (subst 1 v x) x) ->
  Deriv (atomic (eqn (ap1 thmT (ap2 D_IfLf x v)) (codeFTeq2_IfLf x v)))
```

This is *closure-arg-parametric*: the caller supplies `xeq1` per-call.
At specific concrete inputs (closed Trees, fresh-var Pair-shapes), the
closure equation reduces to `refl` and the call goes through.

The schematic form `Th12_F2_IfLf : Deriv P_Th12_IfLf` (BRA/Th12IfLf.agda)
is closure-free at the *schematic* level — closure args only enter when
converting from the schematic Deriv (with var 0, var 1 free) to the
universal-Pi `(x v : Term) -> Deriv ...` form via `ruleInst`.

## Possible paths forward (none cheap)

### Path A — refactor `FromBridges`

Change the IfLf and TreeEq cases of `FromBridges` to take
closure-arg-parametric proofs forwarded from the caller's specific use
sites. Same for the `treeRec` case (per `Thm12Final.agda` lines 29-51,
this is the same fix the `Rec/RecP universal closure` blocker needs).

This would require:
* threading per-call closure args through ~6 dispatcher signatures;
* updating each composite Fun2 case (Fan, Post, Comp2, treeRec) to forward them;
* the closure args become Pi-typed over (x, v); the body specialises them at the IfLf/TreeEq leaf.

Estimated: ~500-800 LoC across `Thm12.agda`, `Thm12/Parts/IfLf.agda`,
`Thm12/Parts/TreeEq.agda`, and `Th12TreeRecInternal.agda`. The `Thm12_F1_Result` /
`Thm12_F2_Result` records would need to gain closure-arg parameters (or
be restricted to specific input domains).

### Path B — schematic Theorem 12 for `thmT` and `sub` directly

Don't go through `FromBridges`. Build:

* `Th12_F1_thmT : Deriv (atomic (eqn (ap1 thmT (ap1 D_thmT (var 0))) (codeFTeq1 thmT (var 0))))`
* `Th12_F2_sub : Deriv (atomic (eqn (ap1 thmT (ap2 D_sub (var 0) (var 1))) (codeFTeq2 sub (var 0) (var 1))))`

by hand from the schematic per-constructor pieces (`Th12_F2_IfLf`,
`Th12_F2_Pair`, `Th12_F1_I`, ...). Use `ruleInst` to convert to the
`(x : Term) -> ...` form at the specific (closed) inputs the Goedel II
chain needs. Closure args at those specific sites reduce to `refl`.

Estimated: ~1500-3000 LoC. Mirrors `Th12RecCheck.agda` pattern but for
the concrete `thmT` and `sub` trees, which are 4-6 levels deep.

### Path C — restrict `Thm12_F1_Result` / `Thm12_F2_Result`

Redefine the records so `proof` takes restricted-domain inputs (closed
Terms, fresh vars, etc.) rather than arbitrary `(x : Term)`. Then the
existing `D_correct2_IfLf` form satisfies it directly. But this
propagates to `Thm13`, `Thm14`, `Thm14Abstract`, `GoedelII` — ~50+
signatures touched.

## Recommendation

Path A (refactor FromBridges) is the cleanest. The closure args are
**already** threaded for IfLf and TreeEq at the per-construction level
(`Thm12/Parts/IfLf.D_correct2_IfLf` and
`Thm12/Parts/TreeEq.D_correct2_TreeEq` both take them). The work is
plumbing them through the recursive structural cases (Fan, Post,
treeRec, Comp2, Lift) so that callers at the **top** can supply the
closure args specialised to **their** input.

For the Goedel II application, all top-level inputs are closed Trees
(`reify j`, `cG`, encoded proof witnesses), so the closure args reduce
to `refl` everywhere they bottom out.

## Files involved

* `BRA/Thm12.agda` — `module FromBridges` definition and instantiation.
* `BRA/Thm12/Parts/IfLf.agda` — already closure-arg-parametric.
* `BRA/Thm12/Parts/TreeEq.agda` — already closure-arg-parametric.
* `BRA/Th12TreeRecInternal.agda` — needs same treatment.
* `BRA/Thm12Final.agda` — already discusses the same architectural fix
  needed for Rec/RecP universal closure (lines 29-51).
