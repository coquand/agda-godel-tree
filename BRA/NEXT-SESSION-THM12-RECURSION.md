# Next session: finish Theorem 12 universal via TreeEq-pattern for Rec/RecP

## Goal

Build Theorem 12 universal in `(f : Fun1)(x : Term)`:

```agda
Thm12 : (f : Fun1) -> Sigma Fun1 (\ Df ->
  Deriv (atomic (eqn (ap1 thmT (ap1 Df (var zero)))
                     (codeFTeq1Asym f (var zero)))))
```

(and the analogous `Thm12_F2` for binary functors).  Structural recursion
on Fun1/Fun2 syntax, with all 7 Fun1 + 8 Fun2 cases covered uniformly.

## Architecture (the high-level structure)

Theorem 12 is a **structural recursion on functor syntax** (Guard's
meta-induction).  For each constructor:

| Case | Strategy |
|------|----------|
| Fun1 leaves: I, Z, Fst, Snd | Re-export existing per-Fun universal `Th12_F1_X` |
| Fun2 leaves: Pair, Const | Re-export existing universal `Th12_F2_X` |
| Comp f g, Comp2 h f g | Instantiate existing `Th12CompCase` / `Th12Comp2Case` parametric modules with sub-Fun IHs |
| Lift f, Post f h, Fan h1 h2 h | Instantiate existing `Th12LiftCase` / `Th12PostCase` / `Th12FanCase` |
| IfLf | Re-export `Th12_F2_IfLf` (universal, in `BRA/Th12IfLf.agda`) |
| TreeEq | Re-export `Th12_F2_TreeEq` (universal, in `BRA/Th12TreeEqClose.agda`) |
| **Rec z s** | **NEW** — chain Df uses `Df_F2_s` as sub-component + `Th12_F2 s` as bridge (TreeEq pattern) |
| **RecP s** | **NEW** — analogous to Rec |

The 12 non-Rec/RecP cases are pure wiring of existing universal proofs.
The two Rec/RecP cases require constructing new chain Df's following
the **TreeEq Phase 4 pattern** (see below).

## The TreeEq pattern (key insight)

**`Th12_F2_TreeEq` is already universal** (BRA/Th12TreeEqClose.agda, 1016
LoC across 5 files, all <1s typecheck).  The closure pattern was
discovered in the prior session (memory:
`project_th12_treeeq_close_done`):

  * `D_TreeEq_NN_fun` (BRA/Th12TreeEqNNFun.agda lines 14-17): the chain
    Fun2 at NN-input emits `Pair tagCode_ruleTrans (Pair y1T y2T)` where
    **`y2T = ap2 D_IfLf (ap2 TreeEq v1 v3) (ap2 Pair (ap2 TreeEq v2 v4)(ap2 Pair O O))`**.
    `D_IfLf` is the Fun2 chain for IfLf — embedded as a sub-component.
  * The proof of correctness (BRA/Th12TreeEqBasePP.agda) uses
    **`Th12_F2_IfLf` (encoded form, universal-in-(x,v))** at the bridge
    step, instantiated via `ruleInst` at the specific args.  This
    avoids the BRA-Deriv form `mkAp2T sT (cor a)(cor b) = cor (s a b)`
    that would fail for non-Pair-like steppers.

**This pattern dissolves the `ih_s_bra` issue.**  For Rec at Pair input,
we apply the same pattern: embed `Df_F2_s` as a Fun2 sub-component in
the chain, and use `Th12_F2 s` (encoded) at the bridge step.

## Why this works for ALL s constructors (one chain, not per-s)

`Th12_F2_X` exists for every Fun2 constructor X (Pair, Const, Lift,
Post, Fan, IfLf, TreeEq, RecP) as a UNIVERSAL-in-(x,v) Deriv.  The
encoded equation `thmT(Df_F2_X(x,v)) = codeFTeq2 X x v` always
includes the bridge from `mkAp2T (codeF2 X)(cor x)(cor v)` to
`cor(X x v)` — but at the **thmT-image level**, not as a BRA-Deriv
equation between Terms.

**The chain Df for Rec z s at Pair-input is ONE Fun1 expression
parametric in s** — not seven per-s files.  The Agda meta-function

```agda
Df_F2 : Fun2 -> Fun2     -- meta-dispatch: Pair -> Df_F2_Pair, etc.
```

embeds the per-Fun chain.  In the chain Fun1 expression, we write
`ap2 (Df_F2 s) orig recs` as a Fun2 sub-component (analogous to
TreeEq's `ap2 D_IfLf ...` in `y2T`).  At runtime, when s is concrete,
Df_F2 s reduces to the appropriate per-Fun Df_F2_X.

The proof of correctness uses `Th12_F2 s` (the per-s encoded
universal Deriv) at the bridge step via `ruleInst` at the specific
Rec-context inputs.  This is uniformly available for every Fun2
constructor.

**The Const counter-example doesn't apply** because we never need a
BRA-Deriv equation between mismatched-shape Terms.  The chain operates
at the encoded level throughout, and `Th12_F2 s` is always encoded-
level provable for every s.

## Concrete next-session work

### Step 1: read the TreeEq template (~30 min)

Files to study:

  * `BRA/Th12TreeEqNNFun.agda` — chain Fun2 with `D_IfLf` as
    sub-component.  This is the **shape** of the chain Df.
  * `BRA/Th12TreeEqNNReduce.agda` — reduction proof at NN input.
  * `BRA/Th12TreeEqBasePP.agda` — uses `Th12_F2_IfLf` ruleInst at the
    bridge step.
  * `BRA/Th12TreeEqClose.agda` — top-level closure delivering universal
    `Th12_F2_TreeEq`.

These ~5 files implement the pattern in ~1000 LoC.  Rec/RecP follow
the same shape.

### Step 2: build BRA/Th12RecCloseS.agda (~600-1000 LoC, 3-5 files)

Mirror Th12TreeEqClose's structure but for `Rec z s`:

  * `Th12RecNNFun.agda` — chain Fun1 at Pair input embedding `Df_F2_s`
    as sub-component.  Replace `step_inner`'s ih_s_bra-based emission
    with one that includes `ap2 Df_F2_s pairT (Pair rec_v1 rec_v2)`
    in the chain (analogous to `y2T` in TreeEqNNFun).
  * `Th12RecNNReduce.agda` — reduction proof at Pair input.
  * `Th12RecBasePP.agda` — bridge via `Th12_F2 s` ruleInst at
    `(pairT, Pair rec_v1 rec_v2)`.
  * `Th12RecClose.agda` — top-level closure: ruleIndBT atop pointwise
    lemmas to deliver universal `Th12_F1_Rec_zs : Deriv P_Th12_Rec_zs`,
    parametric in `(z, s, z_corLemma, z_closed, s_closed, Df_F2_s,
    Th12_F2_s_correctness)`.

### Step 3: build BRA/Th12RecPCloseS.agda (~600-1000 LoC, similar files)

Same pattern for RecP s.  Recursion is on the SECOND argument
(`(p, x)` form), so the structural pieces shift but the pattern is
identical.

### Step 4: build BRA/Thm12.agda (~200-400 LoC)

Replace the existing `BRA.Thm12.FromBridges`-based file with a clean
structural recursion:

```agda
record Thm12_F1_Result (f : Fun1) : Set where
  field
    Df    : Fun1
    proof : Deriv (atomic (eqn (ap1 thmT (ap1 Df (var zero)))
                               (codeFTeq1Asym f (var zero))))

record Thm12_F2_Result (g : Fun2) : Set where
  field
    Dg    : Fun2
    proof : Deriv (atomic (eqn (ap1 thmT (ap2 Dg (var zero)(var (suc zero))))
                               (codeFTeq2Asym g (var zero)(var (suc zero))))) 

thm12_F1 : (f : Fun1) -> Thm12_F1_Result f
thm12_F2 : (g : Fun2) -> Thm12_F2_Result g

thm12_F1 I       = ...  -- re-export Th12_F1_I
thm12_F1 Fst     = ...  -- re-export Th12_F1_Fst
thm12_F1 Snd     = ...  -- re-export Th12_F1_Snd
thm12_F1 Z       = ...  -- re-export Th12_F1_Z
thm12_F1 (Comp f g)     = ...  -- via Th12CompCase + thm12_F1 f + thm12_F1 g
thm12_F1 (Comp2 h f g)  = ...  -- via Th12Comp2Case + thm12_F2 h + thm12_F1 f + thm12_F1 g
thm12_F1 (Rec z s)      = ...  -- via Th12RecCloseS + thm12_F2 s
                                -- (requires z_corLemma, z_closed, s_closed
                                --  -- propagate as preconditions or
                                --  restrict to closed (z, s))

thm12_F2 Pair    = ...  -- re-export Th12_F2_Pair
thm12_F2 Const   = ...  -- re-export Th12_F2_Const
thm12_F2 (Lift f)       = ...  -- via Th12LiftCase + thm12_F1 f
thm12_F2 (Post f h)     = ...  -- via Th12PostCase
thm12_F2 (Fan h1 h2 h)  = ...  -- via Th12FanCase
thm12_F2 IfLf    = ...  -- re-export Th12_F2_IfLf
thm12_F2 TreeEq  = ...  -- re-export Th12_F2_TreeEq
thm12_F2 (RecP s)       = ...  -- via Th12RecPCloseS + thm12_F2 s
```

The Comp/Comp2/Lift/Post/Fan parametric modules expect per-x correctness
proofs.  Convert from universal (var-zero form) to per-x via ruleInst
+ eqSubst (closure of Df + closure of codeFTeq).  ~50-LoC helper for
this conversion.

For Rec/RecP, propagate `z_corLemma_for_O := corOfReify`-style
preconditions.  In practice consumers use closed-Tree z (typically
z = O), so these are dischargeable.

### Step 5: verification

  * Each new file <300 LoC, typecheck <5s.
  * Top-level `BRA/Thm12.agda` typechecks under 10s end-to-end.
  * Save memory: `project_thm12_universal_done.md`.

## Total estimated effort

  * Step 1 (read template): 30 min.
  * Step 2 (Rec close): 4-6 hours, 1 session.
  * Step 3 (RecP close): 4-6 hours, 1 session.
  * Step 4 (top-level): 1-2 hours.
  * Step 5 (verify): 30 min.

Total: 2-3 sessions.

## What's already in place (do not rebuild)

  * `BRA/CorF.agda` (359 LoC, 0.33s) — `corF1`/`corF2` mutual recursion
    producing simplified-cor results per constructor.  **Auxiliary
    helper** for BRA-Deriv equations within proofs (e.g., for
    `corOfPair`-style bridges).  NOT the main load-bearing construction.
  * `BRA/Th12RecUnivPair.agda` (89 LoC, 2.35s fresh / 0.20s cached) —
    unconditional Theorem 12 for `Rec O Pair` via the OLD ih_s_bra
    approach (Th12RecUniv.WithClosure).  **Demonstrates one specific
    case but does NOT generalize.**  The new `Th12RecCloseS.agda`
    supersedes it and works universally.
  * `BRA/Th12TreeEqClose.agda` + supporting (`Th12TreeEqNNFun.agda`,
    `Th12TreeEqNNReduce.agda`, `Th12TreeEqBaseLN.agda`,
    `Th12TreeEqBasePP.agda`) — universal `Th12_F2_TreeEq`.
    **The template to follow exactly.**  ~1000 LoC across 5 files,
    each <300 LoC, all <1s typecheck.
  * All per-Fun universal Th12 files (Th12I, Th12Z, Th12Fst, Th12Snd,
    Th12Pair, Th12Const, Th12IfLf, Th12TreeEqClose) — Fun1/Fun2 leaves
    DONE universally.
  * Parametric modules Th12CompCase, Th12Comp2Case, Th12LiftCase,
    Th12PostCase, Th12FanCase — Fun1/Fun2 composites DONE parametrically.

## Key pointers (avoid rediscovering)

  * `BRA.Thm12.FromBridges` (BRA/Thm12.agda lines 90-156) is
    **deprecated**.  Its `ih_s_bra`-equivalent design is exactly
    what we're replacing.  The new structural recursion sidesteps
    FromBridges entirely.  Don't try to repair FromBridges.
  * `ih_s_bra` (in BRA/Th12RecUniv.agda line 1140 and BRA/Th12RecPUniv.agda
    line 1106) is a parameter that **cannot be uniformly discharged
    in BRA-Deriv form** for non-Pair s.  Don't try to instantiate it
    universally.  The new chain Df doesn't need it.
  * `corF1`/`corF2` (BRA/CorF.agda) gives simplified-cor results per
    constructor.  Useful for BRA-Deriv equations within the chain
    proofs (e.g., when bridging cor of recursive sub-results).  Not
    a substitute for the Th12_F2_s encoded bridge.

## Pre-flight memory reads

  * `project_corf_landed` — what's in CorF.agda + Th12RecUnivPair.agda.
  * `project_th12_treeeq_close_done` — TreeEq pattern (this is the
    template).
  * `feedback_no_universal_thm12_via_frombridges` — why FromBridges
    doesn't work (refined).
  * `feedback_th14_needs_strict_thm12` — downstream Theorem 14 needs
    universal Theorem 12, which Goedel II requires.
  * `feedback_guard_fast_typecheck` — small files, fast typecheck.
  * `feedback_pre_flight_guard15` — verify Guard's Theorem 12 statement
    before starting.
