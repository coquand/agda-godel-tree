# Next session: complete schematic Theorem 12 for TreeEq

## What this session delivered (commit `93cb81e`)

1. **`ruleIndBT2` Deriv primitive** added to `BRA/Deriv.agda`:
   - 2D binary-tree induction with **diagonal** IHs at `(v1, v3)` and
     `(v2, v4)` in the `(Pair v1 v2, Pair v3 v4)` case.
   - Four base/step arguments: baseLL, baseLN-imp (with inner IHs),
     baseNL-imp (with outer IHs), basePP-imp (with diagonal IHs).
   - Required for TreeEq's `axTreeEqNN` recursive structure.

2. **`tagRuleIndBT2 = 45`** in `BRA/Thm/Tag.agda` for completeness.
   Currently unused by the dispatch — see (3).

3. **`encodeRich` case in `BRA/Thm/ThmT.agda`** for `ruleIndBT2`:
   - Reuses `tagRuleIndBT`'s slot via `thmTDispRuleIndBT_param`.
     (Body extracts `Fst (Snd a) = codeFormula P`; the rest of the
     payload is opaque, so we pack the four sub-encodings into the
     `y_step_T` slot.)
   - Avoids adding 100+ lines of skipAtTag chain for a new tag.
   - ThmT.agda still typechecks in ~8s (under the 10s budget).

## Mathematical assessment (CRITICAL — read before next session)

Before charging in, the previous session's handoff
(`NEXT-SESSION-TREEEQ-THM12.md`) recommended **pattern (c)** — design
`Df_F2_TreeEq` as a self-recursive Fun2 whose chain Df at NN
auto-supplies cross-IHs.  **This pattern does not apply to TreeEq.**

Reason: BRA's Fun2 grammar (`I, Fst, Snd, Const, Comp, Comp2, Lift,
Post, Fan, KT, Rec, RecP, IfLf, TreeEq, Pair`) has no diagonal
recursor.  `TreeEq` itself has the right diagonal axiom but
returns a Bool-Term, not a chain payload — and takes no `step`
argument.  No combination of these primitives yields a "step-receiving
diagonal recursor".

So a self-recursive `Df_F2_TreeEq` whose chain Df at NN places
`(ap2 Df_F2_TreeEq v_i w_j)` at IH slots is **not expressible** in
BRA's Fun2 grammar.  This is the genuine mathematical obstruction
that motivates pattern (a) (= the new `ruleIndBT2` primitive).

## What's already in `BRA/Thm12/Parts/TreeEq.agda` (Construction module)

`Parts/TreeEq.Construction` is parametric over a `D_TreeEq_NN_fun :
Fun2`, its closure lemma, and the **concrete pointwise NN proof**
`D_correct2_TreeEq_NN_pt : (p q a b : Term) -> Deriv (...)`.  It
already provides:

- `D_TreeEq` (closed Fun2 with IfLf cascade dispatching on shape).
- `D_TreeEq_reduce_OO` / `LN` / `NL` / `NN` (BRA-equality reductions).
- `bridgeLL` / `LN` / `NL` (bridges from `parOutAxTreeEq*` to
  `codeFTeq2_TreeEq`).
- `D_correct2_TreeEq_LL` / `LN` / `NL` (concrete pointwise).
- `D_correct2_TreeEq_NN` (parametric on `_NN_pt`).
- `D_correct2_TreeEq_univ` (universal closure via NESTED ruleIndBT
  + ruleInst — works because outer IHs aren't needed; the universal
  closure happens via inner ruleIndBT on a renamed Q-formula).

**Key observation:** Construction's `D_correct2_TreeEq_univ` works
parametrically on `D_correct2_TreeEq_NN_pt`.  If we can supply a
concrete `D_correct2_TreeEq_NN_pt` (the unconditional NN proof at
arbitrary closed `(p, q, a, b)`), the universal closure is free.

But proving `D_correct2_TreeEq_NN_pt` unconditionally is impossible
(it needs cross-IHs at sub-args).  So we **bypass Construction's
universal closure** and use `ruleIndBT2` directly.

## The path forward

### Approach: use ruleIndBT2 directly (bypass Construction.univ)

Construct `Th12_F2_TreeEq : Deriv P_Th12_TreeEq` via:
```
Th12_F2_TreeEq = ruleIndBT2 P_Th12_TreeEq v1 v2 v3 v4
                  baseLL_proof
                  baseLN_imp
                  baseNL_imp
                  basePP_imp
```

where:
- `baseLL_proof = D_correct2_TreeEq_LL` (lifted via Eq-subst to
  match `substF (suc zero) O (substF zero O P_Th12_TreeEq)`).
- `baseLN_imp` = `D_correct2_TreeEq_LN (var v3)(var v4)` lifted to
  the implication form via `axK` (inner IHs not needed; axTreeEqLN
  is direct).  ~30 LoC of axK + Eq-subst plumbing.
- `baseNL_imp` = analogous, using `D_correct2_TreeEq_NL`.  ~30 LoC.
- `basePP_imp` = the heavy lift: ~400-600 LoC.

### `basePP_imp` design

Signature:
```
basePP_imp : Deriv (
  substF (suc zero) (var v3) (substF zero (var v1) P_Th12_TreeEq) imp
    (substF (suc zero) (var v4) (substF zero (var v2) P_Th12_TreeEq) imp
     substF (suc zero) (ap2 Pair (var v3) (var v4))
                       (substF zero (ap2 Pair (var v1) (var v2)) P_Th12_TreeEq)))
```

After substF-simplification, this is:
```
[IH at (v1, v3)] imp ([IH at (v2, v4)] imp [goal at (Pair v1 v2, Pair v3 v4)])
```

Inside this implication, the diagonal IHs give us:
- `IH1 : thmT(Df_F2_TreeEq (var v1)(var v3)) = codeFTeq2Asym TreeEq (var v1)(var v3)`.
- `IH2 : thmT(Df_F2_TreeEq (var v2)(var v4)) = codeFTeq2Asym TreeEq (var v2)(var v4)`.

Goal:
```
thmT(Df_F2_TreeEq (Pair (var v1)(var v2))(Pair (var v3)(var v4)))
  = codeFTeq2Asym TreeEq (Pair (var v1)(var v2))(Pair (var v3)(var v4))
```

Strategy:
1. Reduce LHS via `D_TreeEq_reduce_NN`:  `Df_F2_TreeEq (Pair v1 v2)(Pair v3 v4)
   = D_TreeEq_NN_fun (Pair v1 v2)(Pair v3 v4)` BRA-eq.  (1 line via
   `cong1 thmT (D_TreeEq_reduce_NN ...)`.)
2. Now goal is `thmT(D_TreeEq_NN_fun (Pair v1 v2)(Pair v3 v4))
   = codeFTeq2Asym TreeEq (Pair v1 v2)(Pair v3 v4)`.
3. Build a chain Df Term using:
   - `tagCode_axTreeEqNN`-encoded payload (= encoded axTreeEqNN
     equation).
   - `tagCode_ruleTrans` to chain steps.
   - Cross-IHs (via `parDispCong*` lemmas) to substitute
     `mkAp2T cf2 (cor v_i)(cor v_j) ↔ cor(TreeEq v_i v_j)`.
   - `corOfPair`, `cong1 cor`, `axTreeEqNN` reversed under cor.
4. Use existing `thmTDispRuleTrans_param`,
   `thmTDispCongL_param`, `thmTDispCongR_param`, etc.

### `D_TreeEq_NN_fun` design

Closed Fun2 emitting at `(Pair v1 v2)(Pair w1 w2)` a chain Df Term
that bridges `mkAp2T cf2 (cor (Pair v1 v2))(cor (Pair w1 w2))` ↔
`cor(TreeEq (Pair v1 v2)(Pair w1 w2))` via cross-IH substitution
and axTreeEqNN.

Suggestion:
```
D_TreeEq_NN_fun = Fan (Lift (KT tagCode_ruleTrans))
                       inner_NN_dispatch
                       Pair
```

where `inner_NN_dispatch` extracts v1, v2, w1, w2 via
`Lift Fst, Lift Snd, Post Fst Recs, Post Snd Recs` (where Recs =
Post Snd Pair) and assembles the chain payload using `Fan` /
`EmitPair` combinators.

The chain payload (after the outer `tagCode_ruleTrans` wrapper) has
at least 3 sub-equations:
- E1: `mkAp2T cf2 (cor (Pair v1 v2))(cor (Pair w1 w2)) =
       mkAp2T cf2 (mkAp2T pCT (cor v1)(cor v2))(mkAp2T pCT (cor w1)(cor w2))`
       (via `corOfPair` ⨯2).
- E2: bridges the cor-of-Pair form to `cor(TreeEq (Pair v1 v2)(Pair w1 w2))`
      via axTreeEqNN reversed under cor + IHs.

Total chain Df construction ~150-200 LoC.

### Estimated scope for basePP_imp

- D_TreeEq_NN_fun (closed Fun2): ~50 LoC.
- D_TreeEq_NN_fun closed-form lemma (substF2 commutes): ~30 LoC.
- D_TreeEq_NN_fun reduction at (Pair v1 v2)(Pair w1 w2): ~80 LoC
  (Fan + axLift + axKT + projection-extracting reductions).
- Chain Df at NN (~3-5 ruleTrans steps): ~150-200 LoC.
- Cross-IH bridges (parDispCong* + IH application): ~100 LoC.
- substF / Eq-rewrites for the implication form: ~50 LoC.
- **Total: ~400-500 LoC for basePP_imp + supporting infrastructure.**

## File structure recommendation

Following the project's "small files" convention:

- `BRA/Th12TreeEqNN_fun.agda` (~80 LoC): closed `D_TreeEq_NN_fun` +
  closure lemma + reduction at (Pair v1 v2)(Pair w1 w2).
- `BRA/Th12TreeEqBaseLN.agda` (~60 LoC): baseLN_imp from
  `D_correct2_TreeEq_LN` lifted via axK + Eq-subst.
- `BRA/Th12TreeEqBaseNL.agda` (~60 LoC): analogous.
- `BRA/Th12TreeEqBasePP.agda` (~250-300 LoC): basePP_imp.  May need
  to split further if it grows.
- `BRA/Th12TreeEqUniv.agda` (~150 LoC): the `ruleIndBT2` wiring +
  `Th12_F2_TreeEq : Deriv P_Th12_TreeEq`.

Each file should typecheck in <2s.

## Phase C (Thm12.FromBridges) follow-up

Once `Th12_F2_TreeEq` exists, the `BRA/Thm12.agda` `FromBridges`
parameter `D_correct2_TreeEq_univ` can be discharged by:
1. Plug `D_TreeEq_NN_fun` into `Construction.D_TreeEq` (= our
   `Df_F2_TreeEq`).
2. Use `Th12_F2_TreeEq` + `ruleInst` at any concrete (x, v) to
   produce `D_correct2_TreeEq_pt`.
3. Wire into `FromBridges`.

Similar discharge work for Rec / RecP universal (already done in
Th12RecUniv / Th12RecPUniv).

## Reasonable session goal

- Phase 1 (this session): ruleIndBT2 primitive in place. ✅
- Phase 2 (next session): `D_TreeEq_NN_fun` + reduction (~150 LoC)
  + baseLN_imp + baseNL_imp lifters (~120 LoC).  Half a session.
- Phase 3: `basePP_imp` chain Df construction (~400 LoC).  Full
  session.
- Phase 4: ruleIndBT2 wiring + `Th12_F2_TreeEq` (~150 LoC).  Half
  session.
- Phase 5: Thm12.FromBridges discharge for TreeEq (~50-100 LoC).
  Quarter session.

Total ~3 sessions.  Pattern (a) IS the unavoidable path; subsequent
sessions are mechanical engineering.

## Verification + ground truth

- Construction's existing `D_correct2_TreeEq_univ` is a **template**:
  the same outer ruleIndBT structure, but here we use ruleIndBT2 to
  inject diagonal IHs into the basePP case directly.
- The `Parts/TreeEq.Construction` module's pointwise reductions
  (`D_TreeEq_reduce_LL/LN/NL/NN`) are reusable.
- The bridges (`bridgeLL/LN/NL`) are reusable for the LL/LN/NL
  base cases.

## Ground rules (per user, 2026-04-30)

- Pattern (a) is unavoidable. ✅ Done via ruleIndBT2 primitive.
- Small files where possible (≤250 LoC).
- Fast typecheck (< 10s per file).
- Maximally modular.
- Stop only on a mathematical obstacle.  None identified for
  the chain Df construction.
