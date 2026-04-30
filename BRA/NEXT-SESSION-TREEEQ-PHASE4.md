# Next session: Phase 4 (basePP_imp) for Theorem 12 TreeEq

## What this session delivered

1. **Refactor of `BRA/Thm12/Parts/TreeEq.agda`**: split the monolithic
   `module Construction` into:
   - `module ConstructionBase` (parametric on `D_TreeEq_NN_fun` +
     closure only) — provides `D_TreeEq`, `D_TreeEq_closed`, all
     reductions (`_OO`/`_LN`/`_NL`/`_NN`), bridges (`_LL`/`_LN`/`_NL`),
     and pointwise correctness `D_correct2_TreeEq_LL/LN/NL`.
   - `module Construction` extends ConstructionBase with `NN_pt` and
     keeps the existing `D_correct2_TreeEq_NN`, `_univ`, `_TreeEq`
     (via the old nested ruleIndBT route).
   - `Thm12.agda` is unaffected (Construction's interface is
     backward-compatible).

2. **Phase 3 — base lifters**:
   - `BRA/Th12TreeEqBaseLN.agda` (110 LoC, 0.24s) — `baseLN_imp` at
     fixed v3Nat=4, v4Nat=5. Wraps `D_correct2_TreeEq_LN` via two
     `mp/axK` weakenings.
   - `BRA/Th12TreeEqBaseNL.agda` (90 LoC, 0.24s) — `baseNL_imp` at
     fixed v1Nat=2, v2Nat=3. Mirror of BaseLN.

3. **Phase 5 framework**:
   - `BRA/Th12TreeEqUniv.agda` (76 LoC, 0.24s) — `baseLL_proof` (the
     `D_correct2_TreeEq_LL` aligned via eqSubst), `BasePPType` (the
     signature of basePP_imp), and `Th12_F2_TreeEq_param` which calls
     `ruleIndBT2` parametrically on basePP_imp.

4. **Defined fresh-variable indices** (load-bearing for Phase 4
   typechecking):
   - v1Nat = 2 (suc (suc zero))
   - v2Nat = 3 (suc (suc (suc zero)))
   - v3Nat = 4 (suc (suc (suc (suc zero))))
   - v4Nat = 5 (suc (suc (suc (suc (suc zero)))))

## Mathematical assessment of Phase 4 (the heavy lift)

### Why this is harder than the doc estimated

The doc estimated ~400-500 LoC for basePP_imp.  Closer inspection
reveals **a subtle structural issue** that pushes this to ~700-800 LoC.

#### The issue with the current `D_TreeEq_NN_fun`

`BRA/Th12TreeEqNNFun.agda`'s `D_TreeEq_NN_fun` emits:
```
Pair tagCode_axTreeEqNN (Pair v1 (Pair v2 (Pair w1 w2)))
```
i.e. `parEncAxTreeEqNN v1 v2 w1 w2` with **plain** v1, v2, w1, w2.

Then `parDispAxTreeEqNN` produces `parOutAxTreeEqNN v1 v2 w1 w2` whose
LHS_form is:
```
mkAp2T cf2 (mkAp2T pCT v1 v2)(mkAp2T pCT w1 w2)
```
with **plain** v_i — but the goal's LHS reads:
```
mkAp2T cf2 (cor (Pair v1 v2))(cor (Pair w1 w2))
  = mkAp2T cf2 (mkAp2T pCT (cor v1)(cor v2))(mkAp2T pCT (cor w1)(cor w2))  [by corOfPair]
```
with **cor-encoded** variables.  The IHs say `thmT(D_TreeEq v_i w_j) =
codeFTeq2 v_i w_j`, i.e. `Pair (mkAp2T cf2 (cor v_i)(cor w_j))(cor
(TreeEq v_i w_j))` — so the IH provides cor-encoded LHS components.

**Mismatch**: parOutAxTreeEqNN's LHS has plain v_i, codeFTeq2's LHS has
cor v_i.  No direct bridge in BRA from `v_i` to `cor v_i` for free
variables — cor of free variables is opaque.

#### Two possible fixes

**Option A (redesign D_TreeEq_NN_fun, ~50 LoC + invalidates 41d857e)**
Change `inner_payload_NN` to apply cor at each variable extraction:
```
inner_payload_NN_cor =
  Fan (Lift (Comp cor Fst))                          -- cor v1
       (Fan (Lift (Comp cor Snd))                    -- cor v2
             (Fan (Post (Comp cor Fst) (Post Snd Pair)) -- cor w1
                   (Post (Comp cor Snd) (Post Snd Pair)) -- cor w2
                   Pair)
             Pair)
       Pair
```
This makes parDispAxTreeEqNN emit parOutAxTreeEqNN (cor v1)(cor v2)(cor w1)(cor w2)
which DOES match codeFTeq2's LHS via corOfPair.

**Option B (chain Df bridge in basePP_imp, ~700-800 LoC)**
Build a ruleTrans-chained Df_chain in basePP_imp that explicitly bridges
plain v_i to cor v_i positions.  This is the harder route.

**Recommendation: Option A**.  Smaller, cleaner, and matches
Construction's caseLN/caseNL pattern (which apply cor at extraction
time via `Comp cor Fst` / `Comp cor Snd`).

### Phase 4 strategy with Option A

After redesigning `D_TreeEq_NN_fun`:
- LHS bridge: 2x corOfPair (= `axRecNd O stepCor` + stepCorRed) folds
  `mkAp2T pCT (cor v_i)(cor v_j)` into `cor (Pair v_i v_j)`.
- RHS bridge: harder.  parOutAxTreeEqNN's RHS_form is the encoded
  IfLf-Pair-TreeEq Term (with cor-encoded args).  We need to bridge it
  to `cor (TreeEq (Pair v1 v2)(Pair w1 w2))`.

Strategy for RHS bridge:
- axTreeEqNN reversed gives `IfLf (TreeEq v1 w1)(Pair (TreeEq v2 w2)(Pair O O))
  = TreeEq (Pair v1 v2)(Pair w1 w2)`.
- cong1 cor lifts to `cor (IfLf ...) = cor (TreeEq (Pair v1 v2)(Pair w1 w2))`.
- We need: `mkAp2T (codeF2 IfLf) (mkAp2T cf2 (cor v1)(cor w1)) (...) = cor (IfLf ...)`.
- `cor (IfLf A B)` is opaque on applied-IfLf Terms.  cor's Rec defining
  equations only fire on `O` and `Pair a b`.

**This is the actual mathematical obstacle.**  cor does NOT have a
defining equation for IfLf, TreeEq, Pair-of-applications etc.  The RHS
of axTreeEqNN — `IfLf (TreeEq v1 w1)(Pair (TreeEq v2 w2)(Pair O O))` —
is an applied Term, NOT a tree.  cor on it stays opaque.

So `cor (TreeEq (Pair v1 v2)(Pair w1 w2))` cannot be reduced to
`mkAp2T (codeF2 IfLf) ...` syntactically.

#### Way forward: the IH's encoded equation form

The IH at (v1, w1) gives us `thmT(D_TreeEq v1 w1) = codeFTeq2 v1 w1`,
which equals `Pair (mkAp2T cf2 (cor v1)(cor w1)) (cor (TreeEq v1 w1))`.
This is an **encoded equation Term**: it represents the BRA-equation
`mkAp2T cf2 (cor v1)(cor w1) = cor (TreeEq v1 w1)`.

To USE this as a BRA-equation step, we'd need a thmT-dispatch lemma
that extracts the encoded equation and produces the underlying Deriv.

But this would require: from `thmT(D_TreeEq v1 w1) = encoded equation
form` (an Agda equality of Terms), derive `Deriv (atomic (eqn LHS_code
RHS_code))` — i.e., promote thmT-image equality to a Deriv equation.

Is there such a lemma in the codebase?  Looking at thmTDispCong* and
thmTDispRuleTrans, these go the OTHER way: from a Deriv on a chain Df,
they derive that thmT of the chain equals certain encoded forms.

**Genuine obstacle**: we want to DERIVE that `mkAp2T cf2 (cor v1)(cor
w1)` equals `cor (TreeEq v1 w1)` as a BRA-equation, given that
`thmT(D_TreeEq v1 w1) = codeFTeq2 v1 w1`.  This is a **soundness
claim** for thmT — that thmT's output is a "valid encoded equation
representing a BRA theorem".  Such soundness might not be a direct
lemma in the codebase.

### Re-assessment

The Phase 4 path needs a careful look at whether basePP_imp can be
constructed at all in the current ThmT framework, OR whether we need:
- (a) A new thmT-soundness lemma extracting BRA equations from encoded
  forms.
- (b) A different design for the chain Df that exposes the cor-encoded
  RHS directly.
- (c) A different formulation where IHs are presented in a directly
  usable equational form (e.g., extract Fst and Snd projections from
  the encoded equation Term).

The Th12RecPUniv basePair pattern (referenced in NEXT-SESSION-TREEEQ-CONT.md)
uses thmTDispCongL/CongR_param to thread IHs through chain Df slots —
but those lemmas require the IH's chain Df Term to be a known Pair-shape,
not a soundness-style extraction.

**Next session priority**: re-examine Th12RecP.basePair's exact mechanism
(specifically how `IH2RecP.shape` and `IH2RecP.image` together let
parDispCongL_param thread the IH's encoded image into a larger chain).
If the same mechanism applies to TreeEq's diagonal IHs, basePP_imp is
~700-800 LoC of mechanical engineering.  If not, identify the minimal
new lemma or design change needed.

## Files delivered (this session)

- `BRA/Thm12/Parts/TreeEq.agda` — refactored: `ConstructionBase` + `Construction`.
- `BRA/Th12TreeEqBaseLN.agda` — `baseLN_imp` (110 LoC).
- `BRA/Th12TreeEqBaseNL.agda` — `baseNL_imp` (90 LoC).
- `BRA/Th12TreeEqUniv.agda` — Phase 5 framework, parametric on basePP_imp (76 LoC).
- This document.

All four typecheck under 1s each.

## Phase 6 outline (after Phase 4 lands)

Once `Th12_F2_TreeEq : Deriv P_Th12_TreeEq` exists (= Th12_F2_TreeEq_param
applied to actual basePP_imp), discharge Thm12.FromBridges' TreeEq
parameters as follows:

1. Plug in our concrete `D_TreeEq_NN_fun` and `D_TreeEq_NN_closed`
   (already exist in `BRA/Th12TreeEqNNFun.agda`).
2. Derive `D_correct2_TreeEq_NN_pt p q a b` via:
   ```
   ruleTrans (cong1 thmT (ruleSym (D_TreeEq_NN_reduce p q a b)))
             (ruleInst (suc zero) (Pair a b)
                        (ruleInst zero (Pair p q) Th12_F2_TreeEq))
   ```
   — but careful with the substF computation (will need eqSubst alignment
   like baseLL_proof).
3. Provide `D_correct2_TreeEq_univ` directly from Th12_F2_TreeEq via
   ruleInst at (x, v).  Construction.D_TreeEq with our NN_pt should
   definitionally equal CB.D_TreeEq — verify via refl.
