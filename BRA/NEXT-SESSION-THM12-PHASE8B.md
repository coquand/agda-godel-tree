# Next session — Theorem 12 Phase 8b (IfLf + TreeEq shapes)

## What just got delivered (Phase 8a)

`BRA/Thm12/ShapeF1Fst.agda` (215 LoC) and `BRA/Thm12/ShapeF1Snd.agda`
(187 LoC) ship the two atomic Fun1 shape lemmas needed by FromBridges'
Comp2 dispatch, both via `fromBaseAndPair` + a `pair_eta` lemma:

```agda
pair_eta (a b : Term) ->
  Deriv (atomic (eqn (ap2 Pair a b)
                     (ap2 Pair (ap1 Fst (ap2 Pair a b))
                               (ap1 Snd (ap2 Pair a b)))))
```

Both proved in 0.36s.  Witnesses: x' = `Fst (Fst (Df_F1_X x))`, y' =
`Snd (Fst (Df_F1_X x))`.

## What remains (estimated ~700 LoC)

### Phase 8b.1 — `BRA/Thm12/ShapeF2IfLf.agda` (~300-400 LoC)

D_IfLf has 4 dispatch cases (LL, LN, NL, NN) — needs nested ruleIndBT
(NOT ruleIndBT2 — see `BRA/Thm12/Parts/IfLf.agda:957` `D_correct2_IfLf_univ`
for the template).  At each leaf case the result is a concretely
Pair-shaped `parEncAxIfLf*` term, so `pair_eta` applies as in Phase 8a.

The shape formula uses TWO free variables (var 0 = x, var 1 = v):
```agda
P_shape_IfLf : Formula
P_shape_IfLf =
  atomic (eqn (ap1 Fst (ap2 D_IfLf (var 0) (var (suc zero))))
              (ap2 Pair (ap1 Fst (ap1 Fst (ap2 D_IfLf (var 0) (var (suc zero)))))
                        (ap1 Snd (ap1 Fst (ap2 D_IfLf (var 0) (var (suc zero)))))))
```

Pattern from `BRA/Thm12/Parts/IfLf.agda` (line 760+):
- Define `shape_at_LL`, `shape_at_LN`, `shape_at_NL`, `shape_at_NN` (each
  closely mirrors shape_lf in Phase 8a, using D_IfLf_reduce_OO etc.).
- Inner ruleIndBT on var 1 (= v) lifts LL+LN to "x = O" form, NL+NN to
  "x = Pair _ _" form.
- Outer ruleIndBT on var 0 (= x) lifts to universal form.

Use `D_IfLf_reduce_OO`, `D_IfLf_reduce_LN`, `D_IfLf_reduce_NL`,
`D_IfLf_reduce_NN` from `BRA/Thm12/Parts/IfLf.agda`.

### Phase 8b.2 — `BRA/Thm12/ShapeF2TreeEq.agda` (~300-400 LoC)

D_TreeEq similarly has 4 cases plus a recursive case (NN dispatches
diagonally).  Mirror `BRA/Th12TreeEqClose.agda` structure.  Use
`ruleIndBT2` (diagonal 2D induction) to absorb the 4 cases of TreeEq's
defining equations.

The recursive case (TreeEq (Pair v1 v2)(Pair u1 u2) = ...) uses
`axTreeEqNN` whose RHS is `IfLf (TreeEq v1 u1) (Pair (TreeEq v2 u2)(Pair O O))`
— still concretely Pair-shaped at the outer level (the encoded equation
sits in the OUTER position of the Fan output, regardless of branching).

The IH absorption pattern follows `BRA/Th12TreeEqClose.agda`'s use of
axK to discard cross-IHs at non-recursive shape steps.

## Phase 9 — Thm12 finalization (separate from shapes; ~500 LoC)

Once all 4 shape lemmas land:

1. Add per-x adapters via ruleInst (one for each universal Th12_F1_X /
   Th12_F2_X form):
   ```agda
   per_x_Fst : (x : Term) -> Deriv (atomic (eqn (ap1 thmT (ap1 Df_F1_Fst x))
                                                (codeFTeq1Asym Fst x)))
   per_x_Fst x = ... -- ruleInst zero x Th12_F1_Fst, then eqSubst chain
   ```
2. Provide closure suppliers `z_closed_supplier`, `s_closed_supplier`,
   `z_corLemma_for` (the latter via `corOfReify` from `BRA/Cor.agda` for
   `z = reify t`).
3. Build `BRA/Thm12Final.agda` instantiating `BRA.Thm12.FromBridges`
   with all parameters.
4. Verify `thm12_F1 thmT` and `thm12_F2 sb` typecheck.

## Critical gotcha

The shape lemmas use `Fst (Fst (Df_F1_X x))` and `Snd (Fst (Df_F1_X x))`
as the witnesses x' and y' respectively.  This works because the inner
`Fst (Df_F1_X x)` is itself Pair-shaped (by axFst on the runtime tree).
DO NOT try to use `x' = Fst (Df_F1_X x)` directly — that requires
proving `Df_F1_X x` is Pair-shaped, which adds a level.  The
double-Fst trick avoids the issue.

## Starting commands

```bash
cd /Users/coquand/CHWISTEK
agda BRA/Thm12/ShapeF1Fst.agda  # 0.36s — verify Phase 8a is intact
agda BRA/Thm12/ShapeF1Snd.agda  # 0.36s
# Then start ShapeF2IfLf.agda by copying ShapeF1Fst.agda's structure
# and adapting to nested ruleIndBT + 4 leaf cases.
```
