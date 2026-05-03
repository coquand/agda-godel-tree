# Next session — Thm 12 for TreeEq, universal form, no closure args

## Success criterion (single line)

A closed Agda value of the following type, exported from
`BRA.Thm12.Parts.TreeEq` (or a successor module), with no postulates,
no holes, no module parameters, no closure arguments, no restrictions
on `x` or `v`:

```agda
D_correct2_TreeEq : (x v : Term) ->
  Deriv (atomic (eqn (ap1 thmT (ap2 D_TreeEq x v)) (codeFTeq2_TreeEq x v)))
```

The signature must match `D_correct2_Pair`, `D_correct2_Const`,
etc. exactly — universally quantified over both `x` and `v`, no extra
inputs.  Once delivered, callers (e.g. `BRA.Thm12.FromBridges` TreeEq
case) drop the `TreeEq_xeq1` parameter entirely.

## Goal

Replace the current `BRA.Thm12.Parts.TreeEq.D_correct2_TreeEq` (which
takes FOUR closure args `xeq0`, `veq0`, `veq1`, `xeq1`) with the
closure-free universal form above.

## Why the closure args are currently there (artifact)

Same pattern as IfLf: TreeEq's defining axioms are shape-dispatched on
both inputs:

- `axTreeEqLL` : `ap2 TreeEq O O = O`
- `axTreeEqLN a b` : `ap2 TreeEq O (Pair a b) = Pair O O`
- `axTreeEqNL p q` : `ap2 TreeEq (Pair p q) O = Pair O O`
- `axTreeEqNN a1 a2 b1 b2` : `ap2 TreeEq (Pair a1 a2) (Pair b1 b2) = …`

Four shape cases (LL, LN, NL, NN).  The current proof
(`BRA/Thm12/Parts/TreeEq.agda` ~800 lines) uses nested `ruleIndBT` on x
and v, plus four closure args `xeq0, veq0, veq1, xeq1` to discharge the
substitution residues left by the sequential `ruleInst`s in the
universal-from-schematic conversion.

The closure args are an artifact of:
1. Schematic proof at `(var 0, var 1)` via nested `ruleIndBT`.
2. Sequential `ruleInst` at `var 0 := x` then `var 1 := v` to get the
   universal form, which substitutes `var 1` (and `var 0`) inside `x`
   and `v` themselves if they contain those variables.

The diagonal recursive case `axTreeEqNN` (TreeEq of Pair-Pair recurses
on sub-tree pairs) is what motivated `ruleIndBT2` (BRA primitive,
`BRA/Deriv.agda:249`).  TreeEq is exactly the canonical use case for
`ruleIndBT2`.

## Suggested approach

Use `ruleIndBT2` directly at universal `(x, v)`.  The four
`ruleIndBT2` cases (baseLL, baseLN, baseNL, basePP with diagonal IHs
at `(v1, v3)` and `(v2, v4)`) align directly with the four TreeEq
shape cases.  Existing per-shape proofs:

- `D_correct2_TreeEq_LL` (line 560)
- `D_correct2_TreeEq_LN a b` (line 566)
- `D_correct2_TreeEq_NL p q` (line 574)
- `D_correct2_TreeEq_NN p q a b` parametric on `D_correct2_TreeEq_NN_pt`
  (a parametric closure plumbing the diagonal IHs into the basePP
  case via existing `Th12_F2_TreeEq_NN_pt` machinery in
  `BRA/Th12TreeEqBasePP.agda`).

Once `ruleIndBT2` produces `Deriv P` at `(var 0, var 1)`, deriving the
universal `(x v : Term) -> Deriv ...` form should follow without the
four-closure-arg artifact, by structuring the proof so the
schematic-to-universal conversion doesn't require the two-step
`ruleInst` artifact.  Plausible structures (mirroring IfLf):

1. **Schematic packaging.**  Replace `D_correct2_TreeEq` with a single
   `Deriv P_at_var0_var1` value (closure-free).  Adapt callers
   accordingly.

2. **Direct universal proof.**  Use `ruleIndBT2` with fresh indices for
   `v1, v2, v3, v4` to avoid the var-0/var-1 ruleInst conflict.

3. **ruleInst at fresh indices.**  Prove the schematic at fresh `(var
   k1, var k2)` (k1, k2 != 0, 1) and convert via `ruleInst k1 x` then
   `ruleInst k2 v`.

## Existing pieces to reuse

- `D_TreeEq : Fun2` (in `BRA.Thm12.Parts.TreeEq` via
  `ConstructionBase`).
- `D_correct2_TreeEq_LL`, `D_correct2_TreeEq_LN`,
  `D_correct2_TreeEq_NL` (atomic per-shape lemmas).
- `D_correct2_TreeEq_NN p q a b` parametric in
  `D_correct2_TreeEq_NN_pt` (the diagonal-IH plumbing).
- `Th12_F2_TreeEq_NN_pt v1 v2 v3 v4 …` from
  `BRA/Th12TreeEqBasePP.agda` (basePP_NN proof).
- `D_TreeEq_reduce_NN p q a b`, `D_TreeEq_closed`, `subst_reify`,
  `Fun1_closed`, `Fun2_closed` (BRA.SubstClosure).
- `ruleIndBT2 : (P : Formula) (v1 v2 v3 v4 : Nat) -> …` (BRA Deriv
  primitive).
- `feedback_treeeq_needs_indBT2.md` memory note: TreeEq's diagonal
  recursive case needs `ruleIndBT2`; single-variable `ruleIndBT` is
  insufficient for the diagonal IHs.

## Verification target

```agda
D_correct2_TreeEq : (x v : Term) ->
  Deriv (atomic (eqn (ap1 thmT (ap2 D_TreeEq x v)) (codeFTeq2_TreeEq x v)))
```

(no closure args.)  After this, `BRA.Thm12.FromBridges` becomes
discharge-able for the TreeEq case without any closure parameter,
which removes the TreeEq side of the global Theorem 12 obstruction for
`thmT` and `sub`.

## Constraints

* ASCII only.
* `{-# OPTIONS --safe --without-K --exact-split #-}`.
* No postulates, no holes, no with-abstraction, no dot patterns.
* Do not weaken any other theorem.

## See also

`BRA/NEXT-SESSION-THM12-IFLF.md` (analog for IfLf, simpler atomic case
without diagonal recursion).
