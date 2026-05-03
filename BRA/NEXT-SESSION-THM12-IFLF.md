# Next session — Thm 12 for IfLf, universal form, no closure args

## Success criterion (single line)

A closed Agda value of the following type, exported from
`BRA.Thm12.Parts.IfLf` (or a successor module), with no postulates,
no holes, no module parameters, no closure arguments, no restrictions
on `x` or `v`:

```agda
D_correct2_IfLf : (x v : Term) ->
  Deriv (atomic (eqn (ap1 thmT (ap2 D_IfLf x v)) (codeFTeq2_IfLf x v)))
```

The signature must match `D_correct2_Pair`, `D_correct2_Const`,
etc. exactly — universally quantified over both `x` and `v`, no extra
inputs.  Once delivered, callers (e.g. `BRA.Thm12.FromBridges` IfLf
case) drop the `IfLf_xeq1` parameter entirely.

## Goal

Replace the current `BRA.Thm12.Parts.IfLf.D_correct2_IfLf` (which takes
a closure arg `xeq1 : Eq (subst (suc zero) v x) x`) with the
closure-free universal form above.

## Why the closure arg is currently there (it's an artifact)

The current proof in `BRA/Thm12/Parts/IfLf.agda` is heavy (~1000 lines,
nested `ruleIndBT` on both x and v) because it does case analysis on
the SHAPES of both inputs:

- `axIfLfL` : `ap2 IfLf O b = O` (when first arg is leaf)
- `axIfLfN x y a' b'` : `ap2 IfLf (Pair x y) b = ap1 Fst b` (when first
  arg is a node)
- ... and similar shape-dispatched cases on the second argument

So there are 4 shape cases (LL, LN, NL, NN), each handled by a different
IfLf axiom, and the universal proof glues them via two nested
binary-tree inductions. That's where the bulk comes from — **not** from
any recursion of IfLf itself, but from the shape dispatch in IfLf's
defining axioms.

The closure arg `xeq1 : Eq (subst (suc zero) v x) x` that pollutes
`D_correct2_IfLf` is also **not intrinsic to IfLf's logic** — it's an
artifact of how `D_correct2_IfLf` is currently derived: by
`ruleInst`-ing the schematic `D_correct2_IfLf_univ` (which lives at
`(var 0, var 1)`) twice in sequence, where the second `ruleInst` (at
`var 1` with substituent `v`) reaches into `x` if `x` contains `var 1`.
A cleaner derivation that doesn't go through that two-step `ruleInst`
would not need `xeq1`.

IfLf is conceptually simple (atomic, 4 shape cases).  The complexity
in the current file is from shape dispatch and from the artifact
closure — neither of which reflects deep mathematical content.

## Suggested approach

Use `ruleIndBT2` (BRA primitive in `BRA/Deriv.agda` line 249) directly
on the pair `(x, v)` to prove the universal form in one go, without the
two-step `ruleInst` artifact.

`ruleIndBT2` takes 4 cases (LL, LN, NL, PP with diagonal IHs) and
produces `Deriv P` where `P` has var 0 and var 1 free.  The four cases
align directly with IfLf's four shape dispatches:

| Case | x       | v       | IfLf axiom |
|------|---------|---------|------------|
| LL   | O       | O       | axIfLfL    |
| LN   | O       | Pair…   | axIfLfL    |
| NL   | Pair…   | O       | axIfLfN    |
| PP   | Pair…   | Pair…   | axIfLfN    |

Each case reduces to a direct combinator-level proof (existing
`D_correct2_IfLf_LL`, `D_correct2_IfLf_LN`, `D_correct2_IfLf_NL`,
`D_correct2_IfLf_NN` already in `Parts/IfLf.agda`).  No nested
ruleIndBT, no xeq1 closure.

After ruleIndBT2 produces `Deriv P` at `(var 0, var 1)`, deriving the
universal `(x v : Term) -> Deriv (P at x v)` form should be possible
**without** xeq1 if the proof is structured to use ruleIndBT2 in a way
that avoids the two-step ruleInst artifact.  Plausible structures:

1. **Schematic packaging.**  Replace `D_correct2_IfLf` with a single
   `Deriv P_at_var0_var1` value (closure-free).  Adapt callers (FromBridges,
   composite per-case modules) to use schematic IH instead of universal.

2. **Direct universal proof.**  Prove the universal Pi-form using
   `ruleIndBT2` and a different conversion that avoids the var-0/var-1
   ruleInst conflict.  E.g., use fresh variable indices for the
   inducted vars in `ruleIndBT2` (it takes `v1, v2, v3, v4 : Nat`
   parameters — pick fresh ones).

3. **ruleInst at fresh indices.**  Prove `D_correct2_IfLf_univ` at
   fresh `(var k1, var k2)` where `k1, k2` aren't `0` or `1`, then
   convert to universal `(x v : Term) -> Deriv ...` via `ruleInst k1 x`
   then `ruleInst k2 v`.  The xeq1 issue arose because the schematic
   was at `(var 0, var 1)` and the second ruleInst at `var 1` reached
   into `x`; at fresh indices, the second ruleInst doesn't reach into
   x (assuming x has no `var k2`).  This still has a "no `var k2` in x"
   restriction in principle — but in practice for terms not using high
   indices, refl.  May still need a closure arg if we want truly
   universal.

## Existing pieces to reuse

- `D_IfLf : Fun2` (already defined, line 112).
- `D_IfLf_reduce_OO`, `D_IfLf_reduce_LN`, `D_IfLf_reduce_NL`,
  `D_IfLf_reduce_NN` (combinator reductions).
- `D_correct2_IfLf_LL`, `D_correct2_IfLf_LN`, `D_correct2_IfLf_NL`,
  `D_correct2_IfLf_NN` (per-shape correctness lemmas, lines 761-...).
- `ruleIndBT2 : (P : Formula) (v1 v2 v3 v4 : Nat) -> ...` (BRA Deriv
  primitive, `BRA/Deriv.agda:249`).

## Verification target

```agda
D_correct2_IfLf : (x v : Term) ->
  Deriv (atomic (eqn (ap1 thmT (ap2 D_IfLf x v)) (codeFTeq2_IfLf x v)))
```

(no closure args.)  After this, `BRA.Thm12.FromBridges` becomes
discharge-able for the IfLf case without any closure parameter, which
removes the IfLf side of the global Theorem 12 obstruction for `thmT`
and `sub`.

## Constraints

* ASCII only.
* `{-# OPTIONS --safe --without-K --exact-split #-}`.
* No postulates, no holes, no with-abstraction, no dot patterns.
* Do not weaken any other theorem.

## See also

`BRA/NEXT-SESSION-THM12-TREEEQ.md` (analog for TreeEq).
