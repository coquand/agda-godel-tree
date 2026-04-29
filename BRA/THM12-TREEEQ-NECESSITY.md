# Why TreeEq is needed: an implicit gap in Guard's framework

## The proof-checking requirement

To make BRA's encoded theorem-enumerator `th` (Guard) / `thmT` (ours)
**executable as a proof checker**, we need to detect specific tag values
inside Gödel-numbered (or Term-encoded) proof trees:

- `th(4y) = ax(y)` vs `th(4y+1) = sb(...)` vs `th(4y+2) = mp(...)` vs
  `th(4y+3) = ind(...)` requires dispatching on which of the four cases
  the input falls into.
- Substitution operations (`sb`, `sub`, `sbf`, `sbt` in Guard;
  `subT`, `subEnc` in ours) need to recognise variable positions inside
  encoded terms — which means equality-testing tags against the
  "variable" tag.
- Diagonalisation (Theorem 11) requires substituting a Gödel number
  for a free variable inside a Gödel-numbered formula.

All of these operations require an **equality decision** on encoded
values: a primitive-recursive function returning `0`/`1` (Guard) or
`O`/`Pair O O` (ours) telling whether two encoded subterms are equal.

## Guard does not introduce it

In guard15.pdf pages 14–17, Guard lists his Gödel-number primitives
(`mp, sbt, sbf, sb, ind, ax, num, sub, J`) and stops.  He never
introduces an `eqNat : Nat → Nat → Bool` (or its `0/s0` analog).  His
syntactic operations (`sb`, `sub`, ...) are *defined* by case analysis
on encoded tag positions — but the case analysis itself, at the
primitive-recursive-function level, **requires an equality decision
that Guard does not write down**.

This is an implicit gap in the lecture: the framework needs equality
on naturals to make `th, sb, sub` concrete primitive recursive
functions, but Guard treats this as buried in the primitive-recursion
machinery and never names it.  It is "left to the reader" *twice* —
once for the primitive itself, once for its Theorem-12 case.

## Our codebase makes it explicit

We added `TreeEq : Fun2` as a primitive with four defining axioms:

    axTreeEqLL :                Deriv (atomic (eqn (ap2 TreeEq O O) O))
    axTreeEqLN : (a b : Term) → Deriv (atomic (eqn (ap2 TreeEq O (Pair a b)) (Pair O O)))
    axTreeEqNL : (a b : Term) → Deriv (atomic (eqn (ap2 TreeEq (Pair a b) O) (Pair O O)))
    axTreeEqNN : (a₁ a₂ b₁ b₂ : Term) →
                 Deriv (atomic (eqn (ap2 TreeEq (Pair a₁ a₂) (Pair b₁ b₂))
                                    (ap2 IfLf (ap2 TreeEq a₁ b₁)
                                              (ap2 Pair (ap2 TreeEq a₂ b₂)
                                                        (ap2 Pair O O)))))

`TreeEq` is then load-bearing inside `thmT`: every `checkTag_X` helper
(e.g., `checkTag_axI = Fan (Lift (KT tagCode_axI)) (Lift Fst) TreeEq`)
uses `TreeEq` to dispatch on which proof-encoding tag the input has.

Without `TreeEq` (or some equivalent equality decision), the proof
checker `thmT` cannot be defined.

## Why the tree setting makes it harder than Guard's Nat setting

On `Nat`, equality has a clean primitive-recursive definition via
`Rfgh`: outer recursion on first argument, inner navigation on second
via `pred`.  Linear recursion on naturals handles it.  So if Guard
*had* introduced `eqNat` explicitly, his Theorem-12 case for it would
follow the standard `Rfgh` template (outer + inner argument
linearised by `pred`).

On binary trees, equality is genuinely **diagonal**: at the
`(nd a₁ a₂) (nd b₁ b₂)` case, the recursion pairs `(a₁, b₁)` and
`(a₂, b₂)` — not "step both arguments together," and there is no
tree analog of `pred` that linearises one argument while you recurse
on the other.  Each tree has *two* substructures, not one predecessor.

This means `axTreeEqNN` does **not** fit the `Rec`/`RecP` Theorem-12
template that suffices for `Comp, Lift, Post, Fan, Const, IfLf,
Rec, RecP`, and atomic primitives.  And Guard's framework gives no
template for it because Guard never introduces the analog primitive.

## Implications

1. **`TreeEq` is genuinely primitive in our setting**, in a way it
   isn't in Guard's: the diagonal recursion on two trees is essential
   for proof checking, and there is no standard Nat-style derivation
   on trees.
2. **Theorem 12 for `axTreeEqNN` is a genuine architectural question
   not covered by Guard.**  The session note in
   `BRA/Thm12/TreeEqNN.agda` (lines 159–195) recording that the
   natural API extension `axInstReplace` is **unsound** at a concrete
   counterexample is the empirical signal that the obvious extensions
   do not work.
3. **Guard's "details left to reader" hides this gap.**  Pages 14–17
   give a template for the `Rec` and `Comp` style cases (via
   meta-induction on functor definition + the `ind` combinator for
   universal closure over numeric inputs), but no template for
   `eqNat` / `TreeEq` because Guard never introduces it.
