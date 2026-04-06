# Analysis: Eliminating the 108s instForm2 Computation

## The problem

`instForm2` in `SubstTForPrecomp.agda` proves by `refl` that double
substitution (v11, v12) on an equation containing `cstf` and `substTFor`
yields the expected closed form. This takes 108s because Agda must
materialize `reify crTC` (~400K Term nodes) and traverse it.

This computation has no counterpart in Rose or Guard's mathematical proofs.

## Why the mathematical proof avoids it

Rose/Guard never compute a specific numeral. They prove:

1. `reify` produces closed terms (general property of the coding)
2. `subst` is identity on closed terms (general property)
3. `substTFor` with parameters substituted equals `closedSubstTFor` (algebraic)
4. `thFunTFor` contains `substTFor` only in its case-23 branch (structural)

All of these are schematic — they hold for any value of `crTC`.
The specific ~400K-node tree is never materialized.

## What we proved (instant, ~0.1s each)

### SubstReify.agda
```
substReify : (x : Nat) (r : Term) (t : Tree) ->
  Eq (subst x r (reify t)) (reify t)
```
By induction on `t`. Works for any tree, including abstract ones.

### SubstTForClose.agda
```
substTForClose : (replT tgtT : Tree) ->
  Eq (substF1 v11 (reify replT) (substF1 v12 (reify tgtT) substTFor))
     (closedSubstTFor (reify replT) (reify tgtT))
```
The v12-first order is critical: `substReify` is only needed on `tgtT`
(small), never on `replT` (which can be the huge `crTC`).

### ThFunTForSubst.agda
```
thFunTForSubst : (replT tgtT : Tree) ->
  Eq (substF1 v11 (reify replT) (substF1 v12 (reify tgtT) thFunTFor))
     (thFunTForClosed replT tgtT)
```
Propagates `substTForClose` through thFunTFor's 26-branch dispatch chain
to case-23 (the ruleInst case, which uses `substTFor`). Only that one
case changes.

### InstForm.agda
```
instFormGen : (replT tgtT : Tree) (pa pb tc : Tree) ->
  Eq (substEq v11 (reify replT) (substEq v12 (reify tgtT)
      (eqn (ap2 TreeEq (ap1 thFunTFor (ap2 Pair (reify pa) (reify pb)))
                        (ap1 substTFor (reify tc)))
           poo)))
     (eqn (ap2 TreeEq (ap1 (thFunTForClosed replT tgtT) ...)
                       (ap1 (closedSubstTFor ...) (reify tc)))
          poo)
```
Fully general bridge. All tree arguments are universally quantified.
No computation on any specific tree.

## The remaining obstacle

The current `instForm2` has `cstf` in its TYPE:
```
Eq (substEq v12 ... (substEq v11 ... (eqn ... cstf ... substTFor ...)))
   (eqn ... cstf ... cstf ...)
```

Any proof with `cstf` in the type forces Agda to unfold
`cstf = closedSubstTFor (reify crTC) (reify (natCode v1))`,
which requires computing `reify crTC` (~400K nodes). This is
unavoidable — Agda needs to know the structure of `cstf` to type-check.

Attempted alternatives and their timings:
- `instForm2 = refl` (original): 108s
- Compositional with `substReify` on crTC: 129s (3 traversals)
- Compositional with `substClosedSTF`: 298s (substClosedSTF forces reify crTC)
- Compositional with `eqCong cStepOf`: 344s (type matching forces reify crTC)

All approaches that mention `cstf` in the type are >= 108s.

## The path to zero

Restructure `GodelII.agda` to avoid `cstf` in substituted equations:

**Current proof:**
1. `instD`: TreeEq(thFunTFor(enc), substTFor(reify TC)) = poo
2. `step1`: TreeEq(cstf(reify TC), substTFor(reify TC)) = poo
   (from `chain` + instD; introduces cstf)
3. `step2`: TreeEq(cstf(reify TC), cstf(reify TC)) = poo
   (from ruleInst v11/v12 on step1; needs instForm2, 108s)

**Proposed restructure:**
1. `instD`: TreeEq(thFunTFor(enc), substTFor(reify TC)) = poo
2. `instD2`: TreeEq(thFunTForClosed(enc), cstf(reify TC)) = poo
   (from ruleInst v12,v11 on instD; uses instFormGen, instant)
3. Bridge `thFunTForClosed(enc) = cstf(reify TC)` via chain
4. `step2`: TreeEq(cstf(reify TC), cstf(reify TC)) = poo

Step 2 uses `instFormGen` which is instant (no `cstf` in the source
equation). The bridge in step 3 requires showing that
`thFunTForClosed(enc)` agrees with `thFunTFor(enc)` for the specific
proof encoding `enc` — since `enc` doesn't exercise the case-23 branch
in a v11/v12-dependent way, the substituted and original thFunTFor give
the same result on `enc`.

This last point needs either:
- A general lemma that thFunTForClosed and thFunTFor agree on all inputs
  that don't contain v11/v12 (requires a closed-term predicate)
- A ruleInst at the Deriv level on `chain` itself
- An observation that `chain` holds for thFunTForClosed too (since
  `corrPf` from thm14E works for any thFunTFor variant with the same
  coding behavior on proof trees)

## Key insight

The mismatch between the mathematical proof and the formalization is
NOT about substitution complexity. It is about WHEN `cstf` enters the
proof. Rose never substitutes into an expression containing the closed
proof predicate — he substitutes the open template, then applies the
diagonal property. The formalization does it in the opposite order.

Swapping the order is the mathematically correct fix. The `instFormGen`
infrastructure (SubstReify + SubstTForClose + ThFunTForSubst + InstForm)
provides the instant schematic bridge for the swapped order. The
remaining work is restructuring GodelII.agda to use this order.

## File inventory

| File | Lines | Time | Role |
|------|-------|------|------|
| SubstReify.agda | ~120 | 0.1s | substReify + substClosedSTF |
| SubstTForClose.agda | ~45 | 0.1s | substTForClose (v12-first) |
| ThFunTForSubst.agda | ~210 | 0.1s | thFunTForSubst + thFunTForClosed |
| InstForm.agda | ~50 | 0.1s | instFormGen (general bridge) |
| DerivSize.agda | ~85 | 0.1s | Schema F size = 113/125 |
