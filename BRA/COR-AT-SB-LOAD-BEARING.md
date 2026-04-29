# `cor`'s defining equation is load-bearing at sb-substitution
# steps in Theorem 14

Session: 2026-04-26 (continuation of fresh-derivation session).

This document records a precise finding about *where* Guard uses
the specification of `num` (= our `cor`) in the proof of Theorem 14,
and what implication this has for our Agda formalisation.

## The specification of `num` / `cor`

Guard's `num : Nat -> Nat` (Exercise 24 [7], guard15.pdf p.14) is
a primitive recursive functor with defining equations:
  * `num(0) = '0'`
  * `num(s n) = 3J('s', num n) + 1`

Read: `num n` is the Gödel code of the numeral `s^n 0`.  Equivalently,
the term whose Gödel code is `num n` IS `s^n 0`.

Our analog `cor : Fun1` (BRA/Cor.agda) has the analogous defining
property (`corOfReify`, BRA/Cor.agda:82):
  * `cor (reify lf) = reify (code (reify lf))`
  * `cor (reify (nd a b)) = reify (code (reify (nd a b)))`

Read: for any Tree `t`, `cor (reify t) = reify (code (reify t))`.
i.e., the Gödel code of the canonical Term `reify t` equals
`cor (reify t)`'s value.  Equivalently, the Term whose Gödel code
is `cor (reify t)` IS `reify t`.

## Where `num` (resp. `cor`) is used in Theorem 14

Trace through Guard's Theorem 14 proof (guard15.pdf p.16-17).  At
each step we ask: "is num's specification (= num n is the code of
s^n 0) being used?"

### Steps 1, 2: "by Theorem 13"

  * **Step 1:** `th(x) = j ⊃ th(Dth(x)) = 'th(x_) = j'`.
  * **Step 2:** `th(Dsub(i,i)) = 'sub(i,i) = j'`.

These are direct invocations of Theorem 13.  Theorem 13's proof
chain is:
```
f(x) = y ⊢ th(Df(x))
        = 3J(3J('f', num x)+1, num(f x))   -- by Theorem 12
        = 3J(3J('f', num x)+1, num y)      -- by hypothesis f(x) = y
        = 'fx_ = y'                         -- Definition 12 notation
```

The hypothesis-substitution step `num(f x) → num y` uses **`cong1 num`
applied to the hypothesis `f(x) = y`** — pure congruence.  It does
NOT inspect num's defining equations; num is treated as a black-box
Fun1.

**So Theorem 13 does NOT use num's specification.**

### Step 3: combine via mp encoding

`g(x) = 4J(Dsub(i,i), 4J(Dth(x), f(x))+2)+2`.  Two layers of mp.
th unfolds via Definition 12 (`th(4y+2) = mp(th(K y), th(L y))`) and
mp's defining equation discharges the antecedent-matching.

For mp to chain: the antecedent of f's encoded implication
`'th(x_) = j ⊃ ...'` must match the consequent of step 1
`'th(x_) = j'`.  Both are parametric-in-x via `num x` / `cor x`.
**They match because they share IDENTICAL parametric structure**
— both have `num x` (resp. `cor x`) at the underlined-x position.

This requires *consistent parametricity* but not num's defining
equation specifically.

### Layer-3 of f(x): the FIRST genuine use of num's specification

`f(x) = ... 4J(J(num j, 2), t)+1 ...` — the innermost layer.

`y_3 = J(J(num j, 2), t)`.  Per Definition 12:
```
th(4 y_3 + 1) = sb(KKy_3, LKy_3, th(L y_3))
              = sb(num j, 2, th(t))
              = sb(num j, 2, "x_0 = x_2 ⊃ x_1 = x_2 ⊃ x_0 = x_1")
```

By sb's defining equation (Ex.24 [4]):
```
sb(("A", n), "P") = "P[x_n := A]"
```
i.e., sb replaces x_n in P **with the term A whose Gödel code is the
substituent**.  Here the substituent is `num j` and we need to
identify *which term has Gödel code num j*.

**This is the load-bearing use of num's specification:**
by `num(0) = '0'` and `num(s n) = 3J('s', num n)+1`, the term whose
Gödel code is `num j` is exactly `s^j 0`.  So the substitution
gives:
```
sb(num j, 2, "x_0 = x_2 ⊃ x_1 = x_2 ⊃ x_0 = x_1")
  = "x_0 = s^j 0 ⊃ x_1 = s^j 0 ⊃ x_0 = s^j 0"
```
which Guard writes as `'x_0 = j ⊃ x_1 = j ⊃ x_0 = x_1'` (the `j`s
on the RHS are `num j` per Definition 12 convention, matching
`s^j 0`'s Gödel encoding).

**Without num's specification this step doesn't decode** — sb at
substituent `num j` would be just "substitute the numeral whose value
is num j" — the meaning of which is opaque without the bridge to
"the term s^j 0".

### Layer-1 of f(x): parametric use of num's specification

The outermost layer of f(x) is sb at substituent `'th(x_)'` =
`3J('th', num x)+1`, with var-index 0.

For this to decode meaningfully, we need: the term whose Gödel code
is `3J('th', num x)+1` is `th(s^x 0)` — i.e., th applied to the
parametric numeral s^x 0.

This rests on:
  * The encoding scheme `'f t' = 3J('f', 't')+1` with `'t'` = code of
    t — application encoding.
  * Recognising `num x` at the argument slot as "the code of the
    numeral s^x 0" — num's specification.

So Layer 1 also uses num's specification, parametrically in x.

### Step 4: ANOTHER critical use of num's specification

Step 4: `th(x) = j ⊃ th(4J(J(num x, 1), x)+1) = 'th(x_) ≠ sub(i,i)'`.

The functor `4J(J(num x, 1), x)+1` is sb-shape with substituent
`num x`, var-index 1, sub-witness `x`.  Per Definition 12:
```
th(4 y + 1) = sb(num x, 1, th(x))
            = sb(num x, 1, j)        -- under hypothesis th(x) = j
```

By sb's defining equation:
```
sb(num x, 1, j) = "j with x_1 replaced by (the term whose code is num x)"
                = "j with x_1 replaced by s^x 0"           -- by num's spec
                = "th(s^x 0) ≠ sub(i,i)"                    -- since j = "th(x_1) ≠ sub(i,i)"
                = 'th(x_) ≠ sub(i,i)'                       -- Definition 12 notation
```

**Without num's specification, the result of `sb(num x, 1, j)` is
"j with x_1 replaced by some term" — but which term?  Only num's
specification answers it.**

### Step 5: combines steps 3, 4 + more sb's via mp

The outer mp's chain together step-3-output and step-4-output via
matching parametric structures.  No new use of num's specification
beyond what's already in steps 3, 4.

### Closure: ruleInst Con + propositional combination

Closure uses ruleInst on Con (= `th(y) ≠ "0=1"`) at `y := F(x)`,
and propositional combination with step 5 to get
`Deriv (th(x) ≠ j)`.  No new use of num's specification.

## Summary: where it enters

`num`'s specification is used at exactly the **sb-substitution steps**
where the substituent is `num`-of-something:

| Step | Substituent | Variable index | Purpose |
|------|-------------|----------------|---------|
| Layer 3 of f(x) | `num j` (closed) | 2 | substitute `s^j 0` for x_2 |
| Layer 2 of f(x) | `'sub(i,i)'` (closed numeral) | 1 | substitute `sub(i,i)` for x_1 |
| Layer 1 of f(x) | `'th(x_)' = 3J('th', num x)+1` | 0 | substitute `th(s^x 0)` for x_0 |
| Step 4 | `num x` (parametric) | 1 | substitute `s^x 0` for x_1 |
| Layer 2 of h(x) | `'sub(i,i)'` (closed numeral) | 1 | substitute `sub(i,i)` for x_1 |
| Layer 1 of h(x) | `'th(x_)'` | 0 | substitute `th(s^x 0)` for x_0 |

(Layer 2 substituents `'sub(i,i)'` and `'numeral encodings of closed values'`
are also via num's specification at the META level — `'sub(i,i)'` is
itself num applied to the value sub(i,i) = j, so it's `num j` in
disguise.  But that's the same use as Layer 3.)

**So num's specification is used at precisely 6 places in Theorem 14
(actually 4 distinct uses, since Layers 1 and 2 of h(x) repeat the
patterns of f(x)).**

## Implication for the Agda formalisation

In our setting (`cor : Fun1` instead of `num`), `cor`'s specification
(the defining property `corOfReify` in `BRA/Cor.agda:82`) plays the
analogous role.

For each use site above, the Agda proof must invoke `corOfReify` (or
its parametric form) to transition between:
  * "the Tree-value of `cor x` at `x = reify v`" (= `code (reify v)`)
  * "the Term whose Gödel code is `code (reify v)`" (= `reify v`)

Without this bridge, the sb-substitution doesn't reduce to the
intended parametric formula.

### Two encoding routes

In the existing closed-input dispatch encoding (`BRA/Thm/Parts/`),
substituents at sb-style slots are stored as **closed Trees via
`code t`** for some Term t.  E.g., `encRuleInst x t y_h` has
`code t` in the substituent slot.  This closed-Tree storage is
**OK for Hilbert-style instantiation** (where t is a Term and we
substitute the actual Term t into the conclusion), but it does
NOT match Guard's parametric-numeral substitution (where the
substituent IS `num x` parametrically).

To formalise Theorem 14 faithfully to Guard, we likely need an
**alternative set of encoding constructors** where the sb-substituent
slot stores the substituent as a *Term-level expression* (e.g.,
`ap1 cor x`), not via `code`.  These constructors thread `cor` through
parametrically.

### The bridge derivation

At each sb-step, the Agda proof requires a derivation of the form
```
Deriv (atomic (eqn (sb-substituted-encoded-formula)
                   (parametric-encoding-of-substituted-formula)))
```
where:
  * LHS is "the sb-application's value evaluated symbolically".
  * RHS is "the Definition-12 underlined-encoding of the substituted
    formula".

The bridge comes from:
  * The defining property of sb (closed reduction on the formula
    structure).
  * `corOfReify` applied at the substituent positions.
  * Congruence to propagate.

**This bridge derivation is what makes the chain go through.**  It
is provable in BRA, parametric in `x`, using only:
  * sb's defining equation (per BRA/Sub.agda's `subDef`, generalised
    to parametric-substituent variants).
  * `corOfReify` (closed instance) + `cong1 cor` for parametric
    propagation.
  * Standard structural rules (axEqTrans, axEqCong*, etc.).

## Action items

1. **Document the cor-bridge derivation lemma** for each sb-step
   shape in Theorem 14.  Six instances, but only ~3 distinct shapes
   (closed-numeral substituent, parametric-num substituent, parametric-
   th-of-num substituent).

2. **Add parametric encoding constructors** (sb-flavour) that store
   substituents as Term expressions (e.g., `ap1 cor x`), not via
   `code`.  Or alternatively, prove parametric-substituent dispatch
   lemmas for the existing constructors.

3. **Sketch D and D_correct for simplest cases** (next document /
   section), identifying exactly where the bridge is invoked.

The cor-bridge derivation is the **technical content** of Guard's
"meta-induction on the length of the definition of a functor"
(Theorem 12 proof, "details left to the reader").  It is exactly
what's needed to make D's per-case correctness go through.
