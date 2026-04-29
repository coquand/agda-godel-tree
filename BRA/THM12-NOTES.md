# Def 12 and Thm 12 — notes for review

Status: **not a validated plan; Phase 2 work**.  These are my
current reading of guard15 Def 12 (p.16) and Thm 12 (p.16),
written out so the user can check the interpretation before any
code is committed to `BRA/`.

**Scheduled for Phase 2** (after Gödel I / Thm 11; see
`BRA/EX24-DESIGN.md` for the Phase 1 / Phase 2 split).  This file
is the spec the eventual `BRA/CodeT.agda` (and the Thm 12 / 13 / 14
chain) will be coded against.  No code will be written from this
doc until Phase 1 is complete.

Companion to `BRA/EX24-DESIGN.md`.  Once the user confirms the
interpretation, the Thm 12 section of EX24-DESIGN.md should be
revised to reference this file (or this file folded in).

## Def 12 as a meta-level `codeT` / `codeFT` function

### Guard's statement (p.16)

> DEFINITION 12.  Suppose that ξ is a term (formula) in which the
> terms A_1, ..., A_n appear underlined.  Then by "ξ" we shall mean
> a term of BRA which is built up inductively as in Definition 10
> (Def. 11) with the exception that num(A_i) is used instead of
> "A_i".  Hence "ξ" is a term in just those variables which appear
> in A_1, ..., A_n.

And the worked example:

> E.g., "fx = g(hx, 0)"  ~>  3J(3J("f", numx)+1, num g(hx, 0)) .

and the self-consistency remark:

> Note that "sx" = "sx", since 3J("s", numx)+1 = num(sx) .

### How I read it

Def 12 defines a notation `"ξ"` that is NOT a closed natural (it is
not a single Gödel code), but rather **a BRA term** — i.e. an
element of our `Term` type.  When the free variables inside the
underlined sub-terms are later instantiated to specific numerals,
this BRA term evaluates to the genuine Gödel code of the substituted
formula.

The construction is **the usual Gödel coding with two exceptions:**

1. Numerals and constants are coded as closed tree values
   (same as Def 10/11).
2. Free variables `x_n` in underlined positions are coded as
   `num(x_n)` — a BRA *functor application* that stays unreduced
   as long as `x_n` is a variable.

For us, with Guard's `num = cor`:

```agda
codeT  : Term -> Term
codeT O           = ap2 Pair O O               -- = reify (code O); see Note A
codeT (var n)     = ap1 cor (var n)            -- symbolic, unreduced
codeT (ap1 f t)   = ap2 Pair (reify tagAp1)
                     (ap2 Pair (reify (codeF1 f)) (codeT t))
codeT (ap2 g a b) = ap2 Pair (reify tagAp2)
                     (ap2 Pair (reify (codeF2 g))
                       (ap2 Pair (codeT a) (codeT b)))

codeFT : Formula -> Term
codeFT (atomic (eqn l r)) = ap2 Pair (codeT l) (codeT r)
codeFT (not P)            = ap2 Pair (reify tagNeg) (codeFT P)
codeFT (P imp Q)          = ap2 Pair (reify tagImp)
                             (ap2 Pair (codeFT P) (codeFT Q))
```

**Note A: `codeT O`.**  An earlier draft of this doc had
`codeT O = O`.  That was wrong: `BRA/Term.agda` defines
`code O = nd tagO lf` with `tagO = lf`, so `code O = nd lf lf` and
`reify (code O) = ap2 Pair O O`, *not* `O`.  The constant `0`
codes-to-itself-modulo-the-tag-wrapper, mirroring Guard's
"0 -> 0" only in the structural sense, not literally.  Fixed in
the spec above.

### Why this matches Guard

**Guard's worked example.** For `ξ = "fx = g(hx, 0)"`, Def 12
computes `3J(3J("f", numx)+1, num g(hx, 0))`:

- `3J(·, ·)` is Guard's Gödel pairing.  In our tree setting, the
  Pair constructor *is* the pairing, so `3J(a, b)` becomes
  `ap2 Pair a b`.
- `3J("f", numx)+1` codes the application `f(underlined x)`.  Our
  analog: `ap2 Pair (reify tagAp1) (ap2 Pair (reify (codeF1 f))
  (ap1 cor (var 0)))` — where `ap1 cor (var 0)` is the symbolic
  `num(x)`.
- `num g(hx, 0)` is the more interesting half — fully unfolded
  below.

**Worked example: `num g(h x, 0)` in BRA.**  Take `g : Fun2`,
`h : Fun1`, `x = var 0`, `0 = O`.  The source term is
`ap2 g (ap1 h (var 0)) O`.  Apply codeT clause-by-clause:

    codeT (ap2 g (ap1 h (var 0)) O)
      = ap2 Pair (reify tagAp2)
          (ap2 Pair (reify (codeF2 g))
            (ap2 Pair (codeT (ap1 h (var 0)))
                      (codeT O)))

    codeT (ap1 h (var 0))
      = ap2 Pair (reify tagAp1)
          (ap2 Pair (reify (codeF1 h)) (codeT (var 0)))

    codeT (var 0) = ap1 cor (var 0)            -- THE symbolic cor
    codeT O       = ap2 Pair O O                -- = reify (code O)

Putting it together, `codeT (ap2 g (ap1 h (var 0)) O)` =

    ap2 Pair (reify tagAp2)
      (ap2 Pair (reify (codeF2 g))
        (ap2 Pair
          (ap2 Pair (reify tagAp1)
            (ap2 Pair (reify (codeF1 h))
              (ap1 cor (var 0))))                   -- only symbolic cor
          (ap2 Pair O O)))                          -- code of constant 0

**Properties to note.**

1. All structural tags (`tagAp1`, `tagAp2`, `codeF1 h`, `codeF2 g`)
   are closed reified trees -- they reify once at meta-build time
   and never reduce.
2. The constant `0` gets its honest code `ap2 Pair O O`
   (= `reify (code O)`).  It does *not* get wrapped in cor: `0` is
   already a closed numeral, so num/cor on it would just return
   its code, which we substitute directly at codeT-time.
3. The variable `x` (= var 0) is the unique spot where
   `ap1 cor (var 0)` appears symbolically -- *one* occurrence,
   exactly matching the *one* underlined variable in the source
   term.
4. Under `ruleInst x_0 := reify t`, the `ap1 cor (var 0)` becomes
   `ap1 cor (reify t)`, which reduces (by `corOfReify`) to
   `reify (code (reify t))` -- the genuine Gödel code of the
   numeral `reify t`.  The whole expression is then closed and
   equals the actual code of `g(h(numeral-of-t), 0)`.

**Counting cor's.**  The number of symbolic `ap1 cor (var n)`
slots in `codeT t` equals the number of free-variable occurrences
in `t`.  Each `ruleInst` step instantiating one variable to a
closed numeral fires exactly one cor (per occurrence of that
variable).  Bounded growth -- good for Thm 14's diagonal
manipulations.

**Connecting to Guard's `"sx" = num(sx)` self-consistency.**
Guard wrote `num g(h x, 0)` in two ways and showed they agree:
- as Def 12's recursive coding of the term `g(h x, 0)` (the
  unfolding above, with x underlined throughout);
- as `num` applied to the whole open term `g(h x, 0)`.

We follow the structural-unfolding reading for codeT because
(a) it's a total Agda recursion on Term, requiring no BRA proofs
to define; (b) BRA's `cor` (= `Rec falseT stepCor`) is not even
defined to reduce on open `ap1 f` / `ap2 g` -- it only reduces on
reified trees -- so the "apply num to the whole term" reading
isn't directly evaluable in BRA.  The two readings agree as BRA
terms (modulo Def 12's self-consistency observation), but
codeT's structural unfolding is the form we actually compute with.

**Guard's self-consistency "sx" = "sx".** Guard writes
`3J("s", numx)+1 = num(sx)`.  Reading the LHS via Def 12: `"sx"`
with `x` underlined = `3J("s", numx)+1`.  Reading the RHS directly:
`num(sx)` is the BRA functor `num` applied to the term `sx`.  The
equation says these two BRA terms are equal.

In our setting the analog is
`codeT (ap1 s (var 0)) = ap1 cor (ap1 s (var 0))` as BRA terms.
The LHS unfolds to `ap2 Pair (reify tagAp1) (ap2 Pair (reify
(codeF1 s)) (ap1 cor (var 0)))` via the `codeT (ap1 s t)` clause.
The RHS `ap1 cor (ap1 s (var 0))` has to be evaluated via axCorAp1
(if it existed) — but it doesn't exist in BRA/.

**And this is the key point.**  The equation `codeT (ap1 s (var 0)) =
ap1 cor (ap1 s (var 0))` is NOT stated in BRA.  It is the META-LEVEL
definition of `codeT` itself: `codeT (ap1 s t)` unfolds *by
definition* to exactly that structure.  Guard's "sx" = "sx" is
observing that his Def 12 is self-consistent — the underlined
notation applied to `sx` produces `num(sx)`, which is what Def 12's
third clause for "f(A)" would give if we treated all of `sx` as the
underlined sub-term.

So `codeT` in our setting is a **total recursive Agda function on
Term**, producing a BRA term with `ap1 cor (var n)` sitting at each
variable position.  It's a *specification* of what the underlined
code looks like, not something that requires BRA proofs to define.

### What `codeT` is NOT

- Not a BRA Fun1.  It's a meta-level Agda function.
- Not a function that needs cor to reduce.  The result is just a
  BRA term that happens to contain `ap1 cor (var n)` sub-terms.
- Not the same as `reify . code`.  `reify (code t)` produces a
  closed BRA term (all variable positions are coded to specific
  tree-shapes).  `codeT t` leaves `ap1 cor (var n)` unreduced.
  They agree only when `t` is closed (no `var n` occurrences).

## Thm 12 — existence of `Df` matching the underlined code

### Guard's statement (p.16)

> THEOREM 12.  For every singulary functor f there exists a
> singulary functor Df such that  th(Df(x)) = "fx = fx" .
> Similarly for every binary functor g there exists a binary
> functor Dg such that  th(Dg(x,y)) = "g(x,y) = g(x,y)" .
>
> Proof: The proof proceeds by a meta-induction on the length of
> the definition of a functor.  The details are left to the reader.

### How I read it

For each BRA singulary functor `f`, we construct another singulary
functor `Df` such that **the following equation between open BRA
terms in the variable `x`** is derivable in BRA:

```
th(Df(x))  =  "f(underlined x) = f(underlined x)"
```

Both sides are BRA terms containing `num(x) = cor(x)` as a
sub-term (at the variable position on the RHS; inside `Df(x)`'s
reduction chain on the LHS).

In our Agda:

```agda
thm12Sing : (f : Fun1) ->
  Sigma Fun1 (\ Df ->
    Deriv (atomic (eqn (ap1 th (ap1 Df (var zero)))
                       (codeFT (atomic (eqn (ap1 f (var zero))
                                            (ap1 f (var zero))))))))

thm12Bin : (g : Fun2) ->
  Sigma Fun2 (\ Dg -> (v0 v1 : Nat) ->
    Deriv (atomic (eqn (ap2 Dg (var v0) (var v1))
                       (codeFT (atomic (eqn (ap2 g (var v0) (var v1))
                                            (ap2 g (var v0) (var v1))))))))
```

(Type signatures sketched.  The binary case will need care about
which variables the functor Dg uses internally.)

### Why `cor` appears symbolically on BOTH sides

Unfolding the RHS for `f = I` at `var 0`:

```
codeFT (atomic (eqn (ap1 I (var 0)) (ap1 I (var 0))))
  =  ap2 Pair (codeT (ap1 I (var 0))) (codeT (ap1 I (var 0)))
  =  ap2 Pair S S
```

where

```
S  =  ap2 Pair (reify tagAp1)
         (ap2 Pair (reify (codeF1 I)) (ap1 cor (var 0)))
```

The sub-term `ap1 cor (var 0)` appears **inside S**, twice (once
per occurrence of `S`).

The LHS `ap1 th (ap1 Df (var 0))` is designed (by the choice of
Df) to reduce, via th's mod-4 dispatch and ax's axRefl-schema
case, to the same `ap2 Pair S S`.  When that unfolding reaches a
variable position, it will sprout `ap1 cor (var 0)` on the LHS
too — matching the RHS exactly.

The Deriv is closed by `axRefl` at each matched sub-term, plus the
chain of unfoldings.  At no point does `cor` need to *reduce* on
`var 0`.  It remains a functor-application symbol on both sides,
equal to itself.

### This justifies the design decision in BRA/Cor.agda

`BRA/Cor.agda` defines `cor = Rec falseT stepCor` which reduces
only on reified-tree inputs (= Guard's numerals).  Thm 12's
equations contain `ap1 cor (var n)` as syntactic sub-terms that
are never asked to reduce.  When `var n` is later instantiated via
`ruleInst` to some reified tree `reify t`, those `ap1 cor (reify t)`
sub-terms DO reduce (via `corOfReify`) — at that point we're in
Guard's "numeral" case of `num(n)`, which IS defined.  So cor's
restricted reduction behaviour is exactly right: reduces on
numerals, stays symbolic on variables, both matching Guard.

## Proof structure of Thm 12

Guard says "meta-induction on the length of the definition of a
functor."  The length of `f`'s definition is the BRA-constructor
depth.  Base cases are primitive functors; step cases are
composites.

### Base cases (primitive Fun1)

For each primitive Fun1 constructor, construct `Df` explicitly:

- `f = I`        — `D_I`  produces via th's ax-case the coded equation  `I(x) = I(x)` .
- `f = Fst`      — `D_Fst` similarly.
- `f = Snd`      — `D_Snd` similarly.
- `f = KT t`     — parametrised by `t : Term`; `D_{KT t}` uses `codeT t` somewhere.
- `f = Comp p q` — step case below.
- `f = Comp2 h p q` — step case below.
- `f = Rec z s` — step case below.

For the leaf primitives (`I`, `Fst`, `Snd`, `KT`), `Df(x)` is the
tree encoding an `axRefl` proof-index against the coded term
`f(underlined x)`.  This is where `ax` earns its keep: the code of
`Df(x)` is exactly what `ax` (the Ex 24 [6] axiom-selector) maps to
the coded `axRefl` theorem.

### Step cases (composite Fun1)

- `Comp p q` — given `D_p` and `D_q` by IH, construct `D_{Comp p q}`
  by plumbing `D_q`'s output (proof that `q(x) = q(x)`) through
  `D_p` (proof that `p(q(x)) = p(q(x))`), using `ax` schema for
  `axComp` and `mpF` / `indF` to thread the implications.
- `Comp2 h p q` — similar, with a binary-functor axiom schema.
- `Rec z s` — the primitive recursion step.  Needs `indF` (induction
  axiom schema) and `subT` (to substitute the recursive result in
  for the variable) to close.

Each step case is a few dozen lines of combinator plumbing given
the IH and the Ex 24 functors.

### Binary case (Thm 12 for Fun2)

Analogous to singulary, with `Dg` a Fun2 and a slightly more
elaborate `codeT` handling of the second argument.

## Open questions for the user

1. **Does `codeT` as specified above match Def 12?** Specifically:
   is `codeT (var n) = ap1 cor (var n)` the right clause, or should
   it be something else (e.g. `reify (code (var n))` which is closed
   but doesn't depend on n functionally)?  My reading says the
   former (to respect "num(A_i) is used instead of 'A_i'"), but this
   is the central interpretation choice.

2. **Does Thm 12's equation really hold between OPEN BRA terms in
   `var 0`, with `ap1 cor (var 0)` on both sides?** If yes, the
   whole plan is consistent.  If no (e.g. the equation is supposed
   to be between closed codes with `var 0` already instantiated),
   the picture changes and we need to rethink what "for every `x`"
   means.

3. **How does `indF`'s v' ambiguity (from the prior discussion)
   interact with the Rec step case in Thm 12?** The Rec step case
   proves Thm 12 for `Rec z s` given Thm 12 for `z` and `s`.  It
   uses `indF` to close an induction on the Rec argument.  The
   choice of `v'` in indF's spec (option A/B/C from the previous
   notes) may constrain how this step case plays out.

4. **What does the binary Thm 12 need that the singulary one
   doesn't?** Guard's binary `Dg(x, y)` quantifies over TWO
   variables.  Does the proof work uniformly, or does the second
   variable require extra machinery (e.g. a second instance of
   subT to handle the second variable's codeT occurrences)?

## Summary

If the interpretation above is correct:

- Def 12 is a **meta-level Agda function** `codeT` / `codeFT` that
  returns open BRA terms.  No BRA proofs required to define it.
- Thm 12 is a **theorem about open BRA equations** where `cor`
  appears on both sides as an unreduced functor-application symbol.
- The axCor* shortcut was wrong at two levels: wrong domain for
  `cor` (numerals only), and unnecessary because Thm 12 doesn't
  reduce `cor` anyway.
- `BRA/Cor.agda`'s current cor (reduces on reified trees, stays
  symbolic on variables) is exactly what's needed.

If the interpretation is wrong somewhere, this doc is the place to
correct it before any Thm 12 code lands.
