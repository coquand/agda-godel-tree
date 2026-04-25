# Safe-default obligation on code-level auxiliary functions

Session date: 2026-04-26.

This is a standalone record of an independently-valid observation
that emerged during corrected-thmT design discussion.  It applies
**regardless of which thmT architecture is ultimately chosen** —
original Rec-based thmT, corrected Fst-based thmT, or any future
redesign.  The observation lives at the level of mp / sb / ax / ind
(the code-level auxiliary functors) and is orthogonal to the thmT
question.

(The corrected-thmT design itself — `BRA/THMT-CORRECTED-DESIGN.md` —
is currently under review pending re-reading of Guard's Theorems
12-14.  This note's content survives that review.)

## The observation

Guard's Exercise 24 specifications for `mp`, `sbt`, `sbf`, `sb`,
`ind`, `ax`, `num`, `sub` are **partial**.  Each says what the
function does on *valid* inputs (e.g., `mp("P", "P ⊃ Q") = "Q"`)
and is silent on malformed cases (second argument not an implication
code, antecedent doesn't match, sub-pieces are junk).

When implementing these as primitive recursive functors in BRA, the
implementer has to choose what happens on malformed inputs.  Two
options:

1. **Naive**: just compute via the structural recursion, accept
   whatever falls out.  Example: `mp(a, b) = Snd(Snd b)` regardless
   of `b`'s shape.

2. **Safe-default**: route malformed inputs to a default theorem
   code (typically `code(0=0)`).  Example:
   ```
   mp(a, b) = if (Fst b = tagImp ∧ Snd(Fst(Snd b)) = a)
              then Snd(Snd b)
              else code(0=0)
   ```

## Why naive breaks Goedel II

With naive `mp`, consistency Con (`∀y. th(y) ≠ code(bot)`) is
**refutable** in BRA: the closed junk tree
```
y_bad = Pair (mp_naive anything (encode-of-Pair-of-anything-and-code(bot)))
             (Pair tagMpT garbage)
       = Pair code(bot) (Pair tagMpT garbage)
```
satisfies (in any thmT design that returns the stored conclusion or
otherwise computes via mp_naive on this input):
```
Deriv (atomic (eqn (ap1 thmT (reify y_bad)) (reify (codeFormula bot))))
```
which BRA derives via `axFst` on the outer Pair.  ruleInst Con at
y_bad gives a contradiction.  So `Deriv Con → Deriv bot` is
vacuously true (because Deriv Con is impossible).  Goedel II
becomes a vacuous statement, not the substantive theorem.

## Why Guard's argument depends on safe defaults

Guard claims **"th(0), th(1), … enumerates the Gödel numbers of
all and only the theorems of BRA"** (p.15, just before Thm 11).
The "only theorems" half requires that *every* value of th is a
theorem code.  With naive `mp`, `sb`, etc., this fails: junk inputs
to th (which still trigger Definition 12's recursive equations)
can cascade into auxiliaries that produce arbitrary garbage,
including `code(0=1)`.

Guard's text doesn't spell out safe defaults.  But his Theorem 14
proof depends on Con being a non-trivial hypothesis — i.e., Con
not being refutable in BRA.  This is only true if every Definition-12
clause produces theorem codes, not garbage.  So safe defaults are
implicitly required.

## What "safe defaults" means concretely

For each auxiliary, route non-matching shapes to `code(0=0)` (or
some other fixed theorem code).  Concrete sketches:

* **mp**: check `Fst b = tagImp` AND `Snd(Fst(Snd b)) = a`; on
  success return `Snd(Snd b)`, else `code(0=0)`.
* **sb**: check that the formula argument has a recognised outer
  formula tag (tagAtom / tagNeg / tagImp); on success do
  codedSubst, else `code(0=0)`.
* **ax**: enumerate the recognised axiom indices; for unrecognised
  Nat indices return `code(0=0)`.
* **ind**: similarly check that base/step sub-proofs have the right
  shape relative to the induction principle; default to `code(0=0)`
  on mismatch.

The shape checks are TreeEq comparisons on closed structural data;
they reduce on closed inputs (and don't break parametric reasoning
on inputs whose relevant shape pieces are themselves closed).

## Implementation cost

Adding safe defaults to an existing auxiliary is mechanical: wrap
the body in `IfLf` conditioning on the shape check, with `code(0=0)`
in the failure branch.  Per auxiliary: ~10-30 LoC of additional
combinator wrapping plus the shape check.  Doesn't change the
auxiliary's behavior on valid inputs — only specifies what happens
on malformed ones.

## What this observation does NOT depend on

* Whether thmT is Rec-based (current) or Fst-based (corrected design).
* Whether constr5 has type `Fun1`, `Term → Term`, or `Tree → Tree`.
* Whether step 5 is parametric in BRA Term or meta-Pi over Tree.
* Whether the closure uses Hilbert-style ruleInst or some other
  mechanism.

The safe-default obligation is structural to the auxiliaries
themselves and is required for **any** faithful formalisation of
Guard's Theorem 14.

## Next-session relevance

When the abstract chain is re-architected (after Guard re-reading),
the safe-default obligation must be carried into the new
formulation.  Specifically:

* If the rebuild uses encoding constructors that include auxiliary
  computations (e.g., mp_codeF2 inside encMp's Fst slot), those
  auxiliaries must be safe-default versions.
* If thmT is implemented to invoke mp / sb / ax / ind directly
  (Definition-12-style), those also must be safe-default.

Otherwise Con is refutable and Goedel II is vacuous.
