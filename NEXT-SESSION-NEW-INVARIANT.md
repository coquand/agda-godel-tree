# Next Session: Beyond CoreInv — Finding a Congruence-Stable Invariant

## What Was Proved (2026-03-30)

### The Classification Theorem
CoreInv is a non-congruence invariant of raw code. The maximal safe
congruence fragment is trivial (only discarded positions). The
obstruction is global: even pair is unsafe, because codeTerm
distinguishes semantically equal terms.

### Precise Statement
Any congruence principle strong enough to substitute semantically
equal terms into a context whose code survives coreTree destroys
CoreInv. This is because codeTerm is not congruence-stable under
semantic equality: different terms can eval to the same tree but
have completely different code structure (tag, payload shape).

### Consequence
CoreInv cannot be internalized in any useful way. The classification
closes the "safe congruence" direction. The research program shifts
from "find safe congruence" to "find a new invariant."

## The New Question

> Is there an invariant that:
> (a) is congruence-stable (survives substitution of eval-equal terms)
> (b) is strong enough to exclude at least some false equations
> (c) can be proved for all thS outputs

If such an invariant exists: it would enable internalization and
create the genuine Nelson tension.

If no such invariant exists: that would be a deeper impossibility
result — the system fundamentally cannot reflect on its own consistency
in ANY syntactic way.

## Why CoreInv Fails (Root Cause)

CoreInv operates on RAW CODE (codeTerm output). Two terms with the
same eval can have completely different codes:

    cas leaf leaf (pair leaf leaf)  →  eval = lf, code tag = tagCase
    leaf                           →  eval = lf, code tag = tagLeaf

Any invariant based on raw code structure is doomed to be non-congruent,
because congruence operates at the semantic (eval) level.

## The Design Space for New Invariants

### Level 1: Raw code (current)
codeTerm : Term n → Tree. Distinguishes everything. Non-congruent.
coreTree operates here. CoreInv lives here.

### Level 2: Normalized code
Define normCode : Term 0 → Tree that first evaluates, then reifies:
normCode t = codeTerm (reify (eval t)).

This IS congruence-stable: if eval a = eval b, then
normCode a = codeTerm (reify (eval a)) = codeTerm (reify (eval b)) = normCode b.

But: normCode erases ALL computational structure. Every closed term
that evals to lf gets the same normCode. So any invariant based on
normCode is essentially an invariant of EVAL VALUES, not code structure.

Can an eval-value invariant exclude false equations? A false equation
has eval l ≠ eval r. So "eval l = eval r" is itself an invariant
that excludes false equations. And it IS congruence-stable. But it's
just SOUNDNESS — we already have that (ThSResult).

### Level 3: Partially normalized code
Normalize SOME structure but not all. E.g.:
- Normalize cas-leaf/rec-leaf redexes (like coreTree does)
- But also normalize across eval-equivalent terms

This is the sweet spot: enough normalization for congruence stability,
but not so much that all structure is lost.

### Level 4: Semantic invariant with syntactic witness
Instead of comparing codes, compare some semantic property that still
has a syntactic signature. E.g.:
- "The head constructor of eval(l) matches the head constructor of eval(r)"
- This is congruence-stable AND excludes some false equations

## Concrete Candidates to Test

### Candidate A: eval-head invariant
Define: headMatch(c) = "if c = nd L R, then the head constructors
of eval(decodeTerm L) and eval(decodeTerm R) agree."

This is congruence-stable (eval is congruent) and excludes
equations like leaf = pair leaf leaf (head lf vs head nd).

But: does it hold for all thS outputs? By ThSResult, thS outputs
have eval l = eval r. So head(eval l) = head(eval r). YES. ✓

Is it strong enough? It excludes any equation where the two sides
evaluate to trees with different head constructors. That's exactly
the "false equation" criterion.

But it's IDENTICAL to soundness (ThSResult). Nothing new.

### Candidate B: eval-depth invariant
"The tree depths of eval(l) and eval(r) agree."

Same issue: follows from eval l = eval r. Just soundness.

### Candidate C: code-tag-after-eval invariant
"The tags of codeTerm(reify(eval l)) and codeTerm(reify(eval r)) agree."

Since eval l = eval r: codeTerm(reify(eval l)) = codeTerm(reify(eval r)).
Trivially holds. Again just soundness.

### Candidate D: something BETWEEN soundness and CoreInv
The challenge: any invariant that's strictly stronger than soundness
but weaker than CoreInv. Such an invariant would need to track some
code structure that is:
- congruence-stable (survives eval-equal substitution)
- not already captured by eval equality

Is there such a property? The key question is whether there is
ANYTHING about term codes that is both:
1. Invariant under eval-preserving substitution
2. Stronger than just eval equality

In classical logic: no. Two terms with the same eval are
observationally equivalent. Any property preserved by eval-equal
substitution is determined by eval values.

In our system: also no, for the same reason. codeTerm and coreTree
are NOT eval-invariant. Any eval-invariant property reduces to
properties of eval values.

## The Fundamental Theorem (Conjecture)

> Any congruence-stable invariant of thS outputs that holds for
> all valid proofs is a consequence of soundness (eval l = eval r).
> No strictly stronger congruence-stable invariant exists.

If this conjecture is true: the Nelson obstruction is COMPLETE.
There is no way to get a congruence-stable invariant that does
more than soundness. And soundness is not strong enough for
range exclusion (it doesn't distinguish true-but-unprovable
equations from provable ones).

Therefore: the gap between "provable" and "true" is invisible
to any congruence-stable invariant. Only non-congruent invariants
(like CoreInv) can see it. And non-congruent invariants cannot
be internalized.

## What to Test in Agda

1. Formalize the conjecture: any eval-invariant property of
   equation codes that holds for all thS outputs follows from
   eval l = eval r. (This might be hard to state in full generality.)

2. Test specific candidates: define new invariants and check if
   they're both congruence-stable and strictly stronger than soundness.

3. The sharp test: find a TRUE equation (eval l = eval r) that is
   provable AND has the same normCode structure as our unprovable
   niterLeaf equation. If such a pair exists: no eval-invariant
   property can distinguish provable from unprovable true equations.

## Files
- Rose/Godel.agda: CoreInv, nelsonObstruction, classification
- NELSON-OBSTRUCTION.md: the obstruction result
- NEXT-SESSION-CONGRUENCE.md: analysis of congruence question
