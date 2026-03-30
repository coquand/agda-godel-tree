# The Nelson Result: Precise Statement

## What Is Formally Verified

Three theorems in Rose/Godel.agda (0 postulates, --safe):

### Theorem 1: CoreInv proves incompleteness
coreTree is a non-congruent code-level invariant preserved by all
thS operations. It excludes specific true equations from the range,
giving Godel I (niterLeaf-unprovable-all) and Rose-style Godel II
(godelEq-lf-unprovable).

### Theorem 2: Congruence destroys CoreInv
The maximal CoreInv-safe congruence fragment is trivial. Even pair
congruence is unsafe. The classification covers all constructor
positions. (nelsonObstruction, pairCongUnsafe, casBaseUnsafe,
casStepSafe, recStepSafe)

### Theorem 3: Endpoint semantics cannot see incompleteness
A provable equation (casLeaf axiom) and an unprovable equation
(niterLeaf) have identical evaluated endpoints (lf, lf).
(endpointSame = refl)

## The No-Go Theorem (for the coreTree strategy)

For this binary-tree proof system: the provable/unprovable gap is
visible only to non-congruent code-level invariants. But those
invariants are exactly the ones destroyed by the congruence
principles needed for useful internal reflection. Therefore the
coreTree route to self-reflection is blocked in principle.

More precisely: the coreTree invariant cannot be internalized by
adding any useful congruence to thS, because any such congruence
destroys the invariant that makes incompleteness visible.

## What Is NOT Proved

The stronger universal claim "no internal reflection on incompleteness
is possible at all" is NOT established. That would require excluding
every possible alternative invariant, not just coreTree-style or
endpoint-semantic ones.

## Connection to Nelson

Nelson's syntactic viewpoint is vindicated: purely syntactic invariants
(coreTree) really do reveal incompleteness, without any semantic
assumptions.

But the experiments strongly suggest a no-go phenomenon: the syntactic
distinctions that witness incompleteness live BELOW congruence, while
self-reflection needs congruence-like closure.

The structural incompatibility is between three things:
1. Range-excluding invariants (need code-level, non-congruent)
2. Congruence closure (needed for internal equational reasoning)
3. Internal reflection (needs both 1 and 2, but they conflict)

This is a strong model-level objection to Nelson's hoped-for mechanism
in this specific setting, rather than a final impossibility theorem for
every conceivable approach.

## What This Suggests

The gap between "syntax detects incompleteness" and "the system
internalizes that detection" is not accidental. It reflects a
structural incompatibility that may be fundamental: the very
features that make a system able to reason about its own proofs
(congruence, substitution under binders) are the features that
destroy the syntactic invariants that distinguish provable from
unprovable true equations.

Whether this incompatibility persists for ALL possible invariants
(not just coreTree) remains open.
