# Godel II Plan: Three Questions Before Code

## The Distinction

**Project A (wrapper):** Add formula layer on top, postulate D1/D2/D3,
derive Godel II in the meta-system. Useful but not deep — just shows
the development CAN support a standard presentation.

**Project B (genuine):** Show D1/D2/D3 arise from the actual equational
machinery. Much harder. This is the real Rose/Guard implementation.

We already have Project A done (GuardBinaryGodel2.agda, over a
different base system). The interesting question is Project B
in the Rose equational setting.

## Question 1: What is the internal provability predicate?

In the equational setting, "A is provable" means "exists y such that
thS(y) = A". To express this INTERNALLY, we need:

Option 1a: Prov(A) = exists y. thS(y) = A
This requires existential quantification, which we don't have.

Option 1b: Prov(A) as a Term 1 (parameterized by code of A).
Define: provTerm A = matchSub A thTerm : Term 1.
eval_env[y] (provTerm A) = eqTree(thS(y), A).
This returns lf when thS(y) = A, falseT otherwise.
"A is provable" = exists y such that eval_env[y](provTerm A) = lf.

The existential is still meta-level. In the object language, we
can only check provability for SPECIFIC y, not quantify over all y.

Option 1c: Use the diagonal to get a self-referential closed term.
godelSentence target: a closed term whose eval checks thS at one
specific self-referential input. This gives a SINGLE EQUATION, not
a universal/existential statement.

ANSWER: In the purely equational setting, there is no internal
provability predicate that quantifies over all proof trees. The
best we can do is check provability at specific inputs (matchSub)
or at self-referential inputs (godelSentence). This is a fundamental
limitation: the equational system has no quantifiers.

## Question 2: In what form do D1/D2/D3 hold?

### D1 (Sigma-1 completeness): If thS proves A, then thS proves "thS proves A".

In our setting: if ValidProof y and thS(y) = A, then
ValidProof (dThS y) and thS(dThS y) = nd (codeReify A) (codeReify A).

This IS a metatheorem of our system (dThS-valid, dThS-thS).
It is NOT an internal theorem (thS cannot state "if I prove A then...").

STATUS: Metatheorem. Proved.

### D2 (Provability distributes over implication):
Prov(A→B) and Prov(A) implies Prov(B).

In the equational setting, there is no A→B. The closest analogue:
if thS proves L=M and thS proves M=R, then thS proves L=R
(transitivity). This IS internal (vpTrans).

But D2 in the Loeb argument operates on FORMULAS with implication,
not just equations. The equational transitivity is a weaker version.

STATUS: Transitivity is internal. Full D2 (for formulas) requires
a formula layer.

### D3 (Provability of provability):
Prov(A) implies Prov(Prov(A)).

In our setting: if ValidProof y, then ValidProof (dThS y).
And thS(dThS y) proves "thS(y) = thS(y)" (reflexivity of the theorem).

But D3 needs: from a proof of "A is provable", construct a proof
of "A is provable is provable". This requires the provability
predicate to be expressible internally, which (by Question 1)
it isn't in the purely equational setting.

STATUS: The meta-level version exists (dThS-valid). Internal D3
requires a provability predicate, which requires quantifiers.

## Question 3: Does the Loeb fixed point live in the object language?

The Loeb argument needs: a sentence G such that G ↔ (Prov(G) → ⊥).

Our godelSentence gives: eval(G) = eqTree(thS(c), target).
This checks whether thS at a specific input matches the target.
It does NOT say "there EXISTS a proof of G" — it checks ONE input.

For the genuine Loeb fixed point, G needs to say "I am unprovable"
= "for all y, thS(y) ≠ code(G)". This is a universal statement,
not expressible as a single equation.

ANSWER: The Loeb fixed point requires universal quantification over
proof trees, which is not available in the purely equational setting.
Our godelSentence is a WEAKER self-referential construction that
checks provability at one specific input, not all inputs.

## Conclusion

The genuine Rose/Guard Godel II (Project B) requires:
1. An internal provability predicate (needs existential quantification)
2. D2 for formulas with implication (needs implication)
3. D3 with internal provability (needs quantifiers)
4. The Loeb fixed point (needs universal quantification)

None of these are available in the purely equational Rose setting.

Therefore: Project B requires extending the equational system with
at least bounded quantifiers and implication. This is a significant
extension, not a "thin wrapper."

Project A (the wrapper) is feasible: add a formula layer as an
Agda datatype (like GuardBinaryGodel2), validate D1/D2/D3 from
existing machinery, run Loeb. This is ~150-200 lines. But it's
the META-system proving Godel II, not the OBJECT system.

## Recommendation

Do Project A first: it's concrete, connects to the tradition, and
uses the existing machinery. But be EXPLICIT that D1/D2/D3 are
metatheorems, not internal theorems. The formula layer is an Agda
datatype, not part of the equational proof system.

Then: the interesting question becomes whether the formula layer
can be ENCODED equationally (Nelson's chi-translation). If so,
Project B becomes possible. If not, we have a precise characterization
of what the equational system cannot express.

## Key Insight

The Rose equational system is a FRAGMENT of what Godel II needs.
It provides the computational machinery (thS, D_thS, transitivity)
but lacks the logical machinery (quantifiers, implication).

Guard's system has both because it includes Hilbert combinators
(K, S) and formula types (fimpTA3, fallTA3, fexTA3). Our Rose
system deliberately avoids these for simplicity.

The Godel II question thus reduces to: can the logical machinery
be recovered from the equational machinery? This is essentially
Nelson's chi-translation question.
