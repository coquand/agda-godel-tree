# Guard-style Godel II for Binary Trees: Status

## What exists

### GuardComplete.agda (1189 lines, 0 postulates, 0 holes)

```
godel2G : ProofG ConGfull -> EmptyTA
```

Godel II via Loeb for ProofG. Uses representability constructors
(axRepMPG, axRepD3G, axGodelLeftG, axGodelRightG) for D2, D3, and
the diagonal. These package Guard's Exercise 24 / Theorem 12 as
axioms rather than deriving them.

### GuardFull.agda (1029 lines, 0 postulates, 0 holes)

```
godel2G2 : ProofG2 ConG2full -> EmptyTA
```

Same theorem, but with the correct architecture for Guard-style
derivation:

- **exIntroTmG2**: existential introduction with CodeTm witnesses
  (not just ground Code). This matches Guard's system where terms
  can contain variables in existential introduction.

- **substF3deep**: formula substitution that goes under binders
  with proper de Bruijn shifting. Used by exIntroTmG2.

- **Congruence layer**: axCongCaseG2, axCongFoldG2, axCongIfG2
  (Guard's axioms 5-7 for all primitive CodeTm operations).

- **Self-contained checker**: checkCG2 with 22-tag dispatch,
  foldCorrectG2 for all constructors, extCorrectG2.

- **D1 derived**: d1G2 via foldCorrectG2 + axExEval.

D2 and D3 still use axRepMPG2 / axRepD3G2. The derivation path
for eliminating these is fully unblocked.

## What remains

### Eliminate axRepMPG2 (derive D2 from computation axioms)

The derivation is ~40 lines of equational reasoning:

1. axFoldNode on the mp witness term
   `ctNode (ctAtom tagMP3) (ctNode (ctVar 1) (ctVar 0))`
   Unfolds the fold, exposing fold sub-results.

2. axCaseNodeL on the outer ctCase
   (fold results form a ctNode -> node branch -> inner ctCase)

3. Inner ctCase on `ctNode (ctAtom tagMP3) (payload)`
   -> node branch -> ncG2 body

4. ncG2 atom branch: tag dispatch for tagMP3
   3x axClosedEq (tag comparisons: tagMP3 != tagRefl3, tagGen3)
   + axIfFalse + axIfFalse + axIfTrue
   -> reaches hMP handler

5. hMP dispatches on fold(payload)
   fold(payload) = cnode(checker(c1), checker(c2))
   By axFoldNode on ctNode (ctVar 1) (ctVar 0)
   + congNodeBothG2 + hypotheses h1, h2
   -> cnode(enc(A->B), enc(A))

6. hMP-body: ctCase on enc(A->B) = cnode(catom ft1)(cnode encA encB)
   axClosedEq for the matchMP computation on specific enc(A->B), enc(A)
   -> enc(B)

7. Chain all steps with transG2 -> final equation

8. exIntroTmG2 with mp witness -> ProvG2(B)

9. Wrap with genG2 + exElimImpG2 for the two universals

Each step is 2-3 lines of ProofG2 derivation using one computation
axiom + one congruence application. The pattern is established;
the work is mechanical.

### Eliminate axRepD3G2 (derive D3)

Similar structure. The witness for D3 is the encoding of the
axExEval proof applied to the hypothesis witness. The derivation
traces the checker on this encoding. Same tools (axFoldNode +
congruence + axClosedEq).

### Eliminate axGodelLeftG2 / axGodelRightG2 (derive diagonal)

Requires showing that the Godel sentence G and not-Prov(G) are
"equivalent enough" for the Loeb argument. In the current setup,
G = not(exists c. 0=0) and not-Prov(G) = not(exists c. chk(c)=enc(G)).
These are not definitionally equal but are both uninhabited at
fuel 0. The diagonal constructors encode this.

To derive them from computation, we would need an internal
substitution function (the analogue of Guard's sub from Exercise 24
item [8]) and a proof that it correctly computes the diagonal.
This requires the full representability of formula substitution.

## Architecture

```
ChwistekSyntax          Nat, Code, Eq
    |
TreeArithTrack1         CodeTm, FormTA3, evalCT, foldCT, GoodTA3
    |
TreeArithInternal       ProofTA3 (17 constructors), substCT, substF3
    |
TreeArithBootstrap      checkCT3-full, foldCorrect3, sound0, d1-3-axExEval
    |
TreeArithGodel2         loeb-godel2, DerivabilityConditions
    |
GuardFull.agda          ProofG2, checkCG2, foldCorrectG2, d1G2, godel2G2
```

## Key design decisions

1. **Fuel-0 model**: soundness proved at fuel 0 (evalCT returns
   catom 0 for everything). This makes all feqTA3 trivially refl
   and avoids the substitution lemma for full soundness.

2. **exIntroTmG2 with substF3deep**: the architectural fix that
   enables Guard-style representability derivation. substF3deep
   goes under binders with proper de Bruijn shifting.

3. **Congruence as axioms**: axCongCaseG2, axCongFoldG2, axCongIfG2
   are sound at fuel 0 (refl). They correspond to Guard's axioms 5-7.

4. **Representability constructors**: axRepMPG2 and axRepD3G2 are
   the remaining non-Guard axioms. They are sound and correspond to
   derivable representability theorems. Eliminating them requires
   the equational trace described above.

## Files

| File | Lines | What it proves |
|------|-------|---------------|
| GuardComplete.agda | 1189 | godel2G (with representability axioms) |
| GuardFull.agda | 1029 | godel2G2 (with exIntroTmG2, congruence; D2/D3 still axiomatic) |
| GuardThm12.agda | 148 | Theorem 12 meta-level (thm12-meta) |
