# Track 1 Next Session: Complete the ProofTA3 Bootstrap for Gödel II

## What exists (all compiles, 0 postulates, 0 holes)

### TreeArithTrack1.agda (2215 lines)
- CodeTm (8 constructors), FormTA3 (5 constructors), evalCT/foldCT
- checkCT-full: internal checker for ProofTA (all 6 tags: n90-n95)
- foldCorrect: all 6 ProofTA constructors proved
- checkTA-complete: checkTA acceptance → ProofTA derivation
- d3-checker-based: ProvableTA A → internal checker witnesses A
- extCorrect-proof, d3-proof-based: ProofTA A → evalCT witness

### TreeArithInternal.agda (456 lines)
- ProofTA3: extended proof system (15 constructors)
  - Hilbert: axK3, axS3, mp3
  - Quantifiers: gen3, inst3, exIntro3
  - Equality: axRefl3, axSym3, axTrans3
  - Computation: axCaseAtom, axCaseNodeL, axFoldAtom, axIfTrue, axIfFalse, axEqNatRefl
- substCT, substF3: substitution functions
- GoodTA3 semantic model

### TreeArithGodel2.agda (251 lines)
- loeb-godel2: abstract Gödel II theorem (Löb's theorem), fully proved
- encCodeTm, encFormTA3: encoding functions defined
- Prov3, Con3: internal provability and consistency formulas
- godel2-TA3: CONDITIONAL Gödel II for ProofTA3

## What is NOT done

The conditional theorem godel2-TA3 takes these hypotheses:

```agda
d1-3 : {A : FormTA3} -> ProofTA3 A -> ProofTA3 (Prov3 A)
d2-3 : {A B : FormTA3} -> ProofTA3 (fimpTA3 (Prov3 (fimpTA3 A B)) (fimpTA3 (Prov3 A) (Prov3 B)))
d3-3 : {A : FormTA3} -> ProofTA3 (fimpTA3 (Prov3 A) (Prov3 (Prov3 A)))
G    : FormTA3   (Gödel sentence)
gL   : ProofTA3 (fimpTA3 G (fimpTA3 (Prov3 G) fbotTA3))
gR   : ProofTA3 (fimpTA3 (fimpTA3 (Prov3 G) fbotTA3) G)
con3 : ProofTA3 fbotTA3 -> EmptyTA
```

To make it unconditional, ALL of these must be proved.

### Critical issue: Prov3 currently uses checkCT-full (the BASE checker)

Prov3 is defined as:
```
Prov3 A = fexTA3 (feqTA3 checkCT-full (liftCode (encFormTA3 A)))
```

This is WRONG for ProofTA3. checkCT-full only handles ProofTA proof codes
(tags n90-n95). ProofTA3 has ~15 constructors with new tags. Prov3 must
use an EXTENDED checker checkCT3-full that handles all ProofTA3 proof codes.

## The prompt for the next session

```text
You are working in /Users/coquand/CHWISTEK/. Read these files first:
- TreeArithTrack1.agda
- TreeArithInternal.agda
- TreeArithGodel2.agda
- This file (TRACK1-NEXT-SESSION.md)

Goal: Complete the ProofTA3 bootstrap and make godel2-TA3 unconditional.
This is a BUILD task. Do not summarize. Do not speculate.

Task A — Extended checker
1. Choose new tag numbers (n200-n214 or similar) for ProofTA3 constructors.
2. Define encProofTA3 : {A : FormTA3} -> ProofTA3 A -> Code
   encoding each ProofTA3 derivation as a Code with the new tags.
3. Define checkCT3-full : CodeTm extending checkCT-full's ctFold nodeCase
   with handlers for all 15 ProofTA3 tags.
4. Update Prov3 to use checkCT3-full instead of checkCT-full.

Task B — Correctness
5. Prove foldCorrect3 : for each ProofTA3 constructor,
   foldCT at proofFuel3 on encProofTA3 prf gives encFormTA3 A.
   Follow the same strong-fuel pattern (addN (proofFuel3 prf) k).
6. Prove d1-3 : ProofTA3 A -> ProofTA3 (Prov3 A)
   using foldCorrect3 + exIntro3.

Task C — Internal derivability conditions
7. Prove d2-3 : ProofTA3 proves Prov(A->B) -> Prov(A) -> Prov(B).
   Build the internal mp witness using the checker's mp tag.
8. Prove d3-3 : ProofTA3 proves Prov(A) -> Prov(Prov(A)).
   Build the internal D1 witness using the encoding of the D1 derivation.

Task D — Diagonal lemma
9. Define a substitution CodeTm (sub-ct) that performs formula substitution
   internally: sub-ct applied to enc(A) and c gives enc(A[c/v0]).
10. Prove correctness of sub-ct using computation axioms.
11. Construct the Gödel sentence G using the diagonal/fixed-point method.
12. Prove goedelLeft and goedelRight.

Task E — Consistency
13. Prove con3 : ProofTA3 fbotTA3 -> EmptyTA
    by showing all ProofTA3 axioms are sound under GoodTA3.

Task F — Assembly
14. Instantiate godel2-TA3 with d1-3, d2-3, d3-3, G, gL, gR, con3.
15. The result: ProofTA3 Con3 -> EmptyTA (ProofTA3 cannot prove its own consistency).

Mandatory classification at the end:
Case A: Gödel II proved unconditionally for ProofTA3
Case B: Gödel II needs one more lemma (state it in Agda type form)
Case C: Gödel II blocked by a conceptual issue (describe precisely)

Constraints:
- No postulates, no holes
- {-# OPTIONS --without-K --exact-split #-}
- Use private blocks for type-checker performance
- No with clauses
- Follow patterns from TreeArithTrack1.agda (proofFuel, foldCorrect, etc.)
- The encoding functions (encCodeTm, encFormTA3) are already defined in TreeArithGodel2.agda.
  Do NOT try to normalize encCodeTm checkCT3-full.
  Use abstract encoding properties, not concrete term reduction.

Estimated size: ~1000 lines in a new file TreeArithBootstrap.agda.

Key lessons from the previous session:
- evalCT returns Code (not Maybe Code). Fuel exhaustion = catom zero.
- Fuel monotonicity is NOT provable for Code-returning evalCT.
  Use the strong-fuel pattern: addN (proofFuel prf) k.
- n30 (the base fuel constant) must be large enough for the dispatch chain.
  The current n30 = 120 (via addN of n20b pieces). May need more for 15+ tags.
- For the mp case of foldCorrect, case-split on FormTA to reduce eqCodeDeep.
- For abstract B in the result, the computation reduces by refl.
- encProofTA always produces cnodes. Use encProofTA-is-cnode for the
  inner fold default branch.
- The inst case needs substFormTA-id transport (substFormTA is identity).

The main deliverable is the FORMAL STATUS of Gödel II after the bootstrap.
```

## File dependencies

```
ChwistekSyntax.agda
ChwistekProvability.agda
ChwistekCodeLogic.agda
ChwistekSoundness.agda
    |
    v
TreeArith.agda (FormTA, ProofTA, checkTA, soundness, consistency)
    |
    v
TreeArithB.agda (checkTA-mono, D1, D2, checkTA-sound, ConInt ↔ ConExt)
    |
    v
TreeArithTrack1.agda (CodeTm, FormTA3, checkCT-full, D3, completeness)
    |
    v
TreeArithInternal.agda (ProofTA3, computation axioms)
    |
    v
TreeArithGodel2.agda (abstract Gödel II, Prov3, Con3, conditional theorem)
    |
    v
TreeArithBootstrap.agda (NEW: extended checker, D1-3, diagonal, unconditional Gödel II)
```

## Expected outcomes

Case A (Gödel II proved) is the most likely outcome. The patterns are all
established. The main risk is Agda type-checker performance on the large
checkCT3-full term.

Case B (needs one more lemma) would indicate a specific technical gap in
the representability machinery, likely around the diagonal lemma or the
internal D3 construction.

Case C (conceptual blocker) would be surprising at this point, as all
conceptual issues have been resolved in the current session.
