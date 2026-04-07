# Next Session: Complete Gödel II (Rose Theorem 18)

## Setup
Use `~/.cabal/bin/agda-2.9.0`. The Guard/ directory has the complete formalization.

## What was completed this session

### Thm15.agda (compiles, 0 postulates)
- `mkProofEAny : (A B : Term) -> ProofE (eqn A B)` — constructs ProofE
  for ANY equation using trans-from-two-refls (tag 19 + two tag-17 sub-encodings).
  This eliminates the ProofE hyp assumption from Gödel I.
- `godelI : Consistent hyp -> Deriv hyp godelSentence -> Empty` —
  strengthened Gödel I without ProofE hyp requirement.
  Proof: `godelI {eqn l r} con dG = godelII (mkProofEAny l r) con dG`.

### GodelIIFull.agda (skeleton)
- `conSentence = eqn (ap2 TreeEq (ap1 thFunTFor (var zero)) codeBotT) poo`
  where `codeBot = codeEqn (eqn O poo)`, `codeBotT = reify codeBot`.
- `godelII_full` is TODO.

## Prior completed work

### Rose Theorem 14: all 26 Nelson cases
Every thFunTFor dispatch case has an object-level Deriv proof.
Files: NelsonAxI, NelsonAxFst, NelsonAxSnd, NelsonAxConst, NelsonAxComp,
NelsonAxComp2, NelsonAxLift, NelsonAxPost, NelsonAxFan, NelsonAxRecLf,
NelsonAxRecNd, NelsonAxIfLfL, NelsonAxIfLfN, NelsonAxTreeEqLL,
NelsonAxTreeEqLN, NelsonAxTreeEqNL, NelsonAxTreeEqNN, NelsonAxRefl,
NelsonRuleSym, NelsonRuleTrans, NelsonCong1, NelsonCongL, NelsonCongR,
NelsonRuleInst, NelsonRuleF, NelsonAxKT.

### Rose Theorem 17 (diagonal)
diagFTarget in SubstTForPrecomp.agda: cstf(N̂) = code(G).

### GodelII.agda: Gödel I (168 lines)
ProofE(H) → Consistent(H) → H ⊢ G → ⊥

## What to do: complete Gödel II

### The blocker: Con → G internalization

The full Gödel II needs:
```
godelII_full : {hyp : Equation} ->
  Consistent hyp -> Deriv hyp conSentence -> Empty
```

The natural proof strategy:
1. From `Deriv hyp conSentence`, derive `Deriv hyp godelSentence`
2. Apply `godelI` to get Empty

Step 1 is the hard part: deriving G from Con equationally.

**Why it's hard**: The equational system has no implication. We need
to express "if thFunTFor(y) = cGS, then ⊥ is derivable" as an equation.
The standard approach requires a term-level function F such that
thFunTFor(F(y)) = codeBot whenever thFunTFor(y) = cGS. But F encodes
the Gödel I derivation transformation, which depends on the derivation
STRUCTURE, not just the equation output.

### Possible approaches

1. **Direct Schema F**: Show TreeEq(thFunTFor(x), cGST) = poo for all x
   by tree induction on x. Base case works (thFunTFor(O) = O ≠ cGS).
   Step case: for each tag k, show case_k never produces cGS.
   **Problem**: for specific k and data, case_k CAN produce cGS (if the
   data encodes a valid proof of G). So Schema F alone fails.

2. **Conditional via IfLf**: Encode the conditional "if A then B" as
   IfLf(TreeEq(A, target), Pair(B, default)). The equational system
   can manipulate these expressions.
   **Status**: unexplored, might work for specific cases.

3. **Validity function à la Rose**: Define vl(x, y) that checks whether
   equation y is "valid" at variable assignment x. Then Schema F on
   vl to show all proofs yield valid equations.
   **Problem**: requires a universal evaluator, which may not terminate
   within the system's recursion bounds.

4. **Different conSentence**: Instead of "thFunTFor(x) ≠ codeBot",
   use a conSentence that's structurally closer to godelSentence,
   so the derivation is simpler.
   **Status**: unexplored.

5. **Follow Rose literally**: Get Rose's paper (1961) and follow his
   exact equational argument for Theorems 15-16-18. His approach
   is designed for exactly this kind of equational system.
   **Status**: should be the first thing to try.

### Key infrastructure
- Thm15.agda: mkProofEAny, godelI
- GodelIIFull.agda: conSentence, codeBot, codeBotT (skeleton)
- NelsonDispatch.agda: phase1Nd, ndDispatchToCase0-25
- NelsonExtractors.agda: origARed, origBRed, mkAp1FRed, mkAp2FRed, mkEqFRed
- ExtractorRed.agda: deeper extractors
- ThFunTForDefs.agda: origA, origB, mkEqF, mkAp1F, mkAp2F, kF2
- GodelII.agda: treeEqSelf, the original Gödel I proof
- SubstTForPrecomp.agda: diagFTarget, cstf, templateCode, cGS

### Papers
- Guard/guard-godelII-summary.tex: describes the system and Gödel I proof
- Guard/nelson-boundary.tex: R/Q technique and feasibility analysis
- Rose 1961: the original equational proof of Gödel II (not in repo)
