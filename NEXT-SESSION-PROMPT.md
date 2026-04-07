# Next Session: Rose Theorems 15-16-18 (Gödel II)

## Setup
Use `~/.cabal/bin/agda-2.9.0`. The Guard/ directory has the complete formalization.

## What was completed

### Rose Theorem 14: all 26 Nelson cases
Every thFunTFor dispatch case has an object-level Deriv proof.
Files: NelsonAxI, NelsonAxFst, NelsonAxSnd, NelsonAxConst, NelsonAxComp,
NelsonAxComp2, NelsonAxLift, NelsonAxPost, NelsonAxFan, NelsonAxRecLf,
NelsonAxRecNd, NelsonAxIfLfL, NelsonAxIfLfN, NelsonAxTreeEqLL,
NelsonAxTreeEqLN, NelsonAxTreeEqNL, NelsonAxTreeEqNN, NelsonAxRefl,
NelsonRuleSym, NelsonRuleTrans, NelsonCong1, NelsonCongL, NelsonCongR,
NelsonRuleInst, NelsonRuleF, NelsonAxKT.

Each proves: thFunTFor applied to the encoding of rule k produces
the correct equation code. Pattern: phase1Nd + ndDispatchToCase_k +
extractor reductions + combinator reductions.

### Rose Theorem 17: already done
diagFTarget in SubstTForPrecomp.agda: cstf(N̂) = code(G).

### GodelII.agda: Gödel I (168 lines)
ProofE(H) → Consistent(H) → H ⊢ G → ⊥

## What to do next

### Theorem 15 (Rose p.134)
"If A = B then th(y) ≠ [A = 0] ⊢ th(y) ≠ [B = 0]."
Immediate consequence of Theorem 14. In our system: if there's a
Deriv of A = B, then the system proves that thFunTFor tracking of B
implies tracking of A.

This requires combining the 26 individual Nelson cases into a single
result that works for any derivation. The proof goes by induction on
Deriv: for each constructor of Deriv, invoke the corresponding
Nelson case file.

### Theorem 16 (Rose p.134)
"th(y) ≠ [f(0) = 0] & th(y) ≠ [f(sx) = 0] ⊢ f(x) ≠ 0"
Internalized Schema F. Uses Theorem 15 + the ruleF case (NelsonRuleF).
Show that if the system tracks both the base and step cases of a
Schema F proof, then f(x) = 0 follows.

### Theorem 18 (Rose p.135)
Assembly into Gödel II. Uses 15, 16, 17:
- By 17 (diagonal): code(G) = se(nu(N), N)
- By 16 (internalized Schema F): if system proves base + step of
  "validity implies truth", then vl(x, th(y)) = 0
- By 15 + consistency assumption: derive G from Con
- Combined with Gödel I: contradiction

The key type to prove:
```
godelII_full : {hyp : Equation} ->
  Consistent hyp ->
  Deriv hyp conSentence ->
  Empty
```
where conSentence is the internal consistency statement.

## Key infrastructure
- NelsonDispatch.agda: phase1Nd, ndDispatchToCase0-25
- NelsonExtractors.agda: origARed, origBRed, mkAp1FRed, mkAp2FRed, mkEqFRed
- ExtractorRed.agda: deeper extractors (origB2aRed, origB2bRed, etc.)
- ThFunTForDefs.agda: origA, origB, mkEqF, mkAp1F, mkAp2F, kF2
- GodelII.agda: treeEqSelf, the Gödel I proof
- SubstTForPrecomp.agda: diagFTarget, cstf, templateCode, cGS

## Papers
- Guard/guard-godelII-summary.tex: describes the system and Gödel I proof
- Guard/nelson-boundary.tex: R/Q technique and feasibility analysis
