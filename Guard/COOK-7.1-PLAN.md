# Cook's Theorem 7.1 for Guard — Implementation Plan

## Goal

Prove in Agda (Guard system) that Guard, viewed as a proof system for
boolean tautologies, is not p-verifiable.  This is the equational analog
of Cook (1975) Theorem 7.1.

## What exists already

- Guard/CookPV.agda: boolean operations (andF, orF, notF, implF, sg, tr),
  De Morgan laws, excluded middle, double negation = sign, all via Schema F.
  Key result: `andF(t, notF(t)) = falseT` for all t (non-contradiction),
  provable by `deMorgan` + `excludedMiddle` or directly via Schema F
  on `Comp2 andF I notF` vs `KT falseT`.
  NOTE: non-contradiction is NOT yet stated as a standalone lemma.
  First task: add it to CookPV.agda.

- Guard/NoPChecker.agda: trivial corollaries of godelII in proof-checker
  language.  These are placeholders — the genuine content goes here.

- Guard/GodelIIFull.agda: godelII, conToBot, conSentence, codeBotT.
  conSentence = eqn (ap2 TreeEq (ap1 thFunTFor (var zero)) codeBotT) falseT.
  godelII : Consistent hyp -> Deriv hyp conSentence -> Empty.
  conToBot : Deriv hyp conSentence -> Deriv hyp (eqn trueT falseT).

- Guard/Thm14E.agda: thm14E — given a derivation, produce a proof encoding
  + correctness witness (thFunTFor(enc) = codeEqn(eq)).

- Guard/Step.agda: Deriv, ruleF (Schema F), ruleHyp, ruleInst, etc.
  The system is purely equational: no implication connective.
  Conditional reasoning uses hypotheses: Deriv hyp eq.

## The argument (Cook's Lemma 7.2 adapted)

We want to show: for any functors PV_SYS : Fun1 and TR_CHK : Fun2, if
Guard proves the "p-verifiability equation"

    pVerHyp = eqn (ap2 TR_CHK (ap1 PV_SYS (var 0)) (var 1)) trueT

then Guard proves conSentence (and hence is inconsistent by godelII).

### Step-by-step proof sketch

The hypothesis pVerHyp says: for all x,y, TR_CHK(PV_SYS(x), y) = trueT.
This means PV_SYS maps every tree to a "tautology" that TR_CHK accepts.

1. NON-TAUTOLOGY WITNESS.  Define the term:

       phi0 = <encoding of P & ~P as a specific tree>

   and a truth assignment tau0 (e.g., O = "P is true").
   Prove in Guard (from no hypothesis):

       Deriv hyp (eqn (ap2 TR_CHK phi0 tau0) falseT)

   This requires TR_CHK to correctly evaluate phi0.  If TR_CHK is an
   ARBITRARY functor, we cannot prove this!

   KEY INSIGHT: We do NOT need TR_CHK to be arbitrary.  We need it to
   satisfy TWO properties simultaneously:
   (a) TR_CHK(PV_SYS(x), y) = trueT  for all x, y  (p-verifiability)
   (b) TR_CHK(phi0, tau0) = falseT   (phi0 is not a tautology)

   If both (a) and (b) hold, then instantiating (a) at any x with
   PV_SYS(x) = phi0 gives TR_CHK(phi0, tau0) = trueT, contradicting (b).

   So the theorem is: there is no (PV_SYS, TR_CHK, phi0, tau0) such that
   Guard proves BOTH (a) and (b).

2. CONNECTION TO conSentence.  From (a) + (b):
   - If PV_SYS(enc) = phi0 for some enc, then TR_CHK(phi0, tau0) = trueT
     (by (a)), but also = falseT (by (b)), giving trueT = falseT.
   - So Guard proves: PV_SYS(x) = phi0 -> trueT = falseT.
   - In equational form: TreeEq(PV_SYS(x), phi0) behaves like conSentence.

3. THEOREM STATEMENT (simplest clean version):

```agda
cook71 : {hyp : Equation} ->
  (PV_SYS : Fun1) -> (TR_CHK : Fun2) ->
  (phi0 : Term) -> (tau0 : Term) ->
  -- (a) p-verifiability: TR_CHK accepts all PV_SYS outputs
  Deriv hyp (eqn (ap2 TR_CHK (ap1 PV_SYS (var zero)) (var (suc zero))) trueT) ->
  -- (b) non-tautology witness: TR_CHK rejects phi0 at tau0
  Deriv hyp (eqn (ap2 TR_CHK phi0 tau0) falseT) ->
  -- (c) PV_SYS hits phi0: there exists x0 with PV_SYS(x0) = phi0
  (x0 : Term) ->
  Deriv hyp (eqn (ap1 PV_SYS x0) phi0) ->
  -- Conclusion: trueT = falseT (inconsistency)
  Deriv hyp (eqn trueT falseT)
```

   Proof: instantiate (a) at x=x0, y=tau0.  Then:
   - TR_CHK(PV_SYS(x0), tau0) = trueT     [from (a)]
   - PV_SYS(x0) = phi0                      [from (c)]
   - TR_CHK(phi0, tau0) = trueT             [by cong]
   - TR_CHK(phi0, tau0) = falseT            [from (b)]
   - trueT = falseT                          [by trans]

   This is ~10 lines of Agda.

4. APPLYING TO GUARD.  To get the full result, we need to show that
   IF Guard is inconsistent, THEN condition (c) is satisfiable — i.e.,
   PV_SYS hits phi0 for some x0.

   Cook's argument: if Guard proves 0=1, then Guard proves everything,
   in particular it proves "phi0 is a tautology" (i.e., TR_CHK(phi0, tau) = trueT
   for all tau).  By Thm14, this proof has encoding enc.  PV_SYS(enc) should
   then be phi0 (by definition of PV_SYS as the map from proofs to formulas).

   For this last step, PV_SYS must be defined concretely as a Guard functor
   that maps proof encodings to propositional formulas.  The simplest version:

       PV_SYS = KT phi0   (constant function — maps everything to phi0)

   This is degenerate but makes (a) say "TR_CHK(phi0, y) = trueT for all y",
   which directly contradicts (b).  No Thm14 needed.

   For a NON-degenerate version, PV_SYS should use thFunTFor to extract the
   equation code and then map it to a propositional formula.  This is the
   prop_m correspondence from Cook Section 6.

## Implementation plan

### Session 1: The abstract theorem + non-contradiction

1. Add `nonContradiction` to CookPV.agda:
   nonContra = Comp2 andF I notF
   Prove: nonContra(t) = falseT for all t, via Schema F.
   (Base: andF(O, notF(O)) = andF(O, falseT) = falseT.
    Step: andF(PairAB, notF(PairAB)) = andF(PairAB, O) = falseT.)

2. Prove cook71 in NoPChecker.agda (the abstract version from step 3 above).
   This is ~10 lines: just ruleInst + congL + ruleTrans.

3. Prove the degenerate corollary: for any TR_CHK, phi0, tau0, if
   TR_CHK(phi0, y) = trueT for all y AND TR_CHK(phi0, tau0) = falseT,
   then trueT = falseT.  (Even simpler — just ruleInst + ruleTrans.)

### Session 2: The concrete PV_SYS (optional, for full Cook 7.1)

This is the harder session.  Define PV_SYS concretely as a Guard functor:

    PV_SYS(enc) = propFormula(thFunTFor(enc))

where propFormula maps equation codes to propositional formulas.

For the MINIMAL version (equation 0=1 only):
- propFormula(codeBotT) = phi0 (the encoding of P & ~P)
- propFormula(anything else) = phiTrue (some tautology, e.g., P | ~P)

This can be implemented as:
    propFormula = Comp2 IfLf (Comp2 TreeEq I (KT codeBotT)) (KT (Pair phi0 phiTrue))
    (if TreeEq(input, codeBotT) = O then phi0 else phiTrue)

Wait, IfLf dispatches on leaf/node, not on O/non-O equality result.
TreeEq returns O for equal, PairOO for unequal.  So:
    IfLf(TreeEq(x, codeBotT), Pair(phi0, phiTrue))
    = phi0 when TreeEq = O (equal)
    = phiTrue when TreeEq = PairOO (unequal)

So: propFormula = Comp2 IfLf (Comp2 TreeEq I (KT codeBotT)) (KT (Pair phi0 phiTrue))

Then PV_SYS = Comp propFormula thFunTFor.

The proof obligations:
- When thFunTFor(enc) = codeBotT: PV_SYS(enc) = phi0
- When thFunTFor(enc) ≠ codeBotT: PV_SYS(enc) = phiTrue
- TR_CHK(phi0, tau0) = falseT (non-tautology)
- TR_CHK(phiTrue, tau) = trueT for all tau (tautology)

And then cook71 gives: from p-verifiability, either PV_SYS never hits phi0
(meaning thFunTFor(x) ≠ codeBotT for all x, which IS conSentence), or
PV_SYS hits phi0 and we get trueT = falseT.

## Potential problems

1. EVAL OVER FORMULAS: For a general formula evaluator as a Rec functor,
   Guard's Rec recurses into BOTH children of a node.  Tags that are
   themselves nodes get recursively processed.  SOLUTION: for Cook 7.1,
   we DON'T need a general evaluator.  We only need: andF(t, notF(t)) = falseT
   (already proved) and orF(t, notF(t)) = trueT (already proved).

2. PV_SYS DEFINITION: The map from equation codes to propositional formulas
   (prop_m) is intricate in the general case.  SOLUTION: for minimal Cook 7.1,
   use the binary dispatch above (TreeEq + IfLf), mapping codeBotT to phi0
   and everything else to phiTrue.

3. EQUATIONAL REASONING WITHOUT IMPLICATION: Cook uses PV1 which has ⊃.
   Guard is purely equational.  SOLUTION: use hypotheses (Deriv hyp eq)
   and ruleHyp.  The p-verifiability is the hypothesis.

4. CONNECTING TO conSentence: Need to show that the abstract cook71 theorem
   implies conSentence when PV_SYS is defined via thFunTFor.  This requires
   showing: if PV_SYS(x) ≠ phi0 for all x, then thFunTFor(x) ≠ codeBotT
   for all x.  The contrapositive is: if thFunTFor(x) = codeBotT then
   PV_SYS(x) = phi0, which follows from the definition of propFormula.
