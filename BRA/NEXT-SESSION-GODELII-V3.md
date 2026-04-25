# Next session: parametric subEnc + thmT linkage for Goedel II step 4

**This document supplements `BRA/NEXT-SESSION-GODELII-V2.md`** with
the post-session-1 state and the discovered architecture for step 4.

V2 remains the canonical statement of the contract, the four PINNED
lessons, and the methodology.  Read V2 first.

## Status (post-session, 2026-04-25)

Two files done, two topical commits:

  * `BRA/Sb.agda` (234 LoC, 0.20s cold): `sb : Fun2` combinator on
    coded formulas; `sbDef` proves the closed-form reduction
    `ap2 sb (Pair (reify codeA) (reify (natCode n))) (reify codeP)
       = reify (codedSubst codeA (code (var n)) codeP)`.
    Built from existing `subT` + Fan / Lift / KT / Post / Pair.  No
    new primitives, no postulates.

  * `BRA/SbAxiom.agda` (91 LoC, 0.24s cold): `sbForOutRuleInst`
    composes sbDef + codeCommutesFormula to derive
    `ap2 sb (Pair (reify (code t)) (reify (natCode k))) (reify (codeFormula P))
       = reify (outRuleInst k t P)
       = reify (codeFormula (substF k t P))`.
    No new Deriv axioms, no postulates.

Commits: `[BRA-godelII-sb]`, `[BRA-godelII-sb-axiom]`.

The Goedel II contract surface (from V2) is unchanged:

```
constr5 : Fun1
step5   : (x : Term) ->
          Deriv ((atomic (eqn (ap1 thmT x) cG))
                  imp (atomic (eqn (ap1 thmT (ap1 constr5 x))
                                   (reify (codeFormula bot)))))
```

## Key discovery from session 1

BRA already has the substitution-rule infrastructure on the
PROOF-CODE side:

  * `BRA.Thm.Parts.RuleInst.encRuleInst` (proof-code encoding for the
    substitution rule):
    `encRuleInst x t y_h = nd (natCode tagRuleInst) (nd (code (var x)) (nd y_h (code t)))`

  * `BRA.Thm.Parts.RuleInst.outRuleInst` (the resulting coded formula):
    `outRuleInst x t P = codeFormula (substF x t P)`

  * `BRA.Thm.ThmT.thmTDispRuleInst` (the dispatch lemma):
      ```
      thmTDispRuleInst :
        (x : Nat) (t : Term) (P : Formula) (y_h : Tree) ->
        Deriv (atomic (eqn (ap1 thmT (reify y_h))
                           (reify (codeFormula P)))) ->
        Deriv (atomic (eqn (ap1 thmT (reify (encRuleInst x t y_h)))
                           (reify (outRuleInst x t P))))
      ```

  * `BRA.CodeCommutes.codeCommutesFormula` (meta equality):
    `codeFormula (substF x t F) = codedSubst (code t) (code (var x)) (codeFormula F)` .

So the closed-form piece is fully there; **no new ground axiom for
sb is required**.  What is missing is the PARAMETRIC bridge.

## The remaining gap for step 4

Guard p.17 step 4 reads "by the definition of j":

  4) th(x) = j  ⊃  th(4J(J(num x, 1), x) + 1) = "th(<x_>) ≠ sub(i, i)"

The construction `4J(J(num x, 1), x) + 1` is in 4y+1 form
(substitution-rule clause of th).  Decoding under Definition 12
line 2:

  KKy = num x ,  IKy = 1 ,  Iy = x ,
  th(4y+1) = sb(KKy, IKy, th(Iy)) = sb(num x, 1, th(x)) .

Under the hypothesis `th(x) = j`:

  sb(num x, 1, j)  =  sb(num x, 1, code G)  =  code(G[x_1 := num x])
                   =  code(negSubF x) .

To port this to BRA, we need a parametric Term-level analog:

  subProofEnc : Term -> Term  -- BRA's analog of  4J(J(num x,1),x)+1

with the property (parametric in x):

  ap1 thmT (subProofEnc x)
    =  ap2 sb (ap2 Pair (ap1 cor x) (reify (natCode (suc zero))))
              (ap1 thmT x) .

`thmTDispRuleInst` gives this for **closed** y_h (`reify y_h`
specialised to closed encodings).  We need it parametrically in a
FREE Term variable `x`.

### Why the closed-form is not enough by itself

Goedel II's closure (in `BRA.Thm14Abstract.Thm14.GodelII`) does
`ruleInst Con` at `ap1 constr5 (var 1)` -- a Term containing a free
`var 1` representing the universally-quantified proof index.  For the
closure to compose, step 5 must hold parametrically in `x : Term`,
not just for closed witnesses.

### Three options for the parametric bridge

**Option A: add a parametric ground axiom for thmT's subst-rule clause.**

```
axThmTSubRule : (x : Term) ->
  Deriv (atomic (eqn (ap1 thmT (subProofEnc x))
                     (ap2 sb (ap2 Pair (ap1 cor x) (reify (natCode (suc zero))))
                              (ap1 thmT x))))
```

Per `feedback_ground_axioms_ok`, ground defining-equation axioms
parametric in Term variables are fine; this is the universal
characterisation of thmT's substitution-rule clause (Guard
Definition 12 line 2).

PRO: matches Guard's argument literally; simple to state.
CON: adds a postulate-shaped axiom to BRA/Deriv.agda; needs careful
review against `feedback_no_new_deriv_axioms` (general reflection
rules forbidden, but ground defining equations OK).

**Option B: build subProofEnc to be reducible parametrically without an axiom.**

If subProofEnc is built from combinators in such a way that
`thmT (subProofEnc x)` reduces (under thmT's existing axioms) to
`sb (...) (thmT x)` for every Term x, no new axiom is needed.

Sketch: subProofEnc x = ap2 Pair tagRuleInstT (ap2 Pair varCode1T (ap2 Pair x (ap1 cor x))) .

Then  `thmT (subProofEnc x)  =  thmT (ap2 Pair tagT inner)`.  thmT's
Rec-based dispatch unfolds via axRecNd to produce a stepProto
application, which then routes through the IfLf cascade.  At the
RuleInst tag level, the dispatch invokes a substitution computation
on the encoded formula `thmT x` -- which is exactly what we want.

PRO: no new axiom; uses existing thmT's structure.
CON: requires that the IfLf cascade and the substitution combinator
inside the RuleInst dispatch reduce parametrically when the proof
component is an open Term.  This depends on whether the dispatch's
combinator is in fact "open-term reducible" -- not obvious without
inspection.

**Option C: state step 5 in closed-form and lift to parametric via Schema F / induction.**

Use `ruleF` (Schema F) or `ruleIndBT` (binary-tree induction) to
universally close the closed-form variant.  This is in keeping with
how Guard's BRA derives universally closed statements.

PRO: stays inside existing BRA primitives.
CON: requires auxiliary infrastructure; may not match Guard's
argument shape; cost-benefit unclear.

## Recommended next-session path

1. **First half-hour**: re-read `BRA.Thm.Parts.RuleInst.agda` and
   `BRA.Thm.ThmT.agda`'s `thmTDispRuleInst` proof to understand the
   IfLf cascade's behaviour on partially-open inputs.  Decide Option
   A vs B.

2. **If Option B looks viable**: write `BRA/SubEnc.agda` defining
   `subProofEnc : Fun1` (or `Term -> Term`) and prove the parametric
   reduction `ap1 thmT (subProofEnc x) = sb (...) (ap1 thmT x)` from
   existing axioms.  Target: ~250 LoC, <2s.

3. **If Option B is blocked**: switch to Option A.  Add
   `axThmTSubRule` to `BRA/Deriv.agda` as a ground axiom, with a
   header comment justifying it as Guard Definition 12 line 2.  Then
   write the parametric reduction trivially from the axiom.

4. **Either way**: write `BRA/Thm14Step4.agda` deriving step 4 from
   the parametric reduction + `sbForOutRuleInst` + thm11 step 1
   (`j = sub(i,i)`).  This composes step 4 into the form:

     Deriv ((atomic (eqn (ap1 thmT x) cG))
             imp (atomic (eqn (ap1 thmT (subProofEnc x))
                              (reify (codeFormula negSubF_x)))))

   for the appropriately formed `negSubF_x`.

## Hard constraints (unchanged from V2)

  * Small files (~250 LoC max); fast typecheck (<2s cold).
  * `--safe --without-K --exact-split`, ASCII only.
  * No new postulates; ground defining-equation axioms only if
    Option A is chosen, with explicit justification.
  * No new general reflection rules.
  * One named lemma per Guard step.

## Stop conditions (unchanged from V2)

  1. Pre-flight verification fails: re-reading guard15.pdf reveals
     a claim is wrong.  Stop and report.
  2. Single file > 250 LoC OR lemma body > 50 lines OR cold
     typecheck > 2s.  Refactor.
  3. Universal-closure trap: about to write `Deriv (not P)` for open
     P, Sigma form, or closed Con.  Stop, re-read V2 Lessons 1-4.
  4. Step 4 needs general reflection axioms.  Stop and report.

## What's done (unchanged across V3)

`BRA/Sb.agda` and `BRA/SbAxiom.agda` are stable.  Do NOT modify.

`BRA/Thm14Abstract.agda` and `BRA/GoedelII.agda` are stable.  Do NOT
modify the contract surface.

## Files this and subsequent sessions write

  * `BRA/SubEnc.agda` -- parametric subProofEnc + parametric reduction
    (Option A or B, see above).  NEXT SESSION's primary target.
  * `BRA/Thm14Step1.agda` -- internal-implication Thm 13 specialised
    to thmT.
  * `BRA/Thm14Step2.agda` -- closed Thm 13 instance for sub.
  * `BRA/Thm14Step3Int.agda` -- internal-implication step 3.
  * `BRA/Thm14Step4.agda` -- internal step 4 using subProofEnc + sb.
  * `BRA/MpEnc.agda` -- mp_enc + mp-clause infrastructure (mirror
    of subEnc for tag mp).
  * `BRA/Thm14Step5.agda` -- step 5 combining steps 3+4 + mp_enc.
  * `BRA/Thm14ConstructStep5.agda` -- final assembly of constr5 +
    step5.

Estimated total: ~1500 LoC across 8 files, ~3-4 sessions.

## Treat as routine porting

The math is clear; the architecture is set.  Each piece is a
faithful port of Guard's argument step by step.  Per-session
deliverables ship individually as topical commits.
