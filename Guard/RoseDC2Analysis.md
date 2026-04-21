# RoseDC2 — scope analysis

## Context

The plan in `NEXT-SESSION-IMPT-GODELII.md` budgets ~300 lines for
`Guard/RoseDC2.agda` to prove the fully polymorphic version of Rose's
Lemma 1 (internalised modus ponens):

```agda
roseLemma1 :
  {H : Equation} (A B : Equation) ->
  (d : Deriv H B) ->
  Sigma Term (\V ->
    (p q : Term) {hyp : Equation} ->
    -- p is a proof-encoding of A
    Deriv hyp (eqn (ap1 (thmT trivCT) p) (reify (codeEqn A))) ->
    -- q is a proof-encoding of impEqn A B
    Deriv hyp (eqn (ap1 (thmT trivCT) q)
                   (reify (codeEqn (impEqn A B)))) ->
    -- V(p,q) is a proof-encoding of B
    Deriv hyp (eqn (ap1 (thmT trivCT) (ap2 mpPair V (ap2 Pair p q)))
                   (reify (codeEqn B))))
```

After studying Ryan (1978) directly (Lemma 1 on p. 458), the statement
is meaningful, but the V-construction is much more than 300 lines of
work and -- critically -- requires either:

  (a) extending  thmT  with a new case for an MP-dispatch tag (rejected
      by the plan: "no modification of Deriv / Thm14EV3 / ProofEnc"),
      OR
  (b) constructing V via an elaborate symbolic tree-manipulation that
      uses existing tags (Fst/Snd/Pair/IfLf/TreeEq/Rec) to extract
      codeEqn B from the pair of encodings on the fly.

Option (b) is feasible in principle but non-trivial.  It would need:

  1. Parse q's structure:  q encodes  impEqn A B  = eqn (impT charA
     charB) trueT, so thmT q = nd (code (impT charA charB)) (code trueT).
  2. Extract  code B  from this nested structure via Fst/Snd
     applications targeted at the specific positions where t_B and u_B
     live inside the impT-encoded term.
  3. Reassemble  codeEqn B  = nd (code t_B) (code u_B).
  4. Prove the whole chain reduces via thmT to the desired codeEqn B.

This is on the order of 800-1500 lines of delicate encoding proofs,
per the size estimate style used in Guard's 2521-line ProofEnc.agda
for the 27 encoder combinators, given that internal MP is roughly as
complex as internal TRANS + structural extraction combined.

## What was delivered in RoseDC2.agda

Since Layer 5 (GodelIIRose.agda) does NOT need the polymorphic V (it
uses a single concrete X = enc provBot and a single concrete Y =
codeBotT), the pragmatic scope was chosen: deliver the specific
bridging lemmas actually required by Layer 5.

The delivered file provides:

| Lemma                | Content                                                 |
|----------------------|---------------------------------------------------------|
| `treeEqSelfTrue`     | `TreeEq X X = trueT`                                    |
| `treeEqFromEq`       | `X = Y  =>  TreeEq X Y = trueT`                         |
| `impTOfTreeEqFromEq` | `X = Y  =>  impT (TreeEq X Y) P = P`                    |
| `impTOfTreeEqMP`     | Modus-ponens form of the above                          |
| `roseContradict`     | Main closure: `X = codeBotT` + impT-consistency → false |
| `roseContradictVia`  | Chained variant for two-step bridges                    |
| `treeEqFalseToImpT`  | Convert TreeEq-form consistency to impT-form            |

Each is short (1-6 lines of Agda) and uses only axIfLfL/N,
axTreeEq{LL,LN,NL,NN}, treeEqSelf, cong, trans + the toolbox from
`Guard/ImpTProp.agda`.

## What Layer 5 needs from Layer 4

Given the existing  `Guard/GodelIIV3.agda`  proof path (which uses
`conSentenceV3` = eqn (TreeEq ... codeBotT) falseT), the Rose-version
`Guard/GodelIIRose.agda`  rephrases consistency in impT form:

```agda
conSentenceRose = eqn (impT (ap2 TreeEq (ap1 (thmT (reify cGSV3))
                                              (var zero))
                                         codeBotT)
                             falseT)
                      trueT
```

To derive  `Deriv conSentenceRose (eqn trueT falseT)` , Layer 5:

  1. Instantiates var 0 with  enc provBot  (from `necessitation
     godelIDerivV3`, already in Guard.ProvV3 / GodelIIV3).
  2. Uses the substituted hypothesis (impT form with enc provBot fixed).
  3. Uses `corr provBot` to show  `thmT cGSV3 (enc provBot) = codeBotT`.
  4. Applies `roseContradictVia`  with X = `thmT cGSV3 (enc provBot)`
     and Y = codeBotT to get  falseT = trueT.
  5. Applies  `ruleSym`  to get  trueT = falseT  -- the output of
     Gödel II.

Layer 5 is therefore ~100-150 lines, matching the plan's estimate.

## Why the full polymorphic lemma was not attempted

- The plan explicitly permits documenting an obstruction and falling
  back to a pragmatic delivery.
- The polymorphic V is NOT required for the stated Layer-5 goal
  (Gödel II for the Gödel sentence's hypothesis).
- Delivering the full V universally would require substantially more
  effort than the 300-line budget, with no guarantee that Gödel II
  closes more cleanly afterwards than via the targeted bridging lemmas
  already provided.
- Historical precedent: the `StrongPhiCorrAnalysis.agda` and
  `EncCorrPfAnalysis.agda` show that attempting polymorphism where a
  concrete construction suffices has previously been a time sink on
  this project.

## Next steps (optional)

If a future session wants the polymorphic roseLemma1:

  1. Define `impEqn : Equation -> Equation -> Equation` concretely --
     most naturally as  `impEqn A B = eqn (impT (TreeEqOfEqn A)
     (TreeEqOfEqn B)) trueT`  where  `TreeEqOfEqn (eqn t u) = ap2
     TreeEq t u`.
  2. Prove a per-Deriv-constructor family of specialized Lemma-1
     instances (as Ryan does by induction on the derivation).  Each
     instance corresponds to one `p_f` in RoseDC1 + a combinator
     matching that rule's internal MP behaviour.
  3. Package the instances into a master  roseLemma1  by induction on
     Deriv H B.

Step 2 is the bulk of the work -- roughly one combinator per Deriv
constructor, each ~50-100 lines, totalling ~1500-2000 lines.
