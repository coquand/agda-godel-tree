# Goodstein-axiom plan for closing stepFCoreFromConStrong

## Motivation

Ryan's Main Theorem proof (= Rose1.pdf Theorem 4, p.383) uses, at the
step `th(p_G(z, 0)) = {G(z) = 0} → th(V(p_G(z, 0))) = {se(N,N) =
th(z)}` "by lemma 1", a reflection derivation `|a, b| = 0 ⊢ a = b`
in ℰ^rec_E.  In Goodstein's PRA (Rose's reference [1]), reflection
is derived from the characteristic equation

    eq(a, b) · a = eq(a, b) · b

and the definition of eq.  That equation is a THEOREM of Goodstein's
PRA, provable by induction on numerals.

Our tree analogue: Rose/Ryan's `|a, b| = 0` corresponds to our
`TreeEq a b = O`; Rose/Ryan's `eq(a, b) · x` corresponds to our
`IfLf (TreeEq a b) (Pair x O)`.  The tree-Goodstein equation is

    IfLf (TreeEq a b) (Pair a O) = IfLf (TreeEq a b) (Pair b O)

universally in a, b.  Given `Deriv hyp (TreeEq a b = O)`, substituting
the hyp on both sides + axIfLfL yields `Deriv hyp (eqn a b)` — exactly
reflection.

Deriving this equation from our existing primitives is genuinely
complex: it requires nested Schema F (ruleF), and the step case at
Pair/Pair involves axTreeEqNN's nested IfLf output which doesn't
simplify uniformly.  Estimated derivation: 400-800 lines.

Adding it as a new Deriv axiom is shape-legitimate: it's an equation
of the form `f(a, b) = g(a, b)`, NOT a universally-quantified
implication.  Goodstein's PRA also adds its analogous equation as a
characteristic axiom of the equality-test machinery.

## Plan

### Step 1: `Guard/Step.agda` — add `axGoodstein` constructor

```agda
axGoodstein : (a b : Term) ->
              Deriv hyp (eqn (ap2 IfLf (ap2 TreeEq a b) (ap2 Pair a O))
                             (ap2 IfLf (ap2 TreeEq a b) (ap2 Pair b O)))
```

~4 lines.  No risk.

### Step 2: `Guard/DerivLift.agda` — add lift case

```agda
lift (axGoodstein a b) = axGoodstein a b
```

1 line.  Trivial (axGoodstein is polymorphic in hyp).

### Step 3: `Guard/RoseLemma1T.agda` — add Lemma1T encoding case

Add `roseL1T_Goodstein : (H : Equation) (a b : Term) -> Lemma1T H (eqn (ap2 IfLf (ap2 TreeEq a b) (ap2 Pair a O)) (ap2 IfLf (ap2 TreeEq a b) (ap2 Pair b O)))`.

Pick a new tag (e.g., `n29`); construct vPa, vPb encoding the
axGoodstein invocation; provide vCorr and vPass via new helpers in
`Guard/ProofEnc.agda`.

Also update the top-level `roseLemma1T` dispatch to handle
`(axGoodstein a b)`.

~30-60 lines.

### Step 4: `Guard/Thm14EV3.agda` — add ProofE3 encoding case

Parallel to existing axI, axFst, etc. cases.  Needs:
- A new tag (n29) — extend `Guard/ThFunTForV3.agda`'s `ndDispatchV3`
  to branch on n29.
- A new `case29` Fun2 implementing the IfLf/TreeEq/Pair structure.
- A `thm14EV3Goodstein` function producing a ProofE3 record.
- Update the top-level `thm14EV3` dispatch.

~80-150 lines.  Highest risk.

### Step 5: `Guard/ProofEnc.agda` — add encoding helpers

`encAxGoodsteinCorr` and `encAxGoodsteinPass` — parallel to
`encAxReflCorr`/`encAxReflPass` etc.

~40-80 lines.

### Step 6: `Guard/GodelIIClassicalTrivStrong.agda` — write the chain

Transcribe Ryan's Main Theorem proof / Rose1.pdf Theorem 4's chain
using existing `thm14EV3`, `roseLemma1T`, `eTCorrect`,
`godelIClassical`, and the new `axGoodstein` + derived `treeEqRefl`
meta-function.

~200-400 lines.

## Total

~400-700 lines, 2-3 focused sessions.

## This-session goal

Minimally: steps 1 and 2 (add axiom + DerivLift update).  Commit.

Stretch: step 3 (roseLemma1T update).  Commit after typechecking.

Handoff: write `Guard/NEXT-SESSION-GOODSTEIN.md` with remaining
steps 4-6.
