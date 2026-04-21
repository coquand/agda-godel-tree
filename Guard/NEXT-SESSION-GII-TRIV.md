# Next Session: close stepFCoreFromConStrong

## Command

From `/Users/coquand/CHWISTEK`:

```
claude
```

Then paste:

```
Read Guard/NEXT-SESSION-GII-TRIV.md for full context, then proceed.

Goal: close  stepFCoreFromConStrong : Deriv Triv ConTrivRoseStrong ->
                                       Deriv Triv (eqn (TreeEq TP diagBody) poo)
(where TP = thmT trivCT (Pair v0 v1)) to finalise
godelIIClassicalTrivStrongWithCoreFromCon, and hence close the
Rose-style classical Gödel II over Triv.

Infrastructure in place (main):
  * Guard/ImpT.agda                 object-level impT toolkit.
  * Guard/ImpTProp.agda             propositional theorems for impT.
  * Guard/RoseLemma1T.agda          Ryan Lemma 1 over thmT trivCT.
  * Guard/RoseEFun.agda             eT : Fun1 object-level e-function.
  * Guard/RoseEncE.agda             eTree meta-level spec.
  * Guard/GodelIIClassicalTriv.agda Schema F + dAux + dNegGsRose.
  * Guard/GodelIIClassicalTrivStrong.agda
                                    ConTrivRoseStrong + universal Rose
                                    negations + generaliser functions
                                    (dNegGsRoseUnivGen, dNegGsRoseInstGen).
  * Guard/ROSE-CHAIN-DESIGN.md      full design analysis.

Conventions: --safe --without-K --exact-split, no postulates, no holes.
Use ~/.cabal/bin/agda-2.9.0.
Commit after each major piece.

Proceed autonomously.
```

## Status (as of 2026-04-21)

Committed this session:

```
ac2ddb3  [gii-triv-strong] Add dNegGsRoseUnivGen + dNegGsRoseInstGen generalisers
0043d19  [gii-triv-strong] Introduce ConTrivRoseStrong + framework
3085f58  [gii-triv] dNegGsRose: Rose-style e-negation of gsCR at Pair v0 v1
93e0f31  [rose-efun] Introduce eT Fun1 combinator + design memo
```

Previously committed:
```
742a059  [doc] NEXT-SESSION-GII-TRIV.md: handoff for Rose-chain closure
26b7a92  [doc] RoseChainAnalysis: option (i) executed
21da0a1  [gii-triv] Integrate RoseLemma1T and exhibit constructible dAux
7ff35eb  [rose-l1t] RoseLemma1T: Ryan-style Lemma 1 over thmT trivCT
```

## What's delivered

### Strong consistency and framework (`GodelIIClassicalTrivStrong.agda`)

```agda
ConTrivRoseStrong : Equation
ConTrivRoseStrong = eqn
  (impT (ap2 TreeEq (ap1 (thmT trivCT) (var zero))
                    (ap1 eT (ap1 (thmT trivCT) (var (suc zero)))))
        falseT)
  trueT

StepFCoreFromConStrong : Set
StepFCoreFromConStrong =
  Deriv Triv ConTrivRoseStrong -> StepFCoreType

godelIIClassicalTrivStrongWithCoreFromCon :
  StepFCoreFromConStrong ->
  Consistent Triv ->
  Deriv Triv ConTrivRoseStrong ->
  Empty
```

The important correction vs. the earlier `StepFCoreType : Set = Deriv
Triv (...)` is that  StepFCoreType  CANNOT be supplied without
dConStrong -- deriving it in Triv directly would give Deriv Triv gsCR,
which (by godelIClassical + Consistent Triv) contradicts Triv's
consistency.

### Generaliser functions

```agda
dNegGsRoseUnivGen :
  {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (thmT trivCT) (var zero)) (reify cGSCR)) ->
  Deriv hyp B_negGsUniv

dNegGsRoseInstGen :
  (Z : Term) {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (thmT trivCT) Z) (reify cGSCR)) ->
  Deriv hyp (eqn (ap2 TreeEq (ap2 TreeEq (ap1 (thmT trivCT) Z) diagBody)
                              poo)
                  (ap2 Pair O O))
```

These give the Rose-style negation of gsCR as a META-LEVEL
implication: take a hyp-polymorphic derivation of "Z encodes gsCR" and
return a hyp-polymorphic derivation of the negation of gsCR at that Z.

The value of dNegGsRoseInstGen: if we can SUPPLY a Deriv hyp
(thmT trivCT Z = reify cGSCR), we get for free a Deriv hyp of the
e-negated equation.

## The real blocker

To close stepFCoreFromConStrong, we need to construct under Triv:

```
Deriv Triv (eqn (ap2 TreeEq (ap1 (thmT trivCT) (ap2 Pair (var 0) (var 1)))
                             diagBody)
                 poo)
```

### Why this is hard

Informally: "for all (v0, v1), Pair v0 v1 doesn't encode gsCR".

Rose's chain via dConStrong + Lemma 1:
1. Assume (hypothetically) Pair v0 v1 DOES encode gsCR (i.e., assume H_enc).
2. Under H_enc, dNegGsRoseUnivGen (at Z := Pair v0 v1, with hyp = ???)
   gives an encoding V of "¬gsCR". Specifically: thmT trivCT V =
   reify (eTree cGSCR).
3. Instantiate dConStrong at (var 0 := V, var 1 := Pair v0 v1):
   impT (TreeEq (thmT trivCT V) (eT (thmT trivCT (Pair v0 v1))))
        falseT = trueT.
4. Under H_enc: eT (thmT trivCT (Pair v0 v1)) = eT (reify cGSCR)
     = reify (eTree cGSCR)  (via eTCorrect).
5. Also under H_enc: TreeEq (reify (eTree cGSCR)) (reify (eTree cGSCR))
     = O (treeEqSelf).
6. impT O falseT = falseT.  But (3) says impT... = trueT.  Contradiction.
7. Hence under H_enc + dConStrong-in-Triv, bot.
8. Contrapositively: under dConStrong-in-Triv, H_enc is NOT derivable,
   so TreeEq (thmT trivCT (Pair v0 v1)) (reify cGSCR) = poo (for any
   v0, v1).

### Step (2) is where things break

dNegGsRoseUnivGen needs `Deriv hyp (thmT trivCT (Pair v0 v1) = reify
cGSCR)`. Under hyp = H_enc specifically, this is just ruleHyp{H_enc}.
But to use the result at hyp = Triv, we'd need this Deriv under Triv
 -- which requires Pair v0 v1 to actually encode gsCR in Triv, which
it doesn't (under consistency).

### What's needed

One of:

(α₁) A function `lift : Deriv Triv X -> Deriv H X` for any H.
     Requires meta-level tree transformation of the Deriv tree,
     substituting ruleHyp{Triv} with axRefl O (since Triv = eqn O O
     is derivable everywhere via axRefl).  Feasible but requires
     recursion over Deriv's data constructors.

(α₂) A "conditional" formulation of the chain via impT at the Triv
     level: derive `Deriv Triv (impT HEncAsTruthValue bot = trueT)`
     directly, avoiding the need to lift dCon.  The tricky part is
     constructing this impT derivation under Triv (which requires
     roughly the Lemma 1 content internalized as a Triv-derivable
     implication).

(α₃) A multi-hypothesis Deriv (generalise Deriv to take a list of
     hypotheses).  Major refactor.

(α₄) Restate godelIIClassicalTrivStrong under hypothesis =
     godelSentenceV3 or a compound  Triv-AND-H_enc -style hypothesis.
     Not the intended theorem statement but a more tractable target.

### Recommended

**(α₁) lift function**.  This is a clean Agda meta-function that
transports Deriv trees across hypothesis changes when the source
hypothesis is trivially derivable (e.g., Triv = O = O).

Implementation:
```agda
lift : {H : Equation} -> Deriv (eqn O O) X -> Deriv H X
lift (axI t)               = axI t
lift (axFst a b)           = axFst a b
...                        -- every axiom case is polymorphic
lift (ruleHyp {hyp = _})   = axRefl O  -- the discharge step
lift (ruleSym d)           = ruleSym (lift d)
lift (ruleTrans d1 d2)     = ruleTrans (lift d1) (lift d2)
...                        -- structural rules recursively lift
```

~80-120 lines of pattern-matching.  Once available, the Rose chain
transcribes directly.

Alternatively: define dConStrong to be polymorphic in hyp from the
start, as a META-LEVEL parameter:

```agda
dConStrongPoly : {hyp : Equation} -> Deriv hyp ConTrivRoseStrong
```

This is stronger than `Deriv Triv ConTrivRoseStrong` (it says Con is
derivable in EVERY hyp context).  For Triv-theorems that don't use
ruleHyp{Triv} in their proof structure, this polymorphism holds
vacuously — but the caller needs to be aware.

### Size estimate for closing

- Option (α₁) lift function: 80-120 lines.
- Option (α₂) impT-internalization: 200-300 lines, more intricate.
- Option (α₃) multi-hyp Deriv: 500+ lines (refactor).

Recommendation: start with (α₁).

## Files to touch (in order)

1. **Read**  `Guard/ROSE-CHAIN-DESIGN.md` for the full design analysis.
2. **New**   `Guard/DerivLift.agda`  with  `lift : Deriv (eqn O O) X
              -> Deriv H X`  plus specialisations.
3. **Extend** `Guard/GodelIIClassicalTrivStrong.agda`  with the full
              stepFCoreFromConStrong implementation using lift + the
              existing dConStrong + dNegGsRoseInstGen chain.

## Sanity commands

```
time ~/.cabal/bin/agda-2.9.0 Guard/RoseLemma1T.agda
  # 0.25s, no output
time ~/.cabal/bin/agda-2.9.0 Guard/GodelIIClassicalTriv.agda
  # 0.13s, no output
time ~/.cabal/bin/agda-2.9.0 Guard/GodelIIClassicalTrivStrong.agda
  # 0.11s, no output
time ~/.cabal/bin/agda-2.9.0 Guard/RoseEFun.agda
  # 0.04s, no output
```
