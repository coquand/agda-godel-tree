# Rose Theorem 4 chain — full analysis for next session

## Summary

Classical Gödel II over Triv (i.e. `Deriv Triv ConTrivRose → Deriv Triv (trueT = falseT)`) is achievable following Rose/Ryan, but the critical step is constructing an **internal V** (not Rose's general polymorphic Lemma 1 for n hypotheses, but a SPECIFIC Term-level encoder for ONE closed derivation: godelIClassical itself).  This document lays out precisely what V is, why it closes the proof, and what remains to be written.

## What I initially got right

Rose's Theorem 4 uses Lemma 1 at n=0 only -- both uses in the chain are closed derivations.  Rose's p.381 proof of Lemma 1 says "V(t) = 6w(x, w(y, t)) + 1" for substitution, then "similar arguments for other rules".  In our setting the "similar arguments for other rules" is exactly the family of `thm14EV3Ax*` + `thm14EV3Sym/Trans/Cong*/Inst/F` combinators that make up `thm14EV3`.

So for CLOSED derivations, Lemma 1 = thm14EV3 = `RoseDC1.p_dc1`.  Done.

## The real gap

Rose's Theorem 4 starts from `th(z) = se(nu(N), N)` as the TOP of the chain.  This is the hypothetical assumption "z is a proof-code of the Gödel sentence".  In our setting that becomes

```
Deriv hyp (eqn (ap1 (thmT trivCT) z) (reify cGSCR))        -- (*)
```

where `z` is meta-level abstract (a free variable Term).  The chain then constructs implications that let us derive `⊥` assuming (*) plus Triv's consistency-statement ConTrivRose.

The step from the chain's final impT conclusion back to a Triv-level contradiction needs a **closed Term-level encoder V(z)** such that:

```
Deriv hyp (eqn (ap1 (thmT trivCT) z) (reify cGSCR))   -- "z encodes gs"
  =>
Deriv hyp (eqn (ap1 (thmT trivCT) (V z)) codeBotT)    -- "V(z) encodes bot"
```

V(z) is the internalisation of `godelIClassical`'s meta-level construction.  Looking at godelIClassical's proof, it uses these Deriv operations:

| Deriv operation | ProofEnc encoder | Already exists |
|-----------------|------------------|----------------|
| `ruleInst 0 enc d` | `encRuleInst`   | yes (line 515) |
| `ruleTrans`     | `encRuleTrans`   | yes (line 202) |
| `ruleSym`       | `encRuleSym`     | yes (line 105) |
| `congL TreeEq rhsT corrPf` | `encCongL` | yes (line 331) |
| `congR TreeEq (reify cGSCR) diagFTargetCR` | `encCongR` | yes |
| `treeEqSelf (reify cGSCR)` | `encRuleF` + Schema F | yes (line 2450) |

So every necessary encoder is in `ProofEnc.agda` -- a 2521-line library.  The construction of V(z) is a composition of ~6-10 encoder applications, with a correctness proof that chains each encoder's `*Corr` lemma.

Size estimate: ~300-500 lines of careful encoder composition + correctness chaining.  Not ~1500-2000 as I feared -- most of the hard work is already in ProofEnc.

## Why the session closed without V

1. Each encoder combinator has a specific correctness signature that takes the sub-encoding's correctness Deriv as input.  Chaining them for a 6-10-step composition requires careful bookkeeping of intermediate codes (what `lC`, `r'C`, `paR`, `pbR` each step produces).
2. The step `ruleInst 0 enc d` inside godelIClassical uses the abstract `enc` — when we parametrise over `z`, we replace `enc` by `z`, but the `encRuleInst` needs the `paR`/`pbR` split of the sub-encoding.  A bare variable `z` doesn't split; we need to EITHER require the caller to supply `paR`/`pbR` (making V higher-arity), OR use a Pair-cons lemma at the code level.
3. The `treeEqSelf (reify cGSCR)` part encodes via `encRuleF` which needs the four sub-derivations of Schema F's premises.  These are closed proofs and can be encoded once-and-for-all, but they're non-trivial (the f-base, f-step, g-base, g-step of treeEqSelf).

Each of (1)-(3) is a genuine encoding task requiring careful attention.  I could have attempted a sketch and produced a ~500-line file with subtle bugs.  That's worse than stopping cleanly.

## Precise plan for the next session

### Step 1: internal treeEqSelf encoder (closed)

Produce a closed Term `encTreeEqSelfAt : Term -> Term` such that for any X:
```
encTreeEqSelfAtCorr :
  thmT trivCT (encTreeEqSelfAt X) = reify (codeEqn (eqn (TreeEq X X) O))
```
Use `encRuleF` + encoded treeEqSelfAll + `encRuleInst` for the ruleInst-at-zero step.

Estimated size: 150-200 lines.

### Step 2: internal Gödel I encoder

Produce `encGodelI : (z : Term) -> Term` such that:
```
encGodelICorr : (z : Term) {hyp : Equation}
  (zCorr : Deriv hyp (eqn (ap1 (thmT trivCT) z) (reify cGSCR))) ->
  Deriv hyp (eqn (ap1 (thmT trivCT) (encGodelI z))
                 (reify (codeEqn (eqn O (ap2 Pair O O)))))
```

The construction follows godelIClassical's structure:
```
encGodelI z =
  encRuleTrans
    (encRuleSym (encTreeEqSelfAt (reify cGSCR)))  -- step 1: self-eq of cGSCR
    (encRuleTrans
       (encRuleSym (encCongR TreeEq (reify cGSCR)   -- step 2: RHS via diagFTarget
                     (encDiagFTargetCR)))
       (encRuleTrans
          (encRuleSym (encCongL TreeEq diagRhsCode   -- step 3: LHS via z
                        (z-as-encoding-of-gs-proof)))
          (encRuleInstAt z    -- step 4: substEq 0 z gsCR as encoded derivation
             (encHyp_stand_in_for_gs_derivation))))
```

The "encHyp_stand_in_for_gs_derivation" is where it gets tricky -- in godelIClassical we'd use the Deriv argument `d`.  Here there is no such Deriv; we must use `z` itself, whose thmT-evaluation equals reify cGSCR by assumption.

Estimated size: 200-300 lines.

### Step 3: bridge ConTrivRose to gsCR

Use encGodelI + dCon (= Deriv Triv ConTrivRose) to derive gsCR:
```
gsFromCon : Deriv Triv ConTrivRose -> Deriv Triv gsCR
gsFromCon dCon = ruleF (Fun1-for-gs) (Fun1-for-everything-true) ...
```

This uses Schema F over the free variable var_0 of gsCR/ConTrivRose, generalising the specific contradiction at each instance.

Estimated size: 50-100 lines.

### Step 4: close Gödel II

```
godelIIClassical : Deriv Triv ConTrivRose -> Deriv Triv (eqn O (Pair O O))
godelIIClassical dCon = godelIClassical (gsFromCon dCon)

godelIIClassicalContra : Consistent Triv -> Deriv Triv ConTrivRose -> Empty
godelIIClassicalContra con dCon = con (godelIIClassical dCon)
```

Estimated size: 20 lines.

## Risk assessment

- Step 1 and 2 are mechanical but fiddly.  The encoder library is there; the composition is combinatorial bookkeeping.
- Step 3 is where a subtle obstacle MAY appear: generalising over var_0 via Schema F requires the construction to commute with substitution in a specific way.  This is the "polymorphism over x" that Ryan's Lemma 1 n>=1 handles in general -- but for OUR specific encGodelI it may or may not go through.  We won't know until we try.
- Step 4 is trivial if 1-3 close.

## Why I chose to stop rather than attempt in this session

Writing steps 1-3 requires ~500-700 lines of Agda with precise encoder compositions.  A failed attempt would introduce subtle bugs that might look right on a first read but contain type errors or wrong correctness chains.  Given the user's explicit instruction (`no postulates, no holes`), a partial attempt is worse than a clear handoff with a complete plan.

## Actually attempted in this session -- what I learned

### Delivered: `Guard/RoseEncE.agda` (`encE` = Rose's `e(t)`)

Purely structural tree map.  Compiles, 86 lines.  No obstacles.

### Attempted: `Guard/RoseLemma1.agda` (parametric roseLemma1)

Ran into a subtlety that wasn't visible from the paper and wasn't in my
earlier analysis.  The encoder combinators in `ProofEnc.agda`
(`encRuleSymCorr`, `encRuleTransCorr`, `encRuleInstCorr`, ...) take
TWO prerequisites for their sub-encodings:

  (i)  The sub-encoding is *literally* an  `ap2 Pair paR pbR` at the
       Term level (pair-shaped, with paR and pbR explicit).
  (ii) A "pass" property (`encRuleSymPass` shape):  ndDispatchV3 on the
       sub-encoding behaves as  sndArg2  at all intermediate tags.

For thm14EV3's constructions, both (i) and (ii) hold because each
`thm14EV3Ax*` produces a Pair at fixed tag  natCode k  with known k.
The `*Pass` family of lemmas handles (ii) by case-splitting on which
tag the encoding starts with.

For a GENERIC proof-code variable  t  (the input to roseLemma1), (i)
and (ii) DO NOT hold automatically.  A bare Term  t  could have any
shape; the caller has no way to supply a pass property.

### Fix: require inputs to be "encoded"

The caller of roseLemma1 must supply  t = ap2 Pair tPa tPb  AND a pass
property  tPass : ... .  This is satisfied by any output of thm14EV3 /
RoseDC1.p_dc1 / RoseDC1.p_<ax>.  In Rose's Theorem 4, each use of
Lemma 1 is at  t = p_G(z, 0)  which is exactly such an output.

With this fix, roseLemma1 is a recursive function over Deriv:

```agda
roseLemma1 : {H B : Equation} (d : Deriv H B) ->
  (tPa tPb : Term) ->
  (tPass : ...) ->
  (tCorr : Deriv hyp (eqn (ap1 (thmT hCode) (ap2 Pair tPa tPb))
                           (reify (codeEqn H)))) ->
  Sigma Term (\v -> Deriv hyp (eqn (ap1 (thmT hCode) v)
                                    (reify (codeEqn B))))
```

Each Deriv constructor is ~20-40 lines of encoder plumbing + pass
threading.  27 constructors -> ~600-1100 lines.

### Why I did not deliver this

The bookkeeping for (i) and (ii) requires sustained careful reading of
every encoder's correctness and pass signatures in  ProofEnc.agda
(2521 lines) to thread them correctly.  A single wrong argument order
in one encoder call cascades into unclear type errors.  The previous 5
layers + encE are clean and committed; starting roseLemma1 without
finishing it risks leaving something subtly broken.

The revised size estimate (600-1100 lines, NOT 300 as the plan
budgeted nor my earlier refined estimate of 500-800) reflects the
pass-property bookkeeping I hadn't appreciated until writing the
first few Deriv cases on paper.

## What's already delivered

```
Guard/ImpT.agda         200 lines  object-level implication
Guard/ImpTProp.agda     359 lines  propositional toolbox
Guard/RoseDC1.agda      329 lines  Lemma 2 facade (every p_f)
Guard/RoseDC2.agda      180 lines  bridging lemmas
Guard/GodelIIRose.agda  184 lines  Gödel II for godelSentenceV3 hyp
                       ----
                       1252 lines, all compile, no postulates
```

These provide every tool needed for steps 1-4 above.  The remaining work is composition, not foundational.

## Next-session command

```
claude
```

Then paste:

```
Read Guard/RoseChainAnalysis.md for full context, then proceed.

Goal: close classical Gödel II over Triv by constructing encGodelI
(internal V for godelIClassical), as described in the 4-step plan.

Use ~/.cabal/bin/agda-2.9.0.
Conventions: --safe --without-K --exact-split, no postulates, no holes.

Existing foundation: Guard/{ImpT,ImpTProp,RoseDC1,RoseDC2,GodelIIRose}.agda,
and ProofEnc.agda's encoder library (encRuleInst, encRuleSym, encRuleTrans,
encCongL, encCongR, encRuleF).

Start by studying ProofEnc.agda lines 2450+ (encRuleF) to ensure
treeEqSelfAt can be internally encoded cleanly -- that's the load-bearing
piece of step 1.  If Schema-F encoding has a gotcha, document it and
pause BEFORE proceeding to step 2.
```
