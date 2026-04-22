# Next session: Gödel II at the Provable (BRA) layer

## Context

The session of 2026-04-21 established the propositional Provable layer
above our equational Deriv, following Guard 1963 BRA.

The session of 2026-04-22 added the Provable→Deriv soundness bridge,
the ConBRA formula, the meta-form Th 13 lift (provThm14E), and the
reductio closure step (provableGodelIBridge), then **completed the
Option A soundness refactor**: `ruleInst` now requires its
Hilbert-Bernays side condition, the live BRA Gödel II core (32
modules) typechecks under the new sound constructor, and 19
abandoned/unsound modules are correctly type-rejected (see
`SOUNDNESS.md`).

What remains is the chain that produces a closed inhabitant of
`ChainBRA = Provable (atomic Triv) (ConBRA imp atomic gsCR)`.

## What's delivered (committed)

### Guard/Formula.agda (~65 lines)

`Formula` data type: `atomic | not_ | _imp_`, plus formula-level
substitution `substF`.

### Guard/Provable.agda (~85 lines)

```agda
data Provable (hyp : Formula) : Formula -> Set where
  fromDeriv  : {eq : Equation} ->
               ({h : Equation} -> Deriv h eq) ->
               Provable hyp (atomic eq)
  ruleHypP   : Provable hyp hyp
  axK, axS, axNeg         -- Guard 1963 ax 11, 12, 13
  axEqTrans, axEqCong1,
  axEqCongL, axEqCongR    -- Guard 1963 ax 4, 5, 6, 7
  mp                      -- modus ponens
```

No `ruleSubP` (substitution at Formula level is available via the meta-
function `substF`; a Provable-level rule would require deduction-theorem
side conditions that we deferred).

### Guard/ProvableLemmas.agda (~105 lines)

```agda
provI        : (P : Formula) -> Provable hyp (P imp P)   -- I = SKK
deductionThm : Provable P Q -> Provable hyp (P imp Q)    -- Guard Ex 19
```

Deduction theorem proved by structural induction over all Provable
constructors. One acknowledged `CoverageNoExactSplit` warning on the
`mp` case (intrinsic to index unification; function is correct).

### Guard/ProvableEqLifts.agda (~85 lines)

```agda
hypSyll'     : rule form of hypothetical syllogism
prRefl       : a = a via fromDeriv (axRefl a)
prSym        : a = b -> b = a
prTrans      : a = b -> b = c -> a = c
prCong1/L/R  : congruences for unary / binary-left / binary-right functors
```

### Guard/SOUNDNESS.md

Audit of `ruleInst` call sites against the Hilbert-Bernays side condition
"x not free in hyp". `godelIClassical` and related sound uses identified;
`GodelIIRose` / `GodelIIV3` / scaffolding modules are unsound by the
side condition and will not be used for the new Gödel II chain.

### Guard/GUARD-BRA-TEMPLATE.md

The original template for this refactor; steps 1-5 marked done; steps 6-8
(Th 12-13, Th 11, Th 14) remain.

### Guard/ProvableSound.agda (~145 lines)  [2026-04-22]

```agda
sem        : Formula -> Equation -> Set
provSound  : sem hyp ambient -> Provable hyp Q -> sem Q ambient
provExtract       : sem hyp ambient -> Provable hyp (atomic eq) -> Deriv ambient eq
provExtractTriv   : Provable (atomic Triv) (atomic eq) -> Deriv Triv eq
```

Negation interpreted classically (axNeg via emptyElim).  All Provable
constructors have natural Deriv-level meanings.  No postulates.

### Guard/ConBRA.agda (~90 lines)  [2026-04-22]

```agda
conBRAEqn          : Equation
ConBRA             : Formula
conBRAEqnAt X      : closed form of conBRAEqn after substEq zero X
conBRAEqnSubstZero : substEq zero X conBRAEqn  ≡  conBRAEqnAt X
```

The trivCT bridging via trivCTDef handles the abstract definition in
SubstTForPrecompClassical.

### Guard/ProvableTh13.agda (~105 lines)  [2026-04-22]

```agda
provNec        : ProofE3 Triv eq -> Provable hyp (atomic (thmT trivCT enc = code eq))
provThm14E     : Deriv Triv eq    -> same conclusion (composes thm14EV3 + provNec)
provThm14EFor  : convenience wrapper for callers with a polymorphic Deriv
```

This is META Th 13: from a meta-Deriv proof of an equation, lift the
encoded-proof correctness into the Provable layer via fromDeriv.  The
INTERNAL Th 13 (where f(x)=y is itself a Provable assumption, requiring
a Df Term combinator) remains the substantial chain work — see below.

### Guard/ProvableGodelIBridge.agda (~75 lines)  [2026-04-22]

```agda
provableGodelIBridge :
  Consistent Triv ->
  Provable (atomic Triv) (atomic gsCR) -> Empty

provableGodelIBridgeAt : variant parameterised over hyp + sem witness.
```

This is the *closure step*: once the Th 13 + chain produces an implication
`Provable hyp (atomic conBRAEqn imp atomic gsCR)`, godelII_BRA decomposes:

```agda
godelII_BRA con dProv =
  provableGodelIBridge con (mp chainImpl dProv)
```

Sound per Guard/SOUNDNESS.md: godelIClassical operates at hyp = Triv
(closed) so its internal ruleInst calls satisfy the side condition.

## Quick reference: using the delivered infrastructure

### Pattern: lifting a polymorphic Deriv fact as a Provable axiom

```agda
-- Given: d : {h : Equation} -> Deriv h (eqn A B)
-- Goal:  Provable hyp (atomic (eqn A B))
-- Use:   fromDeriv d

-- Given: d : {h : Equation} -> Deriv h (eqn A B)
-- Goal:  Provable hyp (P imp atomic (eqn A B))   (any P)
-- Use:   mp (axK (atomic (eqn A B)) P) (fromDeriv d)
```

### Pattern: chaining via axS (the deduction theorem's mp case)

Given `dPRQ : Provable hyp (P imp (R imp Q))` and `dPR : Provable hyp (P imp R)`:

```agda
mp (mp (axS P R Q) dPRQ) dPR   : Provable hyp (P imp Q)
```

### Pattern: using hypSyll' for transitive implication

```agda
-- Given: dPQ : Provable hyp (P imp Q), dQR : Provable hyp (Q imp R)
-- Goal:  Provable hyp (P imp R)
hypSyll' P Q R dPQ dQR
```

### Worked example: impT-form equality rewrite

Suppose we have `d : Deriv Triv (eqn (ap1 F x) y)` and want to derive, as
a Provable, that `Provable Triv (atomic (eqn (ap1 F x) y))`.

```agda
-- d is NOT polymorphic in hyp (it's specifically at Triv).
-- We cannot use fromDeriv directly.
--
-- Option 1: if d is unconditionally derivable (via only polymorphic
-- rules), it IS polymorphic; fromDeriv works.
--
-- Option 2: if d uses ruleHyp{Triv} but no other hyp dependence,
-- manually construct a polymorphic variant.  Typically one rewrites
-- d's ruleHyp{Triv} with axRefl O (since Triv = eqn O O, the trivial
-- axiom).  This is what Guard.DerivLift does.

-- See e.g. GodelIClassical.agda's use of lift.
```

### Minimal next-session imports

For Gödel II at the Provable layer:

```agda
open import Guard.Base
open import Guard.Term
open import Guard.Step using (Deriv ; Consistent)
open import Guard.ThFunTForV3 using (thmT)
open import Guard.SubstTForPrecompClassical using (trivCT ; gsCR)
open import Guard.GodelIClassical using (godelIClassical)
open import Guard.ProvV3 using (codeBotT)
open import Guard.ThFun using (codeEqn)
open import Guard.Thm14EV3 using (thm14EV3 ; ProofE3 ; encT ; corr)
open import Guard.ProofEnc                          -- encoders for Th 13

open import Guard.Formula
open import Guard.Provable
open import Guard.ProvableLemmas
open import Guard.ProvableEqLifts
```

### Known quirk: `CoverageNoExactSplit` warning

`deductionThm`'s mp case produces ONE such warning. It is intrinsic to
pattern matching on `Provable`'s index-unified conclusion; the function
is correct, case-tree reduction may not be definitional for this case,
and downstream uses don't depend on such reduction. **Do not spend time
trying to eliminate it.**

## What remains: Gödel II chain transcription

### The target

Guard 1963 Th 14: `th(y) ≠ '0 = 1'` is valid but unprovable in BRA.

In our system, `th(y) ≠ '0 = 1'` corresponds (under the tree encoding)
to the equation `TreeEq(thmT trivCT (var 0), codeBotT) = falseT`.
The formula-level version is:

```agda
conBRAEqn : Equation
conBRAEqn = eqn (ap2 TreeEq (ap1 (thmT trivCT) (var zero)) codeBotT)
                falseT

ConBRA : Formula
ConBRA = atomic conBRAEqn
```

Note: `conBRAEqn` has the same shape as our existing `conSentenceV3`
(Guard/ProvV3.agda / GodelIIV3.agda) but with `thmT trivCT` instead of
`thmT (reify cGSV3)`. This is deliberate — we work at the `Triv`-ambient
theory (sound per SOUNDNESS.md) rather than at the Gödel sentence's
own-theory (unsound per SOUNDNESS.md).

```agda
godelII_BRA :
  Consistent Triv ->
  Provable hyp_BRA (atomic conBRAEqn) ->        -- "ConBRA is provable"
  Empty
```

Here `hyp_BRA` is the Provable-level hypothesis. The most natural choice
is `hyp_BRA = atomic (eqn O O)` (the trivial Formula, atomic Triv), so
no actual extra Provable-level assumptions.

### The chain (from guard15.pdf page 17)

```
1) th(x) = j ⊃ th(Dth(x)) = "th(x) = j"            [Th 13]
2) th(Dsub(i, i)) = "sub(i, i) = j"                 [Th 13]
3) th(x) = j ⊃ th(gx) = "th(x) = sub(i, i)"         [1, 2]
4) th(x) = j ⊃ th(Y...) = "th(x) ≠ sub(i, i)"       [defn of j]
5) th(x) = j ⊃ th(combined) = "0 = 1"               [3, 4]
reductio: assume ConBRA provable; by substitution + 5,
  th(x) ≠ sub(i, i) would be provable, contradicting Gödel I.
```

### Open pieces

1. **Th 12-13 lift at Provable level**. Given a Provable equation
   `f(x) = y`, encode as `th(Df(x)) = "f(x) = y"`. Requires:
   - A `Df : Fun1 -> Term -> Term` combinator. Note: our existing
     `Guard/ProofEnc.agda` provides `encAxI`, `encAxFst`, ...,
     `encAxGoodstein` for each Deriv axiom. For a general functor `f`,
     the combinator is built case-by-case. Start with `f = I` (easy).
   - A helper
     ```
     thm13At : (f : Fun1) (x y : Term) {hyp : Formula} ->
               Provable hyp (atomic (eqn (ap1 f x) y)) ->
               Provable hyp (atomic (eqn (ap1 (thmT trivCT)
                                              (Df f x y))
                                         (reify (codeEqn
                                                   (eqn (ap1 f x) y)))))
     ```
   - Approach: use `thm14EV3 (axRefl (ap1 f x))` to get a Deriv, lift
     via `fromDeriv`, then rewrite using the input Provable + equality
     axioms (axEqCongL/R) to substitute y.
   - Key insight: the substitution "f(x) = y in codeEqn (eqn (ap1 f x)
     (ap1 f x))" is NOT a substitution at the term level — it's at the
     *encoded tree* level. The codeEqn's second slot is `reify (code
     (ap1 f x))`, a specific Term computed from f and x. We need
     `reify (code (ap1 f x)) ≡ reify (code y)` under the assumption
     `ap1 f x = y`.  This requires either:
       (a) A separate polymorphic-in-hyp lemma showing that codeEqn's
           second slot computes from f and x, so under the equation
           we can rewrite.
       (b) Using substOp (see Guard/SubstOp.agda) which handles coded
           substitution in the Deriv system.
     Recommend route (b): familiar pattern from our existing work.
   ~150-200 lines.

2. **Chain steps 1-5** at the Provable level, using Th 13 applications
   chained via `mp` and `deductionThm`. ~100-200 lines.

3. **Gödel II reductio**: bridge the Provable chain result to Gödel I
   via `godelIClassical`. The key meta-step is extracting a
   `Deriv Triv gsCR` from the Provable chain's conclusion, which
   requires either:
   - A `fromDerivImp` / `derivToProv` utility (see this session's
     earlier design discussions).
   - OR a direct meta-level pattern match on the specific Provable
     structure.
   ~80-150 lines.

**Total estimate: 400-600 lines, 1-2 sessions.**

### Design decisions to be revisited

- Whether to add `fromDerivImp` as a primitive Provable constructor
  (option i) or build `derivToProv` via `ruleSubP` + `ruleFP`
  (option ii). This session: deferred. See discussion in
  SOUNDNESS.md context and GUARD-BRA-TEMPLATE.md.

- Whether to formalize `ruleInst`'s side condition (Options A/B in
  SOUNDNESS.md) as a precursor or leave as audit-only. Cascading
  refactor if A; additive if B; C (current) ships current work.

## Command for next session

```
Read Guard/NEXT-SESSION-BRA-GODELII.md, Guard/SOUNDNESS.md, and the
godelII_BRA framework in Guard/GodelIIBRA.agda.  Also read
guard15.pdf pages 13-17 for the Gödel I/II proof details.

Goal: produce a closed inhabitant of
  ChainBRA = Provable (atomic Triv) (ConBRA imp atomic gsCR)
which closes godelII_BRA via provableGodelIBridge.

Approach: build the chain at the Deriv level (Route B), as
  chainDeriv : Deriv Triv conBRAEqn -> Deriv Triv gsCR
then derive ChainBRA via deductionThm + provExtractTriv + fromDeriv.

Two pieces of construction work:

  1. combined : Term -> Term
     A Term combinator that, given a candidate encoded proof X (with
     var 1 as the proof slot), produces an encoded proof of '0=1'.
     Built from ProofEnc combinators (encTrans, encSym, encCongL,
     encCongR, encInst, encRefl) wrapping the encoded godelIClassical
     body, with X at the input-proof leaf.  Use var 1 as the proof
     slot (NOT var 0) so treeEqSelf calls at the auxiliary hyp
     remain sound.

  2. combinedCorr : (X : Term) -> {h : Equation} ->
     Deriv h (eqn (TreeEq (thmT trivCT (combined X)) codeBotT)
                  (TreeEq (thmT trivCT X) (reify cGSCR)))
     The polymorphic equation linking thmT-images.  Proof: case-by-
     case reduction through thmT's validating cases (case19V3 trans,
     case18 sym, case21 congL, case22 congR, case23V3 ruleInst,
     case17 refl).  Each step uses pass-through lemmas in
     Guard/ThFunTForV3Pass.agda and Guard/StepReduce.agda.

Then:
  chainDeriv dCon = ...                                      -- ~50 lines
  godelII_BRA con dProv =
    con (godelIClassical (chainDeriv (provExtractTriv dProv)))

Conventions: --safe --without-K --exact-split, no postulates, no
holes.  Use ~/.cabal/bin/agda-2.9.0.  Commit after each of:
combined definition, combinedCorr proof, chainDeriv composition,
godelII_BRA closure.

Proceed autonomously.
```

## Session ledger

| # | Step | Status | Commit |
|---|---|---|---|
| 1 | Formula + Provable core | ✅ | `[bra-step1]` |
| 2 | Formula substitution | ✅ | `[bra-step2]`/`-fix` |
| 3 | provI + deductionThm | ✅ | `[bra-step3]` |
| 4-5 | Equality axioms + derived rules | ✅ | `[bra-step4-5]` |
| 6 | Audit ruleInst; SOUNDNESS.md | ✅ | `[doc]` |
| 7a | Provable→Deriv soundness (sem + provSound) | ✅ | `[bra-step6]` |
| 7b | ConBRA formula + substEq form | ✅ | `[bra-conbra]` |
| 7c | Meta Th 13 lift (provThm14E) | ✅ | `[bra-th13-meta]` |
| 7d | Reductio closure (provableGodelIBridge) | ✅ | `[bra-bridge]` |
| 7e | Parameterised godelII_BRA (ChainBRA hyp) | ✅ | `[bra-godelII-frame]` |
| 7f | Option A — sound ruleInst across the live core | ✅ | `[soundness-A]` x 5 |
| 8 | combined + combinedCorr (chain core) producing ChainBRA witness | ⏳ | — |

The 2026-04-21 session delivered the propositional layer and soundness
audit in 6 commits.  The 2026-04-22 session added the Provable→Deriv
bridge, ConBRA framing, meta-Th-13 lift, reductio closure step, and
the parameterised godelII_BRA framework in 5 commits, ~495 lines of
Agda + doc updates.  No postulates, no holes (one acknowledged
exact-split warning in deductionThm carries over).

The shape of the final theorem is now fully nailed down:

```agda
godelII_BRA :
  ChainBRA ->                                          -- step 8a-8b output
  Consistent Triv ->
  Provable (atomic Triv) (atomic conBRAEqn) -> Empty
godelII_BRA chain con dCon =
  provableGodelIBridge con (mp chain dCon)
```

The remaining work is exactly: produce a closed inhabitant of
`ChainBRA = Provable (atomic Triv) (ConBRA imp atomic gsCR)`.

## Strategy for the remaining chain

Two viable routes:

**Route A — Internal Provable chain (Guard 1963 transcription)**.
Build a Term combinator `Df : Fun1 -> Term -> Term -> Term` such that
`thmT(trivCT)(Df f x y) = reify(codeEqn(eqn (ap1 f x) y))` is provable
in Deriv given `eqn (ap1 f x) y`.  The construction uses substOp to
substitute `code y` for `code (ap1 f x)` inside the encoded axRefl
proof of `f(x) = f(x)`.  Then transcribe Guard 1963 chain steps 1-5
propositionally (using mp + axEqCong* + deductionThm).  Estimate:
~400-600 lines, 1-2 sessions.  Faithful transcription.

**Route B — Meta-level chain via provExtract**.  Build the chain at
the Deriv level as `chainDeriv : Deriv Triv conBRAEqn -> Deriv Triv gsCR`.
At the Deriv level, propositional implication is not directly available,
so the chain encodes `Pr(x, j) → Pr(combined x, '0=1')` via IfLf-
conditional terms.  Then godelII_BRA is:

```agda
godelII_BRA con dProv =
  con (godelIClassical (chainDeriv (provExtractTriv dProv)))
```

Estimate: similar size, but no abstract Df construction needed since
encoding machinery (thmT, ProofE3) is already at the Deriv level.

Either route closes the proof.  Route B is more concrete; Route A is
more faithful to Guard.

### Soundness pitfall RESOLVED (2026-04-22)

Earlier note: both routes need to apply `treeEqSelf` (or the diagonal
collapse) at an auxiliary hypothesis  hypAux = eqn (thmT trivCT (var 0))
(reify cGSCR) that has `var 0` free.  `treeEqSelf` internally uses
`ruleInst zero t treeEqSelfAll`, which is unsound when
`var 0 ∈ free(hyp)`.

**Now resolved by Option A**: `ruleInst` requires its side condition
explicitly, so any unsound application of `treeEqSelf` (or downstream
`combined`) at a hyp with var 0 free will fail to typecheck.  The
type system forces use of the var-1-shifted formulation.  No more
hand-tracking required.

In addition, `treeEqSelfReify : (t : Tree) -> Deriv hyp (TreeEq (reify t)
(reify t) = O)` (added during Option A) avoids `ruleInst` entirely for
the typical reify-of-tree case, so most chain uses of self-equality
discharge cleanly without any side condition at all.
