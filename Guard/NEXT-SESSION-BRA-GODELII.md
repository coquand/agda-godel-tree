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

### Conventions for the Route A chain

- **Proof slot** — the candidate-proof variable in both `conBRAEqn`
  and `gsCR` is `var zero` (= `x_0` in Guard's notation).  Every
  chain step's Provable hypothesis mentions `thmT trivCT (var zero)`
  in the LHS of its `atomic` equation.  There is no var-1 shift
  (that was a Route B workaround, now obsolete).

- **`j` = reified Gödel number of the sentence** — in our notation
  `j = reify cGSCR` (a closed Term).  Guard's "th(x) = j" is our
  `atomic (eqn (ap1 (thmT trivCT) (var zero)) (reify cGSCR))`.

- **`sub(i, i)` = the diagonal target** — in our notation, the Term
  `rhsT = ap2 substOp (ap2 Pair (ap1 cor (reify templateCodeCR))
                                (reify (natCode v1)))
                      (reify templateCodeCR)` that reduces to
  `reify cGSCR` via `diagFTargetCR`.  (So `j` and `sub(i, i)` are
  provably equal as closed Terms, matching Guard's step 1'.)

### Open pieces (Route A work items)

1. **`Df : Fun1 -> Term -> Term -> Term`** — Guard's Th 12.
   For each `f : Fun1`, `Df f x y` is a closed Term representing an
   encoded proof tree that validates the equation `ap1 f x = y` once
   given the hypothesis `ap1 f x = y` at the Provable level.

   Sketch for `f = I`:
   ```
   Df I x y = encCongR I (reify (code (ap1 I x))) (encAxI (reify (code x)))
              -- or similar; spell out concretely during implementation.
   ```
   Rationale: `encAxI (reify (code x))` is the encoded proof of
   `I x = x` (always valid under any hyp).  Wrapping it via a congR
   step inside the target codeEqn's RHS slot lets us, under the
   extra Provable hypothesis `I x = y`, rewrite the encoded RHS to
   reach `codeEqn (eqn (I x) y)`.

   Other Fun1 cases (`Fst`, `Snd`, `Comp f g`, `Comp2 h f g`, `Rec z s`,
   `KT t`) are mechanical variants, each using its matching
   `encAx*` encoder from `Guard/ProofEnc.agda`.  The binary-functor
   analogue `DfF2 : Fun2 -> Term -> Term -> Term -> Term` follows
   the same pattern on `encAxFst`, `encAxSnd`, ..., `encAxTreeEq*`.

   ~150-200 lines.

2. **`thm13At`** — the Provable-level Th 13 lift.
   ```agda
   thm13At : (f : Fun1) (x y : Term) {hyp : Formula} ->
             Provable hyp (atomic (eqn (ap1 f x) y)) ->
             Provable hyp (atomic
               (eqn (ap1 (thmT trivCT) (Df f x y))
                    (reify (codeEqn (eqn (ap1 f x) y)))))
   ```
   Proof: `fromDeriv` on `Df f x y`'s unconditional Deriv witness at
   the `f(x) = f(x)` level (built via `thm14EV3 (axRefl (ap1 f x))`
   + encCongR), then rewrite the encoded-RHS slot using the Provable
   hypothesis `ap1 f x = y` via `axEqCongR` on the reified codeEqn.
   The coded substitution is handled by `substOpCorrect`
   (Guard/SubstOp.agda), which is the familiar pattern from
   GodelIClassical's `diagFTargetCR`.

   ~80 lines.

3. **Chain steps 1-5 at the Provable layer** (guard15.pdf p.17).

   - **Step 1**: `th(x) = j ⊃ th(Dth(x)) = "th(x) = j"`.
     Apply `thm13At` with `f = thmT trivCT`, `x = var zero`, `y = reify cGSCR`;
     discharge the hypothesis via `deductionThm` to get a Provable
     implication.

   - **Step 2**: `th(Dsub(i, i)) = "sub(i, i) = j"`.
     Closed-form application of `thm13At` — no hypothesis to
     discharge since `sub(i, i) = reify cGSCR = j` is provable as a
     closed Deriv (use `diagFTargetCR`).

   - **Step 3**: combine 1 and 2 via `axEqCongR` (rewrite `j` for
     `th(x)` inside step 2's RHS) + `hypSyll'` to chain
     implications.  Produces
     `th(x) = j ⊃ th(gx) = "th(x) = sub(i, i)"`.

   - **Step 4**: from the definition of `j`, derive
     `th(x) = j ⊃ th(Y...) = "th(x) ≠ sub(i, i)"` — purely
     equational (`j`'s structure as a reified codeEqn is known), no
     new Df applications needed.

   - **Step 5**: `th(x) = j ⊃ th(combined) = "0 = 1"` — compose
     step 3 and step 4 using the encoded `mp` encoder in ProofEnc
     (`encMp` if present, else built from `encTrans` + `encCong*`).
     `combined` is the Term corresponding to Guard's
     `4J[4J(J(num x,1),x)+1, 4J(gx,hx)+2]+2` — i.e., a specific
     ProofEnc-built encoded proof term; its exact form is pinned
     down by step 5's Provable-level derivation.

   ~100-150 lines.

4. **Closure to ChainBRA**.

   Given step 5:
   ```agda
   step5 : {hyp : Formula} ->
     Provable hyp (atomic (eqn (ap1 (thmT trivCT) (var zero))
                               (reify cGSCR))
                   imp
                   atomic (eqn (ap1 (thmT trivCT) combined) codeBotT))
   ```

   From `dCon : Provable (atomic Triv) (atomic conBRAEqn)`, instantiate
   `conBRAEqn`'s `var zero` slot at `combined` using (formula-level)
   `substF zero combined` to get
   `Provable (atomic Triv) (atomic (eqn (ap2 TreeEq (ap1 (thmT trivCT) combined) codeBotT) falseT))`.
   This is `combined is not a proof of 0=1`.

   Step 5's contrapositive (using `axNeg`, `mp`) on the negation of
   `th(combined) = 0=1` yields the negation of `th(x) = j`, which —
   after the `rhsT = reify cGSCR` rewrite via `diagFTargetCR` and
   some `axEq*` massage to arrive at `gsCR`'s shape — gives
   ```agda
   chainBRAClosure : Provable (atomic Triv) (ConBRA imp atomic gsCR)
   ```
   i.e., the target `ChainBRA`.

   `godelII_BRA chainBRAClosure` is then the completed Gödel II.

   ~80 lines.

**Total estimate: 400-550 lines, 1-2 sessions.  Dominated by Df's
per-functor cases in step 1.**

### Design decision (retired)

Earlier drafts of this handoff kept an open question about whether
`fromDerivImp` / `derivToProv` needed to be added as a primitive
Provable constructor or derived.  **Route A does not need either**:
the closure feeds `mp chain dCon : Provable (atomic Triv) (atomic gsCR)`
directly into the already-built `provableGodelIBridge`, which
extracts a `Deriv Triv gsCR` via the existing `provExtract`
machinery.  No new primitive is required.

## Command for next session

```
Read Guard/NEXT-SESSION-BRA-GODELII.md, Guard/SOUNDNESS.md, the
godelII_BRA framework in Guard/GodelIIBRA.agda, and
Guard/ChainPrototype.agda (which documents why Route B was shelved).
Also read guard15.pdf pages 13-17 for the Gödel I/II proof details,
paying particular attention to Th 12 / Th 13 / Th 14 on pages 16-17
and Exercise 24 [2]-[4] on page 14 (the sbt / sbf / sb functors).

Goal: produce a closed inhabitant of
  ChainBRA = Provable (atomic Triv) (ConBRA imp atomic gsCR)
which closes godelII_BRA via provableGodelIBridge.

Approach: Route A — faithful Guard-1963 transcription at the
Provable layer.  Route B is ruled out (see handoff).  The chain
(guard15.pdf p.17, steps 1-5) is built step-by-step as Provable
implications using mp + axEqCong* + deductionThm; `thmT` is only
applied to concrete closed equations, never to an abstract
candidate proof.

Concrete work breakdown is in the "Open pieces (Route A work
items)" section of this handoff — read it first.  TL;DR, in order
(commit after each):

  1. Df combinator (f = I first, then Fst/Snd/Comp/Comp2/Rec/KT;
     binary analogue DfF2 on Fun2 in parallel).  ~150-200 lines.

  2. thm13At (Provable-layer Th 13 lift).  ~80 lines.

  3. Chain steps 1-5 (guard15.pdf p.17), each as a Provable
     implication chained via hypSyll' + mp + axEqCong* +
     deductionThm.  ~100-150 lines.

  4. ChainBRA closure: contrapositive-and-substitute into dCon,
     reshape to match gsCR via diagFTargetCR + axEq*, feed into
     the already-complete provableGodelIBridge.  ~80 lines.

Conventions already established:
  - Proof slot = var zero (NOT var 1).  The var-1 shift was a Route
    B workaround; it is obsolete under Route A because no
    treeEqSelf side-condition is at risk.
  - j = reify cGSCR.
  - sub(i, i) = rhsT (the substOp diagonal from GodelIClassical).
  - trivCT, codeBotT, trivClosed, diagFTargetCR, treeEqSelfReify
    are all in scope and reusable.

--safe --without-K --exact-split, no postulates, no holes.  Use
~/.cabal/bin/agda-2.9.0.  Commit prefix: [bra-routeA].  Estimated
total: 400-550 lines, 1-2 sessions.

Starting pointer: begin with Df I in a new Guard/RouteADf.agda.
Draft the signature exactly as in "Open pieces" item 1.  Build
Df I x y from encAxI + encCongR and verify its thmT-reduces-to-
codeEqn lemma polymorphically in hyp (pure Deriv, no Provable yet).
That shakes out the pattern for the other Fun1 cases before any
Provable layer is touched.

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
| 7g | Prototype encInst reduction — Route B ruled out | ✅ | `[bra-prototype]` |
| 7h | Route A chosen, Route B shelved (handoff rewrite) | ✅ | `[bra-routeA-plan]` |
| 8a | Df : Fun1 -> Term -> Term -> Term (Guard Th 12) | ⏳ | — |
| 8b | thm13At lift at Provable layer | ⏳ | — |
| 8c | Chain steps 1-5 transcription (guard15.pdf p.17) | ⏳ | — |
| 8d | ChainBRA witness + godelII_BRA closure | ⏳ | — |

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

**Decision (2026-04-22): Route A — Guard-1963 Provable-layer
transcription.**  Route B (Deriv-level chain via `chainDeriv`) has been
ruled out after the `ChainPrototype` de-risk step exposed an
unworkable obstruction on abstract sub-proofs (see
"Prototype result" and "Why Route B was shelved" below).

### Route A — Internal Provable chain (Guard 1963 transcription)

Transcribes Guard 1963 Th 14 propositionally at our `Provable` layer:

```
1) th(x) = j  ⊃  th(Dth(x)) = "th(x) = j"            [Th 13]
2) th(Dsub(i, i)) = "sub(i, i) = j"                   [Th 13]
3) th(x) = j  ⊃  th(gx) = "th(x) = sub(i, i)"         [1, 2]
4) th(x) = j  ⊃  th(Y...) = "th(x) ≠ sub(i, i)"       [defn of j]
5) th(x) = j  ⊃  th(combined) = "0 = 1"               [3, 4]
reductio: assume ConBRA provable; by substitution + 5,
  th(x) ≠ sub(i, i) would be provable, contradicting Gödel I.
```

At our Provable layer, `⊃` is the `imp` connective and each step is a
`Provable hyp (... imp ...)` lemma chained via `mp`, the equality
axioms (`axEqCongL/R/Trans`), and discharged via `deductionThm`.

The "Open pieces" section below spells out the concrete Agda work
(Df combinator, `thm13At` lift, chain steps 1-5).

### Why Route A sidesteps the abstract-X obstruction

Route B's failure was that the thmT validator must reduce on an
abstract sub-proof `X` (via `encRuleInstCorr` and friends) to close
the chain at the Deriv level.  Validator reductions stall on abstract
Terms — there is no syntactic shape for `guardNdV3` / `guardLfV3` to
dispatch on.

Route A never applies `thmT` to an abstract sub-proof.  The
hypothetical "x encodes gsCR" lives as a **Provable hypothesis**
`Provable hyp (atomic (th(x) = j))`, not as a Term needing
validation.  Under this hypothesis, `axEqCongL/R` rewrites `th(x)` to
`j` inside other equations — pure propositional reasoning, no
validator unfolding.  Th 13 is only applied to concrete closed
equations (axioms like `axRefl (ap1 f x)`), whose encodings are
fully concrete and reduce cleanly — the regime that already works.

### Why Route B was shelved

`Guard/ChainPrototype.agda` typechecks its Pair-structured form
(`protoInstRed`) via `encRuleInstCorr`:

```agda
protoInstRed :
  (paR pbR lC r'C : Term) ->
  (subCorr : {h : Equation} ->
    Deriv h (eqn (ap1 (thmT trivCT) (ap2 Pair paR pbR)) (ap2 Pair lC r'C))) ->
  Deriv hyp (eqn (ap1 (thmT trivCT) (encRuleInst aR (ap2 Pair paR pbR)))
                 (ap2 Pair (ap2 substOp aR lC) (ap2 substOp aR r'C)))
```

but *not* for a fully abstract `X : Term`.  The inner Rec-unfolding of
`thmT trivCT (Pair aR X)` reaches a `thmTStep` whose
`IfLf(TreeEq (Snd orig) O, ..., ..)` guard does not reduce:
`Snd (Pair aR X) = X` is abstract, so neither `guardNdV3` (needs
`X = Pair x y`) nor `guardLfV3` (needs `X = O`) applies.

Consequence: `combinedCorr`, stated polymorphically in an arbitrary
`X`, is not provable via the godelIClassical-style encoded-proof
chain.  The Route B redesigns R1/R2/R3 (variable-schema rework, raw
`IfLf` `combined`, narrowed statement) would each introduce either
speculative obstructions or structural churn in load-bearing code
like `godelIClassical`.  Route A avoids all of this.

See `Guard/ChainPrototype.agda` for the full prototype (~170 lines,
no holes, no postulates) and the explicit reduction trace that
documents where the IfLf thicket appears.

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
