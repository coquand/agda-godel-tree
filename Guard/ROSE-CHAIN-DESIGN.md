# Rose-chain design memo: closing godelIIClassicalTriv

## Goal

```agda
godelIIClassicalTriv :
  Consistent Triv ->
  Deriv Triv ConTrivRose ->
  Empty
```

Via the reduction in `Guard/GodelIIClassicalTriv.agda`:

```agda
godelIIClassicalTrivWithCore :
  StepFCoreType ->                        -- the one open premise
  Consistent Triv -> Deriv Triv ConTrivRose -> Empty
```

where

```agda
StepFCoreType =
  Deriv Triv
    (eqn (ap2 TreeEq (ap1 (thmT trivCT) (ap2 Pair (var 0) (var 1)))
                      diagBody)
         poo)
```

This memo analyzes why the naive Rose/Ryan chain via `dAux` + `roseLemma1T`
+ direct `dCon`-instantiation DOES NOT close the chain, and lays out what
is actually needed.

## Inventory of what is true

### 1. dAux is constructible

Under the hypothesis `H_enc = (thmT trivCT (Pair v0 v1) = reify cGSCR)`,
we have

```agda
dAux : Deriv H_enc B_aux
  where B_aux = eqn (TreeEq (thmT trivCT (Pair v0 v1)) diagBody) O
```

via `congL TreeEq diagBody (ruleHyp{H_enc})` + `diagFTargetCR` +
`treeEqSelf`. Semantically: if Pair v0 v1 encodes gsCR, then the TreeEq
evaluates to O.

### 2. roseLemma1T encodes dAux

```agda
dAuxEncoded : ... -> Lemma1T H_enc B_aux
```

produces `V : Term` and `vCorr : thmT trivCT V = reify (codeEqn B_aux)`.

### 3. dCon instantiates

```agda
dCon : Deriv Triv ConTrivRose
     = Deriv Triv (impT (TreeEq (thmT trivCT (var 0)) codeBotT) falseT = trueT)
```

At `var 0 := V` via `ruleInst`:

```agda
dConAtV : Deriv Triv (impT (TreeEq (thmT trivCT V) codeBotT) falseT = trueT)
```

## Why the naive chain fails

Compose (1)-(3): `thmT trivCT V = reify (codeEqn B_aux)` (from vCorr).

Substitute into dConAtV:

```
impT (TreeEq (reify (codeEqn B_aux)) codeBotT) falseT = trueT
```

The antecedent is `TreeEq (reify (codeEqn B_aux)) codeBotT`. These are
two SPECIFIC trees:

- `reify (codeEqn B_aux)` has shape `ap2 Pair (reify codeOfLHS)
  (reify codeOfO)` where LHS = the TreeEq-of-Pair expression.
- `codeBotT = reify (codeEqn (eqn trueT falseT)) = reify (codeEqn (eqn
  O poo))` has shape `ap2 Pair (reify codeOfO) (reify codeOfPoo)`.

Since these are DISTINCT closed trees (the first slot differs:
`codeOfLHS` vs `codeOfO`), TreeEq between them structurally evaluates to
`poo` (via recursive `axTreeEqNN` + eventual `axTreeEqNL`). Thus:

```
impT poo falseT = trueT           (by impTFalseAnt)
```

which is the vacuous case of impT. **No contradiction: dConAtV is
satisfied, but it tells us nothing useful.**

To get a useful contradiction, we need the ANTECEDENT to evaluate to
`trueT = O`, not `poo`. This requires V such that `thmT trivCT V =
codeBotT` — i.e., V encodes a proof of bot, not of B_aux.

## What Rose actually does (papers)

### Rose 1967, Theorem 18 ("Godel II")

Rose's consistency statement is NOT "no x proves bot". It is:

```
Con_Rose : th(y) != e(th(z))                    -- no theorem is the e-negation of any theorem
```

Parametric over BOTH y and z. Here e is a PR function sending the code
of `A = B` to the code of `A != B`.

Rose's proof of Thm 18 (p.133):

1. Assume BOTH `⊢ Con_Rose` (consistency provable) AND `⊢ th(y) =
   se(nu(N), N)` (Gödel sentence G has a proof, indexed y).
2. Instantiate Con_Rose at x := X where th(X) = [se(nu(N), N) != th(0)]:
   derive `th(z) != [se(nu(N), N) = th(0)]`.
3. From premise (2) + Thm 17 (fixed-point): `e(th(z)) != [se(nu(N), N)
   != th(sy)]`, hence `th(z) != [se(nu(N), N) = th(sy)]`.
4. Apply Thm 16 to f(y) = a(se(nu(N), N), th(y)): `a(se(nu(N), N),
   th(y)) != 0` ⟺ `se(nu(N), N) != th(y)` for all y.
5. But this IS the Gödel sentence, so `⊢ G`. Combined with (1) via Thm
   17, derive contradiction.

**Key observation**: step 2 uses `e` to TOGGLE the form of an equation
between `A=B` and `A!=B`. The consistency statement's parametricity in
z is ALSO crucial: different instantiations serve different roles.

### Ryan 1978, Main Theorem

Same structure as Rose, slightly cleaner. Uses the same `epsilon(x)`
function and the same two-parameter consistency.

## Why our ConTrivRose is not directly adequate

Our ConTrivRose is SINGLE-PARAMETER (only var 0), and uses
`codeBotT` (a specific term) rather than `e(th(var 1))` (a functional
expression).

This is classically equivalent IF we also have a derivation
`e(th(x_1))-is-equivalent-to-negation-encoded` machinery. But AS
AN OBJECT-LEVEL EQUATION, it is strictly weaker than Rose's.

In particular: Rose's chain derives `th(z) != [se(nu(N), N) = th(y)]`
by substituting a specific `X` with `th(X) = [se(nu(N), N) != th(0)]`.
This substitution relies on x being a FREE variable in Con_Rose. With
only `codeBotT` in place of `e(th(x_1))`, this step is unavailable.

## Options for closing godelIIClassicalTriv

### Option α: Strengthen ConTrivRose to Rose's form

```agda
eT : Fun1                                    -- the e-function as a primitive
eT = ...                                     -- constructed via Rec + tag dispatch

ConTrivRose_Strong : Equation
ConTrivRose_Strong = eqn
  (impT (ap2 TreeEq (ap1 (thmT trivCT) (var zero))
                    (ap1 eT (ap1 (thmT trivCT) (var (suc zero)))))
        falseT)
  trueT
```

Pros: Rose's chain directly transcribes.
Cons:
- Requires defining `eT` as a `Fun1` (primitive-recursive combinator).
- Requires proving `eT`-correctness: `eT (reify (codeEqn (eqn A B))) =
  reify (codeEqn (eqn (ap2 TreeEq A B) falseT))` for all A, B.
- Requires reproving the Schema-F ingredients baseF/stepG/baseG for the
  new ConTrivRose_Strong.
- ConTrivRose_Strong still needs to be shown EQUIVALENT to / stronger
  than ConTrivRose (the classical connection).

Estimated: 500-800 lines.

### Option β: Internal derivation of bot under H_enc + dCon

Idea: construct `dBot : Deriv (Triv + H_enc-as-extra-hypothesis) bot`
using `dCon` internally. Then apply `roseLemma1T` to `dBot` to get V
with `thmT trivCT V = codeBotT`, closing the chain.

Obstacles:
1. `dCon : Deriv Triv ConTrivRose` is tied to hyp = Triv. roseLemma1T
   requires `Deriv H B` for some single-hypothesis H. We can't directly
   splice dCon into a `Deriv H_enc B` derivation.
2. Workaround: Generalize `roseLemma1T` to handle TWO hypotheses
   (Ryan's n=2 case). Then we can apply it to `Deriv (Triv ∧ H_enc)
   bot`.
3. Even with n=2 Lemma 1, we need `Deriv (Triv ∧ H_enc) bot`. Can we
   construct this?

Attempting the construction: under Triv and H_enc simultaneously,
- dAux gives B_aux under H_enc (and trivially under Triv's ambient
  axioms).
- dCon gives ConTrivRose under Triv (parametric in var 0).
- We want: O = poo (bot).

From B_aux: `TreeEq TP diagBody = O`.
From H_enc: `TP = reify cGSCR`.
So `TreeEq (reify cGSCR) diagBody = O`, and diagBody = reify cGSCR, so
`TreeEq (reify cGSCR) (reify cGSCR) = O` — which is just treeEqSelf,
not a contradiction.

To derive bot directly under H_enc ∧ Triv, we need OBJECT-LEVEL
instantiation of dCon at a specific V' with thmT trivCT V' = codeBotT.
But V' is what we're trying to construct via Lemma 1.

This is circular. Option β does NOT close without additional machinery.

### Option γ: Construct V directly (non-Lemma-1 encoder)

Build a CONCRETE `V_bot : Term` (with v0, v1 free) such that:

```agda
vBotCorr : Deriv H_enc (eqn (ap1 (thmT trivCT) V_bot) codeBotT)
```

That is: under H_enc, V_bot is a proof-code of bot.

This requires: V_bot's image under thmT trivCT, when H_enc holds, equals
codeBotT. 

To construct such V_bot: we need to assemble an object-level encoding
of the DERIVATION showing bot from H_enc. The derivation uses dAux +
some additional step that produces bot.

But under H_enc alone, bot is NOT derivable (H_enc is satisfiable; it
holds for NO actual Term, but the hypothetical Deriv system allows it
as a consistency-test). So Deriv H_enc bot is empty.

To fix: add dCon to the picture as an AXIOM, not a hyp. Since dCon is
a `Deriv Triv ...`, we can unfold it INSIDE our Deriv H_enc chain
IFF Triv's axioms are subsumed by H_enc's (they're not).

Option γ also requires the n=2 Lemma 1 upgrade.

### Option δ: Modify Deriv to allow multi-hypothesis

Extend `Deriv` to take a LIST of hypotheses. Then `Deriv [Triv,
H_enc] bot` becomes expressible, and multi-hypothesis Lemma 1 kicks in.

Major refactor. Not recommended at this stage.

## Recommended path forward

**Option α variant**: implement the `eT` function and its correctness
only (no strengthening of ConTrivRose). Use `eT` at the TERM level to
construct V_bot from V_Baux:

1. Take V with `thmT trivCT V = reify (codeEqn B_aux)` (from dAuxEncoded).
2. Build `V_enc := ap1 eT-as-term V`  (where eT-as-term is a specific
   Term representation of `eT`).
3. Show `thmT trivCT V_enc = reify (codeEqn (eqn (TreeEq LHS O)
   falseT))`.

where LHS = TreeEq(thmT trivCT (Pair v0 v1)) diagBody.

Now `codeEqn (eqn (TreeEq LHS O) falseT)` is the code of the equation
"TreeEq LHS O = falseT", which is the E-NEGATION of B_aux.

Under H_enc: TreeEq LHS O = TreeEq O O = O = trueT (NOT falseT). So
this equation is FALSE under H_enc, meaning `V_enc` encodes a proof of
a FALSE equation. Does this contradict dCon?

dCon says no proof-code for codeBotT. V_enc's code is NOT codeBotT
(it's `codeEqn (eqn (TreeEq LHS O) falseT)`). So dCon at V_enc doesn't
directly fire.

**The underlying problem**: dCon is specific to codeBotT, not general
over all false equations. To close the chain, we need dCon to rule out
proof-codes for ANY provably-false equation.

This requires MORE FIRST-PRINCIPLES CONSISTENCY (omega-consistency, or
"no theorem is falsifiable by the standard model"), which is stronger
than bare "no proof of 0=1".

## Summary

Our ConTrivRose (using `codeBotT`) is **STRICTLY WEAKER** than the
Rose/Ryan consistency statement (which uses `e(th(var 1))` and is
parametric in two free variables). Rose's chain for Thm 18 depends
crucially on the two-parameter form and the e-negation structure.

### Action items (prioritised)

1. **Decide whether to upgrade ConTrivRose** to the two-parameter
   e-negation form. This enables Rose's chain to transcribe directly,
   at cost of ~500-800 lines of new infrastructure (eT combinator, its
   correctness, new Schema-F premises).

2. If upgrading: order of work:
   a. Define `eT : Fun1` via Rec + dispatch on Pair-shape.
   b. Prove `eT (reify (codeEqn (eqn A B))) = reify (codeEqn (eqn (ap2
      TreeEq A B) falseT))` parametric in A, B.
   c. Prove dCon instantiated at appropriately-chosen V (using eT) gives
      bot under H_enc.
   d. Re-derive baseF / stepG / baseG / stepF for the new ConTrivRose.

3. If NOT upgrading: revisit whether `godelIIClassicalTriv` is even the
   right target statement. Perhaps the target should be
   `godelIIClassicalTrivRose : Consistent Triv -> Deriv Triv
   ConTrivRose_Strong -> Empty`, and the transition from
   ConTrivRose_Strong to our weaker ConTrivRose is left as a separate
   conditional equivalence (which it isn't, in general).

4. Alternative target: prove `Deriv Triv ConTrivRose_Strong -> Deriv
   Triv ConTrivRose` (if true, this gives a stronger-to-weaker
   reduction and lets the Rose chain apply to the stronger form, from
   which the weaker follows).

## Estimated effort

- Option α full: 500-800 lines, 3-5 sessions.
- Option β (requires Lemma-1 n=2 upgrade): 300-500 lines, 2-3 sessions.
- Documentation only (this memo): done.

## What is NOT needed

The `Guard/RoseEncE.agda` module's `eTree` + `eTerm` are META-LEVEL
code-manipulation functions; they operate on Trees/Terms at the
meta-level. To apply Rose's chain we need:

- `eT : Fun1` that lives INSIDE the Agda-level Term grammar (not a
  meta-function). This is a PRIMITIVE-RECURSIVE combinator definable
  via Rec + primitives.
- `eTCorrect` proved at the Deriv level (not just as an Agda Eq).

These are the missing pieces. `RoseEncE.agda`'s eTree is the
meta-level SPEC to match, not the implementation.

## Next concrete session

1. Define `eT : Fun1` in a new module `Guard/RoseEFun.agda`.
2. Prove `eTFunCorrect : Deriv hyp (eqn (ap1 eT (reify (codeEqn (eqn A
   B)))) (reify (codeEqn (eqn (ap2 TreeEq A B) falseT))))` for
   arbitrary A, B.
3. Define `ConTrivRose_Strong` in `Guard/GodelIIClassicalTrivStrong.agda`.
4. Transcribe Rose's Thm 18 chain using eT and the two-parameter
   consistency.
