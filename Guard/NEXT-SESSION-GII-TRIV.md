# Next Session: close godelIIClassicalTriv

## Command

From `/Users/coquand/CHWISTEK`:

```
claude
```

Then paste:

```
Read Guard/NEXT-SESSION-GII-TRIV.md for full context, then proceed.

Goal: close  godelIIClassicalTriv : Consistent Triv ->
                                    Deriv Triv ConTrivRose ->
                                    Empty
by upgrading ConTrivRose to the two-parameter e-negation form and
completing the Rose/Ryan Theorem 4 / Theorem 18 chain.

Infrastructure delivered as of 2026-04-21 (main):
  * Guard/RoseLemma1T.agda          Ryan-style Lemma 1 over thmT trivCT.
  * Guard/GodelIIClassicalTriv.agda Schema F reduction; dAux + dNegGsRose
                                    constructed and encoded via Lemma1T.
  * Guard/ImpT.agda  +  Guard/ImpTProp.agda   object-level impT toolkit.
  * Guard/RoseEncE.agda             e-Tree meta-level spec.
  * Guard/RoseEFun.agda             eT : Fun1 object-level e-function,
                                    with eTCorrect under any hyp.
  * Guard/ROSE-CHAIN-DESIGN.md      design memo: why naive chain fails,
                                    3 options surveyed, alpha recommended.

Conventions: --safe --without-K --exact-split, no postulates, no holes.
Use ~/.cabal/bin/agda-2.9.0 (NOT /opt/homebrew/bin/agda).
Commit after each major piece.

Read ROSE-CHAIN-DESIGN.md first -- it explains the core design issue
(our ConTrivRose uses codeBotT; Rose/Ryan's Thm 18 needs the e-negation
form) and lays out option alpha (the recommended path).

Proceed autonomously.
```

## What's done (committed on main)

Eight commits as of 2026-04-21:

```
93e0f31  [rose-efun] Introduce eT Fun1 combinator + design memo
742a059  [doc] NEXT-SESSION-GII-TRIV.md: handoff for Rose-chain closure
26b7a92  [doc] RoseChainAnalysis: option (i) executed, remaining chain laid out
21da0a1  [gii-triv] Integrate RoseLemma1T and exhibit constructible dAux
7ff35eb  [rose-l1t] RoseLemma1T: Ryan-style Lemma 1 over thmT trivCT
08a8b3a  [doc] RoseChainAnalysis: session update on Guard/GodelIIClassicalTriv
c8dc3ad  [gii-triv] Factor step-F premise through TreeEq-core form
f39c293  [gii-triv] GodelIIClassicalTriv: infrastructure for Schema F approach
```

Plus this session (2026-04-21):

```
3085f58  [gii-triv] dNegGsRose: Rose-style e-negation of gsCR at Pair v0 v1
93e0f31  [rose-efun] Introduce eT Fun1 combinator + design memo
```

Key artifacts (updated):

**`Guard/RoseEFun.agda`** (168 lines, 0.04s, no postulates):
  * `eT : Fun1` -- the object-level e-function, built from Comp2 Pair,
    KT, I primitives.
  * `eTReduces` -- Deriv-level reduction of `ap1 eT x` to its expanded
    Pair form, polymorphic in hyp.
  * `eTCorrect A B` -- Deriv-level: `ap1 eT (reify (codeEqn (eqn A B)))
    = reify (codeEqn (eqn (ap2 TreeEq A B) falseT))` for any A, B.

**`Guard/GodelIIClassicalTriv.agda`** (additions this session):
  * `B_negGs` + `dNegGsRose` : Deriv H_enc (Rose-style e-negation of
    gsCR at Pair v0 v1).
  * `dNegGsRoseEncoded` : roseLemma1T dNegGsRose produces V' whose
    `thmT trivCT V' = reify (codeEqn B_negGs)`.

**`Guard/ROSE-CHAIN-DESIGN.md`** (252 lines): complete analysis of why
our ConTrivRose is strictly weaker than Rose/Ryan's, and the three
options surveyed (alpha = strengthen, beta = internal bot, gamma =
direct V).  Recommends option alpha.

## The core design issue

Our `ConTrivRose`:
```agda
ConTrivRose = eqn
  (impT (ap2 TreeEq (ap1 (thmT trivCT) (var zero)) codeBotT) falseT)
  trueT
```

Rose (1967) / Ryan (1978) Thm 18 (Main Theorem) consistency:
```
Con_Rose = th(x) != e(th(z))     -- parametric in BOTH x and z
```

Rose's proof of Thm 18 critically uses:
(a) TWO free variables in the consistency statement (x and z).
(b) The e-negation function: "if y = code(A=B), then e(y) = code(A!=B)".

With only `codeBotT` (a specific constant) in place of `e(th(var 1))`,
Rose's chain cannot be transcribed -- specifically, the instantiation
step 2 of his proof (p.133) requires substituting an X with `th(X) =
[se(nu(N), N) != th(0)]`, which is only possible when the target is
parametric.

**Recommendation (option alpha)**: upgrade ConTrivRose to the
two-parameter e-negation form.

## Concrete plan -- pick up here

### Step A: define ConTrivRose_Strong

```agda
ConTrivRose_Strong : Equation
ConTrivRose_Strong = eqn
  (impT (ap2 TreeEq (ap1 (thmT trivCT) (var zero))
                    (ap1 eT (ap1 (thmT trivCT) (var (suc zero)))))
        falseT)
  trueT
```

Reads: "For all x, z: thmT trivCT x != eT (thmT trivCT z)."  i.e., "no
theorem-index's image is the e-negation of any theorem-index's image."

**File**: new module `Guard/GodelIIClassicalTrivStrong.agda`.

### Step B: Rose's Thm 18 chain

Given `dConStrong : Deriv Triv ConTrivRose_Strong`:

1. Under H_enc, encode dNegGsRose via roseLemma1T: get V' with
   `thmT trivCT V' = reify (codeEqn B_negGs)`.
2. Separately, build a V that encodes "Pair v0 v1 encodes gsCR at
   instance Pair v0 v1" -- the trivial encoder (via ruleHyp{H_enc}
   itself encoded via Lemma1T from ruleHyp).
3. Instantiate dConStrong at (var 0 := V', var 1 := V):
     impT (TreeEq (thmT trivCT V') (ap1 eT (thmT trivCT V))) falseT = trueT.
4. Under H_enc:
   - `thmT trivCT V = reify cGSCR` (from H_enc + ruleHyp's encoding).
   - `ap1 eT (reify cGSCR)` reduces via eTReduces to
     `reify (eTree cGSCR)` (meta-level match with codeEqn B_negGs).
   - `thmT trivCT V' = reify (codeEqn B_negGs)`.
   - If  `codeEqn B_negGs = eTree cGSCR`  (!), then
     TreeEq (reify (codeEqn B_negGs)) (reify (eTree cGSCR)) = O
     (by treeEqSelf after congR).
5. From (*) impT O falseT = trueT gives falseT = trueT (bot under
   H_enc).
6. Apply Lemma1T to this bot-under-H_enc derivation: get V_bot with
   `thmT trivCT V_bot = codeBotT`.
7. Plug V_bot into dCon (the ORIGINAL ConTrivRose, derivable from
   ConTrivRose_Strong at a specific choice of var 1): derive bot
   under Triv.
8. `gsFromCon` then closes via Schema F (StepFCoreType).

### Crucial check: codeEqn B_negGs vs eTree cGSCR

Need to verify:
```
codeEqn B_negGs  =?=  eTree (codeEqn (gsCR[var 0 := Pair v0 v1]))
```

B_negGs = eqn (ap2 TreeEq (ap2 TreeEq TP diagBody) poo) (ap2 Pair O O).
  codeEqn B_negGs = nd (code (ap2 TreeEq (ap2 TreeEq TP diagBody) poo))
                      (code (ap2 Pair O O))

gsCR[var 0 := Pair v0 v1] = eqn (ap2 TreeEq TP diagBody) poo.
  codeEqn that           = nd (code (ap2 TreeEq TP diagBody))
                              (code poo)

eTree(that) = nd (nd tagAp2 (nd (codeF2 TreeEq)
                                 (nd (code (ap2 TreeEq TP diagBody))
                                     (code poo))))
                 codeFalse

To match codeEqn B_negGs:
  nd (code (ap2 TreeEq (ap2 TreeEq TP diagBody) poo)) (code (ap2 Pair O O))
= nd (nd tagAp2 (nd (codeF2 TreeEq) (nd (code (ap2 TreeEq TP diagBody))
                                        (code poo))))
     (code falseT)                [since poo = falseT and code poo = code falseT]

And codeFalse = code falseT.  So these DO match definitionally.
The meta-equation is refl (after unfolding codeFalse = code falseT).

### Size estimate

- Step A: 30 lines.
- Step B chain: 150-250 lines of Deriv-level assembly.
- Rebuild baseF/stepG/baseG for ConTrivRose_Strong (if we keep Schema F):
  mostly mechanical, 50-100 lines.
- Link ConTrivRose_Strong -> ConTrivRose (classical equivalence) if
  keeping the original theorem statement: 50-100 lines.

Total: 300-500 lines.

## Alternative simpler target

If the full strong form is too ambitious, an intermediate deliverable
is:

```agda
godelIIClassicalTrivStrong :
  Consistent Triv ->
  Deriv Triv ConTrivRose_Strong ->   -- NOTE: strong form
  Empty
```

This proves Goedel II over the Rose-style consistency directly, without
needing to bridge to the weaker ConTrivRose.  The bridge is a separate
classical-logic exercise that can be deferred.

## Files to touch (in order)

1. **Read**  `Guard/ROSE-CHAIN-DESIGN.md`  for the full design analysis.
2. **New**   `Guard/GodelIIClassicalTrivStrong.agda`  with
              ConTrivRose_Strong definition + Schema-F premises
              (analogues of baseF, stepG, baseG).
3. **New or extend**  a Rose-chain module that assembles dConStrong +
              roseLemma1T(dNegGsRose) + Lemma1T-hyp-encoding into the
              bot-under-H_enc derivation (Step B 1-5 above).
4. **Close** godelIIClassicalTrivStrong via Consistent Triv.

## Sanity commands

```
time ~/.cabal/bin/agda-2.9.0 Guard/RoseLemma1T.agda
  # 0.25s, no output
time ~/.cabal/bin/agda-2.9.0 Guard/GodelIIClassicalTriv.agda
  # 0.13s, no output
time ~/.cabal/bin/agda-2.9.0 Guard/RoseEFun.agda
  # 0.04s, no output
```
