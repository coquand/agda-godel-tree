# UNIFIED-DESIGN: one-layer, hyp-less Deriv on formulas

## Goal

Port Guard 1963's BRA (Lecture Notes on Recursive Arithmetic, Def 7,
pp.9-10) as a single Agda data type matching Guard's formal system
structurally, and prove Gödel I and Gödel II against it.

Previous iterations split the system across multiple layers
(`Guard.Step.Deriv` for equations, `Guard.Provable` for propositions,
`Guard.BRA` for the Option G rewrite).  Each layer carried a
hypothesis parameter (`hyp : Equation` or `hyp : Formula`).  This
design collapses all of that into a single hyp-less relation on
formulas, mirroring Guard's `⊢ P`.

## Motivation

Five distinct problems converge on the same architectural fix:

1. **Guard has no `Deriv` relation.** BRA is a Hilbert system:
   axioms + rules, closed under `⊢`.  Hypothetical reasoning
   ("`X ⊢ Y`") is an informal shortcut for `⊢ X ⊃ Y`, justified by
   the deduction theorem (Guard Exercise 19).  Our hyp-ful
   `Deriv hyp P` is a deviation from Guard, not a feature of BRA.

2. **The multi-layer split is artificial.** We've had
   `Deriv` (equational) + `Provable` / `BRA` (propositional) with
   `fromDeriv` embeddings, `provExtract` / `braExtract` soundness
   bridges, and `provToBRA` bridges between them.  Guard has one
   layer.  Merging is a net simplification.

3. **The Option G formula-level-negation obstruction was
   mis-diagnosed.** The original analysis claimed a circular
   soundness requirement on a hypothetical `case34` (`~`) encoder.
   That circularity was an artifact of conflating the validating
   `thmT` with the axiom system's soundness.  Guard's `th` doesn't
   validate; it structurally emits Gödel numbers.  Soundness is a
   meta-theorem about the axiom set (Guard Thm 8), not a per-encoder
   check.  See the exchange in session 2026-04-22 for the corrected
   framing.

4. **Equation-form `gsCR` / `conBRAEqn` doesn't map onto Guard's
   ~-formula Gödel sentence.** We encoded "A ≠ B" as the equation
   `TreeEq A B = poo`, which was convenient for the equational
   `Deriv` but fights Guard's formula-level ~.  A ~-formula `gsCR`
   is the natural form in Guard's system and admits a direct `axNeg`
   + `mp` closure.

5. **Hyp-carrying rules accumulate side conditions.** `ruleInst`
   requires `Eq (substEq x t hyp) hyp`.  A future `ruleIndBT`
   requires three analogous conditions.  Every `hyp` in every
   derivation propagates these obligations.  Hyp-less rules have
   none.

## Design

### Formulas (Guard Def 7)

The existing `Guard.Formula.Formula` is correct as-is:

```agda
data Formula : Set where
  atomic : Equation -> Formula
  not_   : Formula -> Formula
  _imp_  : Formula -> Formula -> Formula
```

No changes.  Primitive connectives are `~` and `⊃` only, matching
Guard (other connectives are abbreviations if ever needed).  The
`atomic` wrapper is the one-line bridge from `Equation` (existing
infrastructure) to `Formula`.  `substF` and `codeFormula` are already
defined.

### Derivation relation (Guard Def 7 + rules)

Single data type, no hyp, target is a formula:

```agda
data Deriv : Formula -> Set where

  ------------------------------------------------------------------
  -- Equational axioms (Guard Ax 0-10).  Conclude atomic equations.

  axNotSZero : Deriv (not (atomic (eqn (ap1 succ O) O)))      -- Ax 0
  axO        : (x : Term) -> Deriv (atomic (eqn (ap1 zeroF x) O))
  axU        : (x : Term) -> Deriv (atomic (eqn (ap1 u x) x))
  axV        : (x y : Term) -> Deriv (atomic (eqn (ap2 v x y) y))
  axEqTrans  : (a b c : Term) ->
               Deriv ((atomic (eqn a b))
                       imp ((atomic (eqn a c))
                             imp (atomic (eqn b c))))           -- Ax 4
  axEqCong1  : (f : Fun1) (a b : Term) ->
               Deriv ((atomic (eqn a b))
                       imp (atomic (eqn (ap1 f a) (ap1 f b)))) -- Ax 5
  axEqCongL  : (g : Fun2) (a b c : Term) ->
               Deriv ((atomic (eqn a b))
                       imp (atomic (eqn (ap2 g a c) (ap2 g b c)))) -- Ax 6
  axEqCongR  : (g : Fun2) (a b c : Term) ->
               Deriv ((atomic (eqn a b))
                       imp (atomic (eqn (ap2 g c a) (ap2 g c b)))) -- Ax 7
  axComp     : (f g h : Fun1) (x : Term) ->
               Deriv (atomic (eqn (ap1 (Comp f g) x) (ap1 f (ap1 g x))))  -- Ax 8-style
  ...  -- all existing Guard.Step.Deriv equational axioms, each lifted
       -- to produce  atomic (eqn _ _)

  ------------------------------------------------------------------
  -- Additional equational axioms (our extensions over Guard's
  -- minimal BRA: Pair/Fst/Snd, IfLf, TreeEq, Goodstein, etc.).  All
  -- produce  atomic (eqn _ _)  conclusions, same pattern.

  axFst      : (a b : Term) -> Deriv (atomic (eqn (ap1 Fst (ap2 Pair a b)) a))
  axSnd      : (a b : Term) -> Deriv (atomic (eqn (ap1 Snd (ap2 Pair a b)) b))
  axIfLfL    : (a b : Term) -> Deriv (atomic (eqn (ap2 IfLf O (ap2 Pair a b)) a))
  ...

  ------------------------------------------------------------------
  -- Structural rules (atomic-equation-only, at the object level).

  axRefl     : (t : Term) -> Deriv (atomic (eqn t t))
  ruleSym    : {t u : Term} -> Deriv (atomic (eqn t u)) ->
                               Deriv (atomic (eqn u t))
  ruleTrans  : {t u v : Term} -> Deriv (atomic (eqn t u)) ->
                                  Deriv (atomic (eqn u v)) ->
                                  Deriv (atomic (eqn t v))
  cong1      : (f : Fun1) {t u : Term} ->
               Deriv (atomic (eqn t u)) ->
               Deriv (atomic (eqn (ap1 f t) (ap1 f u)))
  congL      : (g : Fun2) {t u : Term} (x : Term) ->
               Deriv (atomic (eqn t u)) ->
               Deriv (atomic (eqn (ap2 g t x) (ap2 g u x)))
  congR      : (g : Fun2) (x : Term) {t u : Term} ->
               Deriv (atomic (eqn t u)) ->
               Deriv (atomic (eqn (ap2 g x t) (ap2 g x u)))

  ------------------------------------------------------------------
  -- Propositional axioms (Guard Ax 11, 12, 13).

  axK        : (P Q : Formula) ->
               Deriv (P imp (Q imp P))
  axS        : (P Q R : Formula) ->
               Deriv ((P imp (Q imp R))
                      imp ((P imp Q) imp (P imp R)))
  axNeg      : (P Q : Formula) ->
               Deriv ((not P) imp ((not Q) imp (Q imp P)))

  ------------------------------------------------------------------
  -- Rules of inference (no side conditions — no hyp to constrain).

  mp         : {P Q : Formula} ->
               Deriv (P imp Q) ->
               Deriv P ->
               Deriv Q

  ruleInst   : (x : Nat) (t : Term) {P : Formula} ->
               Deriv P ->
               Deriv (substF x t P)

  ruleIndBT  : (P : Formula) (v1 v2 : Nat) ->
               Deriv (substF zero O P) ->
               Deriv ((substF zero (var v1) P) imp
                      (substF zero (var v2) P) imp
                      (substF zero (ap2 Pair (var v1) (var v2)) P)) ->
               Deriv P
```

### Induction is binary-tree induction

Our primitive data structure is `Tree = lf | nd a b`, not `Nat`.
Primitive recursion is `Rec z s`:
 * `Rec z s lf = z`             (axRecLf)
 * `Rec z s (nd a b) = s (nd a b) (Pair (Rec z s a) (Rec z s b))`  (axRecNd)

The induction rule matches:
 * base:  `P(O)` — corresponds to `lf`.
 * step:  `P(x_1) ⊃ P(x_2) ⊃ P(Pair x_1 x_2)` — corresponds to
          `nd`'s two subtrees via `Pair`.

Guard's unary induction on `Nat` is a derived rule: naturals embed as
`natCode : Nat → Tree` (`natCode 0 = lf`, `natCode (suc n) = nd
(natCode n) lf`), and the unary version is the special case where one
subtree is ignored.  We lose nothing by having only binary-tree
induction as primitive.

### Hyp-less rules: no side conditions

`ruleInst` and `ruleIndBT` as written above have no preconditions.
This is consistent because there is no hyp to constrain.  Guard's
original rules have no Hilbert-Bernays side conditions either (they
are statements about `⊢ P` closure).

Soundness of substitution and induction is a validity-preservation
meta-theorem (Guard Thm 8):  if `⊢ P` and `P` is valid, then every
instance `P[t/x]` is valid; similarly for induction.  We re-prove
this meta-theorem against our specific axiom set as part of the new
`godelIClassical` proof.

### Deduction theorem

The object-level analog of Guard's Exercise 19:

```agda
data DerivAssuming (A : Formula) : Formula -> Set where
  -- mirror every Deriv constructor:
  axNotSZero' : DerivAssuming A (not (atomic (eqn (ap1 succ O) O)))
  ...
  axK'        : (P Q : Formula) -> DerivAssuming A (P imp (Q imp P))
  ...
  mp'         : {P Q : Formula} ->
                DerivAssuming A (P imp Q) ->
                DerivAssuming A P ->
                DerivAssuming A Q
  ...
  -- and one extra constructor:
  ruleHypAux  : DerivAssuming A A

deductionTheorem : (A B : Formula) ->
                   DerivAssuming A B ->
                   Deriv (A imp B)
```

`DerivAssuming` is used ONLY to state and prove the deduction
theorem.  Working derivations live in `Deriv`; hypothetical reasoning
materialises as implication via `deductionTheorem`.

`deductionTheorem`'s proof is a standard Hilbert-system structural
induction, using `axK` + `axS` to lift each case.  ~100-150 lines.

## What this replaces

| Current module               | Unified replacement            |
|------------------------------|--------------------------------|
| `Guard.Step.Deriv`           | `Deriv` (on formulas, hyp-less) |
| `Guard.Provable`             | `Deriv` (absorbed)             |
| `Guard.BRA`                  | `Deriv` (absorbed)             |
| `Guard.ProvableSound`        | `validitySound` (direct)       |
| `Guard.ProvableLemmas`       | `dedThmLib` (via `DerivAssuming`) |
| `Guard.ProvableEqLifts`      | `eqLifts` (atomic-only helpers) |
| `Guard.BRASound`             | (not needed — no hyp)          |
| `Guard.BRAGodelIBridge`      | absorbed into `godelII`        |
| `Guard.GodelIIBRA*`          | absorbed into `godelII`        |

The following stay unchanged:

 * `Guard.Term`, `Guard.Base` (terms, trees, equations).
 * `Guard.Formula` (formula data type).
 * `Guard.ThFun`, `Guard.ThFunTForV3`, `Guard.ThFunTForV3Defs`,
   `Guard.ThFunTForV3Pass`, `Guard.ThFunTForCorrectDefs`,
   `Guard.ThFunTForCases0..3`  (thmT validator + dispatches).  Note:
   these currently take `hyp : Equation` in their signatures because
   they produce `Deriv hyp (eqn _ _)`.  Post-migration, they produce
   `Deriv (atomic (eqn _ _))` without the hyp parameter.  The
   signature change is mechanical; no proof rewrite.
 * `Guard.ProofEnc`, `Guard.ProofEncFormula` (encoders).  Signature
   change only.
 * `Guard.CodeOfReify`, `Guard.SubstOp`, `Guard.SubstTForCorrect`,
   `Guard.SubstTForPrecompClassical`, `Guard.Thm14EV3`,
   `Guard.GodelIClassical`  — all carry over with signature
   adjustments.

## Architectural invariants

These remain:

1. Terms, trees, equations are primitive syntactic structures.
2. `Fun1`, `Fun2` represent primitive recursive functors; `Rec` is
   primitive recursion on trees.
3. `thmT` is a validator: it takes an encoded proof tree as input and
   emits the `codeFormula` of the conclusion (or a sentinel `O` on
   malformed input).  This is unchanged.  Validation is not at odds
   with Guard-faithfulness: we've confirmed the source of the Option
   G obstruction was mis-diagnosis, not validator mechanics.
4. Soundness of the axiom set (all `Deriv P` are valid in Guard Thm
   8's sense) is a meta-theorem proven separately.

These change:

5. ~~Multiple layers (Deriv / Provable / BRA)~~ → single `Deriv`.
6. ~~Hyp-relative reasoning intrinsic to the data type~~ → hyp-less,
   with `deductionTheorem` converting `DerivAssuming`.
7. ~~Equation-form `gsCR` = `TreeEq A B = poo`~~ → ~-formula
   `gsCR = not (atomic (eqn thx rhsT))`, matching Guard's Def 11.3.
8. ~~`conBRAEqn` = equation~~ → ~-formula
   `conBRAFormula = not (atomic (eqn (thmT x) codeBotT))`.

## Migration plan

Six commits, each typechecks incrementally without touching the
final-target files until the last step:

### [unify-1] New Deriv data type + deductionTheorem

Create `Guard/DerivF.agda` (new hyp-less type, temporarily named to
avoid collision) and `Guard/DerivFDedThm.agda` (deduction theorem).
Leave the old `Guard.Step.Deriv` in place.  Typechecks standalone.

### [unify-2] Migrate equational infrastructure

Port `Guard.StepReduce`, `Guard.ExtractorRed`, `Guard.CodeOfReify`,
`Guard.SubstOp`, `Guard.SubstTForCorrect`, `Guard.ThFun`,
`Guard.ThFunTForDefs`, `Guard.ThFunTForCases*`,
`Guard.ThFunTForCorrectDefs`, `Guard.TreeEqSelf`, `Guard.SubstTForPrecomp*`
to target `DerivF` at atomic equations.  Most changes are mechanical:
replace `Deriv hyp (eqn t u)` with `DerivF (atomic (eqn t u))`.

### [unify-3] Migrate thmT machinery

Port `Guard.ThFunTForV3`, `Guard.ThFunTForV3Defs`,
`Guard.ThFunTForV3Pass`, `Guard.Thm14EV3` to `DerivF`.  Extend
`substOp` to distribute through `tagImp` and `tagNeg` — needed for
formula-level `ruleInst` reductions.

### [unify-4] Migrate Gödel I

Port `Guard.SubstTForPrecompClassical`, `Guard.GodelIClassical` to
`DerivF`.  Migrate `gsCR` from equation form to ~-formula form.
State and prove the new `godelIClassical_neg` at the ~-formula
level.

### [unify-5] Re-port encoders + build the chain

Port `Guard.ProofEnc` and `Guard.ProofEncFormula` to `DerivF`.
Re-transcribe Guard Th 14's chain (steps 1-5) in a new
`Guard/GodelIIChain.agda` using the hyp-less primitives and
`deductionTheorem`.

### [unify-6] Gödel II + cleanup

Close `godelII : Consistent Triv -> DerivF (atomic conBRAFormula) ->
Empty` via the chain + `godelIClassical_neg`.

Delete obsolete modules: `Guard.Provable`, `Guard.ProvableSound`,
`Guard.ProvableLemmas`, `Guard.ProvableEqLifts`, `Guard.ProvableTh13`,
`Guard.ProvableGodelIBridge`, `Guard.BRA`, `Guard.BRAGodelIBridge`,
`Guard.ConBRA`, `Guard.ConBRAv2`, `Guard.GodelIIBRA`,
`Guard.GodelIIBRAPort`, `Guard.GodelIIBRAv2`, `Guard.RouteAChain`,
`Guard.RouteADf`.  Rename `DerivF` → `Deriv`, `Guard.DerivF` →
`Guard.Deriv`.  Delete the old `Guard.Step`.

Roughly 1000-1500 lines modified / added, 800-1200 lines deleted.
Net: smaller, simpler codebase.

## Risks and open questions

1. **Soundness of `ruleInst` without hyp side condition.**  In the
   hyp-less system, `ruleInst x t P` is always sound (substitution of
   a ground theorem by any term gives a valid formula).  But the
   deduction theorem's proof needs care: when converting
   `DerivAssuming A B` to `Deriv (A ⊃ B)`, the `ruleInst` case
   requires `A`'s variable-freshness in `t` or similar.  Standard but
   needs attention.

2. **Induction soundness at the axiom level.**  `ruleIndBT` at the
   object level is sound if `P` ranges over the two-subtree induction
   pattern correctly.  The validity-preservation proof is standard
   but needs explicit verification against our `Tree` inductive type.

3. **Migration of `Thm14EV3`.**  Our Thm 12 analog proves
   `thmT trivCT (enc d) = reify (codeEqn (concl d))` for each Deriv
   constructor `d`.  Post-migration, `concl d` is a `Formula`, so we
   need `reify (codeFormula (concl d))`.  The wrapping from `codeEqn`
   to `codeFormula ∘ atomic` is definitional — a one-line change per
   encoder case.

4. **`diagFTargetCR` and the ~-formula `gsCR`.**  Current `gsCR` uses
   equation form.  The migrated `gsCR` is `not (atomic (eqn thx
   rhsT))`.  `diagFTargetCR` currently proves `rhsT = reify cGSCR`
   where `cGSCR = codeEqn gsCR` (equation code).  Post-migration,
   `cGSCR = codeFormula gsCR = codeFormula (not (atomic ...)) = nd
   tagNeg (codeEqn ...)`.  The numeral changes; the proof strategy
   (via `codedSubst` unfolding) carries over with one extra layer
   of tagNeg handling.

5. **Chain step 4.**  Previously flagged as an obstruction; with
   the ~-formula migration, it becomes `ruleInst` applied to the
   proof-slot under the `conjHyp = atomic (eqn thx j)` hypothesis,
   wrapped in `deductionTheorem` at the outer level.  Step 4's
   content naturally produces a ~-formula encoding because `gsCR`
   IS a ~-formula.

## What this is NOT

 * Not a rewrite of the Term / Fun1 / Fun2 / Tree infrastructure.
 * Not a change to the encoder tags or dispatch chain (case0..case33
   stay, case34 for `~` added).
 * Not abandoning Option A's soundness-at-validator discipline:
   `thmT` still validates sub-proofs at case19V3, case23V3, case33.
   Validation is compatible with Guard-faithfulness.
 * Not abandoning the Agda proof infrastructure already built:
   `Thm14EV3`'s per-case correctness, the existing encoder cases,
   `godelIClassical`'s classical diagonal — all port through.

## Deprecation trail

 * `[bra-g-*]`  Option G commits (2026-04-22): BRA data type,
   formula-level encoders, chain steps 1-3, ports.  Superseded by
   the unified design but the infrastructure (encAxK/S/Neg/Mp,
   case30..33) transfers intact.

 * `[provable-*]`  Propositional layer (earlier sessions).
   Superseded.  Content absorbed via `axK`/`axS`/`axNeg` + `mp` as
   `Deriv` constructors.

 * `[route-a-*]`  Thm 13 lift via cor + encEqRefl (RouteADf /
   RouteAChain).  Absorbed into `Guard.Thm13` post-migration.

No proof work is lost; each prior effort contributed a structural
component (encoders, diagonal construction, chain steps) that re-uses
against `Deriv` with signature changes only.
