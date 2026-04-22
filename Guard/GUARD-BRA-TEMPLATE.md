# Guard 1963 BRA-style Gödel II — Detailed Template

## Goal

Adapt Guard 1963 (`guard15.pdf`) chapter on Gödel I / Gödel II to our
existing Guard/ codebase by adding a **propositional layer** above our
existing equational `Deriv` system. This bypasses the impT-as-IfLf
gymnastics that blocked the previous attempt.

Key insight: Guard's BRA has propositional connectives `⊃` and `~` as
**primitive**, plus K (axiom 11), S (axiom 12), and classical
contraposition (axiom 13) as axioms. Deduction theorem follows
(Exercise 19). All the hypothetical-syllogism/dedThm machinery we were
trying to derive equationally is **primitive** in BRA.

## Architecture

```
┌─────────────────────────────────────────────────┐
│  Provable layer (NEW)                           │
│  - Formula : Set (atomic | ⊃ | ~)               │
│  - Provable : Formula → Set                     │
│  - K, S, NEG axioms                             │
│  - modusPonens, ruleHypP, ruleSubP              │
│  - fromDeriv embedding                          │
│  - Th 11 (Gödel I), Th 14 (Gödel II)            │
└─────────────────────────────────────────────────┘
                     ▲
                     │ fromDeriv
                     │
┌─────────────────────────────────────────────────┐
│  Deriv layer (EXISTING — REUSED unchanged)      │
│  - Term, Equation, Deriv hyp eq                 │
│  - axI .. axGoodstein (~22 axioms)              │
│  - ruleSym, ruleTrans, congL/R/1, ruleInst, ruleF│
│  - treeEqRefl, treeEqSelf                       │
│  - thmT, codeEqn, encoders (ProofEnc)           │
└─────────────────────────────────────────────────┘
```

The existing `Guard/` directory (60 files, ~30K lines) is **untouched**
except for the orphaned `Guard/ImpTSchemaF.agda` and `Guard/ImpTL1.agda`
from the abandoned impT-form Lemma 1 attempt — these can stay as
historical record or be deleted.

The new layer is ~5-7 new files, ~650 lines total.

## Provable layer — exact definitions

### `Guard/Formula.agda` (~50 lines)

```agda
module Guard.Formula where

open import Guard.Term using (Equation)

data Formula : Set where
  atomic : Equation -> Formula
  not_   : Formula -> Formula      -- ~ P
  _imp_  : Formula -> Formula -> Formula   -- P ⊃ Q

-- Negation as an abbreviation for not.  Following Guard's notation.
infixr 5 not_
infixr 4 _imp_
```

Note: pure data declaration; no induction principle needed beyond
Agda's built-in pattern matching.

### `Guard.Provable.agda` (~150 lines)

```agda
module Guard.Provable where

open import Guard.Formula
open import Guard.Term using (Equation; subst; var; Term)
open import Guard.Step using (Deriv)

-- Provable hyp P : "from hyp (a single Formula hypothesis), P is
-- derivable".  The single-hypothesis form mirrors our existing
-- Deriv hyp eq.  Multi-hypothesis case can be encoded via P ⊃ Q.

data Provable (hyp : Formula) : Formula -> Set where

  -- Embedding from the Deriv layer.  Any Deriv-level fact at hyp=Triv
  -- (i.e., polymorphic in Deriv-level hypothesis) lifts to a Provable
  -- atomic at any Provable-level hyp.
  fromDeriv : {eq : Equation} ->
              ({h : Equation} -> Deriv h eq) ->
              Provable hyp (atomic eq)

  -- Hypothesis.
  ruleHypP : Provable hyp hyp

  -- Propositional axioms (Guard Ax 11, 12, 13).
  axK : (P Q : Formula) ->
        Provable hyp (P imp (Q imp P))

  axS : (P Q R : Formula) ->
        Provable hyp ((P imp (Q imp R)) imp ((P imp Q) imp (P imp R)))

  axNeg : (P Q : Formula) ->
          Provable hyp ((not P) imp ((not Q) imp (Q imp P)))

  -- Modus ponens.
  mp : {P Q : Formula} ->
       Provable hyp (P imp Q) ->
       Provable hyp P ->
       Provable hyp Q

  -- Substitution rule (Guard's substitution of terms for variables).
  -- At the Formula level, substitute a Term for a free variable in
  -- atomic-equation subformulas.  Only atomic case mentioned here;
  -- compound ~ and ⊃ recurse via a function substF (defined in this
  -- module).
  ruleSubP : (x : ℕ) (t : Term) {P : Formula} ->
             Provable hyp P ->
             Provable hyp (substF x t P)

  -- Equality axioms (Guard Ax 4, 5, 6, 7).  Stated at the Provable
  -- level so they can chain with ⊃ and ~.
  axEqTrans : (a b c : Term) ->
              Provable hyp ((atomic (eqn a b)) imp ((atomic (eqn a c))
                            imp (atomic (eqn b c))))
  axEqCong1 : (f : Fun1) (a b : Term) ->
              Provable hyp ((atomic (eqn a b)) imp
                            (atomic (eqn (ap1 f a) (ap1 f b))))
  -- ... (axEqCongL, axEqCongR similarly)
```

Notes:
- `fromDeriv` requires the underlying Deriv to be polymorphic in its
  Deriv-hypothesis. This matches all our axioms (axI, axGoodstein,
  treeEqRefl as a derived rule, etc.) which are polymorphic.
- Equality axioms (Ax 4-7) are stated as Provable axioms because they
  cross between equation-level and propositional-level reasoning. They
  are derivable from Deriv's axioms but stated as Provable axioms for
  convenience (each ~5 lines to prove from `fromDeriv` + modus ponens).

### `Guard/ProvableLemmas.agda` (~80 lines)

Derived theorems and the deduction theorem.

```agda
-- Identity:  P ⊃ P.  Standard combinator derivation: P ⊃ ((P ⊃ P) ⊃ P)
-- by axK, then axS+axK to get P ⊃ P.
provI : (P : Formula) -> Provable hyp (P imp P)

-- Deduction theorem.  This is THE key meta-theorem.
-- "If under (P :: hyp) we can derive Q, then under hyp we can derive
-- P ⊃ Q."  Proved by induction on Provable.
deductionThm : {P Q : Formula} ->
               Provable P Q ->                  -- under hypothesis P
               Provable hyp (P imp Q)            -- at any other hyp
-- Proof by induction on the Provable proof tree:
--   ruleHypP -> use provI : P ⊃ P.
--   axK / axS / axNeg / equality axioms -> wrap with axK to get
--     hyp ⊃ axiom.
--   mp pq p -> chain via S: deduction(pq) gives hyp ⊃ (P ⊃ Q),
--     deduction(p) gives hyp ⊃ P, axS combines.
--   fromDeriv d -> wrap with axK.
--   ruleSubP -> commute with substitution.
--   ruleHypP if P matches the hyp -> provI; else axK lift.

-- Hypothetical syllogism (composition).  Direct corollary of deductionThm
-- + a few mp's:  (P ⊃ Q) ⊃ ((Q ⊃ R) ⊃ (P ⊃ R)).
hypSyll : (P Q R : Formula) ->
          Provable hyp ((P imp Q) imp ((Q imp R) imp (P imp R)))

-- Reductio: if P ⊃ Q and P ⊃ ~ Q, then ~ P.  Via classical contraposition.
reductio : (P Q : Formula) ->
           Provable hyp (P imp Q) ->
           Provable hyp (P imp (not Q)) ->
           Provable hyp (not P)
```

### `Guard/ProvableEqLifts.agda` (~80 lines)

Wrappers for our existing Deriv lemmas at the Provable layer.

```agda
-- Lift treeEqRefl: TreeEq a b = O ⊃ a = b.
treeEqReflP : (a b : Term) ->
              Provable hyp ((atomic (eqn (ap2 TreeEq a b) O))
                            imp (atomic (eqn a b)))
treeEqReflP a b = ?  -- via fromDeriv on treeEqRefl + axK + mp.

-- Similarly for axGoodstein, axIfLfL, etc.
```

## Lemma 2 / Theorem 12-13 (substitution preservation by th)

### `Guard/Th12_13.agda` (~200 lines)

This is the BRA analog of our existing `thm14EV3`. Specifically:

**Th 12 (BRA)**: For every singulary functor f, there exists Df such
that `th(Df(x)) = "f(x) = f(x)"` (Gödel number form).

**Th 13 (BRA)**: For each singulary f, `f(x) = y ⊃ th(Df(x)) = "fx = y"`.

In our setting, the analog is:

```agda
thm12 : (f : Fun1) (x : Term) ->
        Provable hyp (atomic (eqn (ap1 (thmT trivCT) (Df f x))
                                   (reify (codeEqn (eqn (ap1 f x) (ap1 f x))))))
        -- "th(Df(x)) = code of (f x = f x)"

thm13 : (f : Fun1) (x y : Term) ->
        Provable hyp ((atomic (eqn (ap1 f x) y))
                       imp (atomic (eqn (ap1 (thmT trivCT) (DfY f x y))
                                         (reify (codeEqn (eqn (ap1 f x) y))))))
```

**Key observation**: `Df` and `DfY` are concrete Term combinators
(constructed from the proof of f x = y via our existing thm14EV3 / 
ProofEnc encoders). The Provable layer just packages the result with
⊃ structure.

`thm13` follows from `fromDeriv` on `thm14EV3` applied to `axRefl`-like
derivations + chaining via deductionThm/hypSyll.

## Theorem 11 (Gödel I) at the Provable layer

### `Guard/Thm11.agda` (~100 lines)

We REUSE our existing `godelIClassical` (Guard.GodelIClassical), which
gives us `Deriv Triv gsCR -> Deriv Triv bot`. Lifted to Provable:

```agda
godelI_BRA : Provable hyp (atomic gsCR imp atomic bot)
godelI_BRA = ?  -- fromDeriv (deductionThm-style on godelIClassical)
```

## Theorem 14 (Gödel II) at the Provable layer

### `Guard/Thm14.agda` (~150 lines)

Direct transcription of Guard's Th 14 proof (guard15.pdf p.16-17).

```agda
godelII_BRA : (Consistent BRA) ->
              Provable hyp (atomic ConBRA) ->
              Empty
```

Where `ConBRA` is the BRA-style consistency sentence ("th(y) ≠ '0=1'")
encoded as an atomic formula.

The proof transcribes Guard's 5-step chain:
```
1) th(x) = j ⊃ th(Dth(x)) = "th(x) = j"           -- thm13
2) th(Dsub(i, i)) = "sub(i, i) = j"               -- thm13 + computation
3) th(x) = j ⊃ th(gx) = "th(x) = sub(i, i)"       -- 1) + 2) + internal mp
4) th(x) = j ⊃ th(...) = "th(x) ≠ sub(i, i)"     -- def of j
5) th(x) = j ⊃ th(combined) = "0 = 1"             -- 3) + 4) + internal mp
```

Each step uses thm13 + propositional reasoning (axK, axS, mp,
deductionThm). The "internal mp" steps use a Term-level combinator that
encodes modus ponens at the th-level (similar to encRuleTrans in our
existing ProofEnc).

The final reductio: if `th(y) ≠ "0=1"` were provable, then by
substitution + step 5, `th(x) ≠ j` would be provable — contradicting
Gödel I (Theorem 11). Hence ConBRA is unprovable.

## Critical design questions and answers

**Q1: Single-hypothesis vs multi-hypothesis Provable?**  
A: Single (`Provable hyp formula`), matching Deriv's structure. Multi-
hyp emulated via P ⊃ Q. Deduction theorem makes this equivalent to
multi-hyp.

**Q2: How does fromDeriv handle the hyp parameter?**  
A: fromDeriv takes a polymorphic-in-Deriv-hyp derivation (`{h : Equation}
-> Deriv h eq`). All our useful equational facts are polymorphic.
Provable's hyp parameter is independent.

**Q3: Equality axioms — derive or admit?**  
A: Admit at Provable layer (5 lines each, 4 axioms). Each is a one-line
wrapper of the corresponding Deriv axiom (axRefl, ruleSym, etc.) +
axK to get the ⊃ form. Trivial.

**Q4: Substitution rule on compound formulas?**  
A: Define `substF : ℕ → Term → Formula → Formula` recursively
(atomic uses substEq from Term.agda; ~ and ⊃ recurse). ~10 lines.

**Q5: Induction at Provable layer?**  
A: Not needed for Gödel II proof. Schema F (Deriv-level) suffices for
all equational facts; Provable just chains them propositionally.

**Q6: Consistency of BRA — meta-level statement?**  
A: `Consistent BRA = Provable hyp (atomic (eqn O O) imp false-formula)
→ Empty` — the standard contradictory-derivation-implies-false form.
Wrapping our existing `Consistent Triv`.

## File layout

```
Guard/Formula.agda              50 lines  - Formula data type
Guard/Provable.agda            150 lines  - Provable + axioms + mp + sub
Guard/ProvableLemmas.agda       80 lines  - provI, deductionThm, hypSyll, reductio
Guard/ProvableEqLifts.agda      80 lines  - treeEqReflP, axIfLfLP, ...
Guard/Th12_13.agda             200 lines  - Lemma 2 at Provable (subst preservation by th)
Guard/Thm11.agda               100 lines  - Gödel I at Provable layer
Guard/Thm14.agda               150 lines  - Gödel II at Provable layer
                              ----
                               810 lines total
```

## Implementation order

1. **Formula** + **Provable** core (with axioms + mp + ruleHypP + fromDeriv,
   no substitution yet). Verify typechecks. ~150 lines, 1 commit.

2. **Substitution at Formula level + ruleSubP**. ~30 lines, 1 commit.

3. **provI + deductionThm**. The critical proof — induction on Provable.
   ~80 lines, 1 commit. **High-risk: if this doesn't work, reassess.**

4. **hypSyll + reductio + equality axioms**. ~80 lines, 1 commit.

5. **ProvableEqLifts** — wrap our existing Deriv lemmas. ~80 lines, 1 commit.

6. **Th 12-13** (substitution preservation by th, lifted from thm14EV3).
   ~200 lines, 2-3 commits.

7. **Th 11** (Gödel I at Provable). ~100 lines, 1 commit.

8. **Th 14** (Gödel II at Provable). ~150 lines, 2 commits.

**Total: ~10-12 commits, estimated 4-8 hours of focused work.**

## Risks and mitigations

| Risk | Likelihood | Mitigation |
|---|---|---|
| deductionThm proof is harder than expected | Medium | Step 3 is the gating commit. If blocked >1 hour, revisit design. |
| substitution interaction with ⊃/~ has corner cases | Low | Standard Agda recursive definition; well-understood. |
| Th 12-13 needs more axioms than anticipated | Medium | We can add Provable-level axioms freely (shape-legitimate). |
| Th 14 chain doesn't match guard15.pdf transcription | Low | Guard's proof is detailed; should transcribe step-by-step. |
| `fromDeriv` polymorphism constraint is too restrictive | Medium | Worst case: add a `fromDerivHyp : Deriv H eq → Provable (atomic H ⊃ atomic eq)` variant for non-polymorphic Derivs. |

## What gets orphaned

- `Guard/ImpTSchemaF.agda` (impTSelf, impTAnyTrueT) — keep as historical;
  may have future use.
- `Guard/ImpTL1.agda` (scaffold) — delete or keep stub.
- The broader `Guard/RoseLemma1T.agda`, `Guard/Thm14EV3.agda` etc.
  REMAIN USEFUL: they provide the Term-level proof encoders (Df, DfY)
  needed by Th 12-13.

## What we KEEP from existing work

- All of `Guard/Step.agda` (Deriv, all 22+ axioms).
- All of `Guard/Term.agda` (term grammar, codeEqn, etc.).
- `Guard/TreeEqSelf.agda`, `Guard/TreeEqRefl.agda`.
- `Guard/ProofEnc.agda` (encoder combinators — used by Th 12-13).
- `Guard/ThFunTForV3.agda` and the thmT machinery.
- `Guard/Thm14EV3.agda` (encoding correctness — used by Th 12-13 for
  Lemma 2 lift).
- `Guard/GodelIClassical.agda` (used by Th 11 lift).

The new layer is ADDITIVE, not destructive.

## Open questions before starting

1. Should `Provable` be parameterized over hyp (`Provable hyp formula`) or
   over a list of hypotheses (`Provable hyps formula`)?
   **Answer**: single hyp, like Deriv.

2. Should we use Agda's built-in `_⊃_` (function arrow) or our own
   constructor for ⊃?
   **Answer**: our own constructor (so Formula remains finitary).

3. Should `not P` be primitive or `P ⊃ ⊥` for some falsity?
   **Answer**: primitive, following Guard. Simpler axioms.

4. Should we expose `axEqTrans`, `axEqCong*` directly or derive them
   from `fromDeriv`?
   **Answer**: derive them as lemmas (1 line each via `fromDeriv` +
   `axK`-wrapping). Not actual axioms.

## Decision checkpoint

If during step 3 (deductionThm) we find the propositional-axioms-as-
chosen don't suffice or the proof is getting unwieldy (>2x estimated
size), STOP and add more axioms or revise the design. The deduction
theorem is the make-or-break milestone.
