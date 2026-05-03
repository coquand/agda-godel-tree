# Architectural findings — two design defects in BRA's syntax

Date: 2026-05-01.  Surfaced while attempting `thm12_F2 (Fan h1 h2 h)` cleanly.

## Guiding principle (durable)

BRA's proofs follow the elementary mathematics of guard15.pdf.  Concretely:

- Proofs are plain case analysis on `Term` / `Tree` / `Fun1` / `Fun2` / `Nat`.
- Induction on derivations (`Deriv`) is admissible when the paper's proof is by induction on derivations.
- **No fancy Agda features**: no dot patterns (`.(...)`), no `with` abstractions, no dependent index unification, no instance arguments, no REWRITE pragmas, no irrelevance annotations.

If a proof requires such machinery, that signals the formalisation has drifted from the paper.  Fix the formalisation, not the Agda surface.

The current codebase honours this almost everywhere.  The single offender is `BRA/Thm/ThmT.agda`'s `encodeRich`, which uses 40 dot patterns and 0 elsewhere — and is exactly the function that gets stuck when `Fun2` grows a constructor.  See Finding 2 below.

---


## Finding 1 — The `parDispCongL` / `parDispCongR` depth-3 encoding creates an artificial shape obligation

### What

`thm12`'s `Comp2` and `Fan` cases call `parDispCongL` / `parDispCongR` (Fun2 single-slot substitution), which use the encoding

```
parEncCongL g y_h xT  =  ap2 Pair tagCongL
                          (ap2 Pair (reify (codeF2 g))
                            (ap2 Pair y_h xT))
```

`thmT` distributing through this needs to walk past the inner `Pair y_h xT`, requiring `Fst y_h` to be Pair-shaped.  But `y_h` is the open IH-output term — its shape is not provable from the IH `d_h : thmT y_h = Pair u1 u2`.

### Why this defect is *not* present for `Comp`

`parEncCong1 f y_h = ap2 Pair tagCong1 (ap2 Pair (reify (codeF1 f)) y_h)` — depth 2.  Only one distribution, on a `Pair` whose `Fst` is the closed `reify (codeF1 f)`.  No obligation on `y_h`.

### Why we got the awkward depth-3 form

`congL g xT (IH at y_h)` is "apply Fun2 `g` to (LHS, xT) and (RHS, xT)".  CongL needs to encode three things: the functor `g`, the open IH-position `y_h`, and the literal *other slot* `xT`.  The current encoding nests these so that the open `y_h` ends up *inside* an inner Pair that thmT has to walk through.

### The clean fix

Reorder so the open subterm sits at the **outer `Snd`**:

```
parEncCongL g y_h xT  =  ap2 Pair tagCongL
                          (ap2 Pair (ap2 Pair (reify (codeF2 g)) xT)
                                    y_h)
```

Now thmT's walk goes through:
- outer Pair `(Pair codeF2g xT, y_h)` — `Fst` = `Pair codeF2g xT`, Pair-shape via `axFst`.
- inner Pair `(codeF2g, xT)` — `Fst` = `codeF2g`, Pair-shape via `fstReifyCodeF2`.

`y_h` reaches `body_congL` via `Snd b` directly; `thmT(y_h)` is supplied by `d_h`.  No shape on `y_h` is needed at any step.

### Cost

`body_congL` / `body_congR` combinator navigation, plus all `body_congL_eval` / `_param` / `_lifted` / `_doublelifted` and `parDispCongL` / `parDispCongR` lemmas in `BRA/Thm/ThmT.agda` (~600 LoC), plus consumers (`Comp2.agda`, `Fan.agda`, `TreeEqNN.agda`, `StepT12.agda`, `Thm12RecCheck.agda`).  Total ~600-1000 LoC.

### Status

Deferred — handle after Finding 2's refactor.

---

## Finding 2 — `Rec` and `RecP` are a misdesigned split of Guard's `Rfgh`

### Guard's primitive (guard15.pdf p.10, axioms 9-10)

```
Rfgh(x, 0)   =  f(x)
Rfgh(x, sy)  =  g(h(x, y), Rfgh(x, y))
```

One combinator, three sub-arguments, doing both jobs at once: carries a parameter `x` AND has a non-trivial leaf `f(x)`.

### What BRA has instead

Two combinators, neither covering `Rfgh`:

```
Rec : Term -> Fun2 -> Fun1
  Rec z s O          = z                                                   -- non-trivial leaf, NO parameter
  Rec z s (Pair a b) = s (Pair a b) (Pair (Rec z s a) (Rec z s b))

RecP : Fun2 -> Fun2
  RecP s p O          = O                                                  -- parameter, but leaf FORCED to O
  RecP s p (Pair a b) = s (Pair p (Pair a b)) (Pair (RecP s p a) (RecP s p b))
```

`Rec` keeps the non-trivial leaf but drops the parameter.  `RecP` keeps the parameter but forces the leaf to `O`.  Their union ≈ Guard's `Rfgh`, but at any single use site you only have one or the other.

### Cost of the split

- Two pairs of axioms (`axRecLf` / `axRecNd` / `axRecPLf` / `axRecPNd`) instead of one.
- Two pairs of cascade tags (`tagAxRecLf` / `tagAxRecNd` / `tagAxRecPLf` / `tagAxRecPNd`) instead of one.
- Two pairs of `body_*` dispatchers in `thmT` instead of one.
- Two `thm12` cases (`thm12_F1 (Rec z s)`, `thm12_F2 (RecP s)`) instead of one.
- `Rec`'s `z : Term` admits open `z` (e.g. `var k`), which forces the entire `Th12RecCloseS*` family (4 files), the `z_corLemma_for` parameter in `FromBridges`, and the `body_axRecLf` analysis (Task B of `NEXT-SESSION-THM12-FAN-COMP2.md`).  None of this is genuinely needed: the only concrete uses of `Rec` in BRA are `cor = Rec O stepCor` and `thmT = Rec O stepProto`, both with `z = O`.

### The unified replacement

```
R : Fun1 -> Fun2 -> Fun2

  ap2 (R f s) p O          = ap1 f p
  ap2 (R f s) p (Pair a b) = ap2 s (ap2 Pair p (ap2 Pair a b))
                                   (ap2 Pair (ap2 (R f s) p a)
                                             (ap2 (R f s) p b))
```

Recovers existing constructions:

| Before | After |
|---|---|
| `RecP s` | `R Z s` (since `Z p = O` by `axZ`) |
| `Rec z s` (only ever used with `z = O`) | wrap `R (KT z) s` to fix parameter, or for `z = O` use `R Z s` directly |
| `cor = Rec O stepCor`  | `cor = ap1-of (R Z stepCor)` (Fun1-from-Fun2 wrapper, parameter slot ignored) |
| `thmT = Rec O stepProto` | analogous |

### Direct simplifications

- 4 axioms collapse to 2 (`axRLf : R f s p O = f p`, `axRNd : R f s p (Pair a b) = s ...`).
- 4 cascade tags collapse to 2.  Two fewer `body_*` dispatchers in `thmT`.
- Goedel II's chain becomes shorter.
- `Th12RecCloseS*` family (4 files), `Th12RecPCloseS*` family (4 files), `z_corLemma_for` parameter — all deletable.
- One `thm12_F2 (R f s)` clause replaces three (`Rec`, `RecP` in current syntax).
- The "open-`z`" obstruction (Task B of NEXT-SESSION-THM12-FAN-COMP2.md) doesn't exist: leaf is `f p`, where `f : Fun1` reduces by its own axioms, not via a corOfReify bridge.

### Status

In progress — starting in this session.

### Migration plan

1. `BRA/Term.agda`: replace `Rec` / `RecP` constructors with `R`; update `codeF1` / `codeF2` / `substF1` / `substF2` / `KT`.
2. `BRA/Deriv.agda`: replace 4 axioms with 2.
3. `BRA/Thm/Tag.agda` (or wherever): replace 4 tags with 2.
4. `BRA/Thm/ThmT.agda`: collapse the 4 `body_*` dispatchers into 2; restructure cascade.
5. Cascade through ~25 consumer files: `Cor.agda`, `Sub.agda`, `Sb*.agda`, `CodeCommutes*.agda`, `CorF.agda`, `StepT12*.agda`, all `Th12Rec*` / `Th12RecP*` files, all `BRA/Thm12/` files.
6. Re-typecheck the 11 already-correct `BRA/Thm12/Parts/*.agda` files.

Total ~2000-3000 LoC across ~25 files.  Inherently a flag-day refactor (changing data types invalidates pattern matches everywhere).

---

## Implementation note (2026-05-01) — first-pass attempt findings

I attempted the additive pattern-synonym approach (add `R : Fun1 -> Fun2 -> Fun2` as a new Fun2 constructor, declare `pattern RecP s = R Z s` to keep legacy code working without modification).  Foundational changes succeeded for `BRA/Term.agda`, `BRA/Deriv.agda`, `BRA/CodeCommutes.agda`, `BRA/CorF.agda`.

**Obstacle in `BRA/Thm/ThmT.agda`:** `encodeRich` pattern-matches on `Deriv` constructors with Formula-indexed dependent types (e.g. `encodeRich .(substF x t P) (ruleInst x t {P = P} pf)`).  Adding `R` to `Fun2` extends `substF2`'s domain, and Agda's coverage checker hits `SplitError.UnificationStuck` on `substF x t P ≟ atomic (eqn O x₁)` — it can no longer prove the ruleInst case is exhaustive.

This is a known limitation of dependent pattern matching: extending an indexed datatype that appears in another type's index can break exhaustiveness even when no semantic content has changed.

**Possible workarounds** (for a future session):
- Restructure `encodeRich` to dispatch on the Formula first, then on the Deriv (avoids the index unification at the case-split level).
- Use Agda's `with`-abstraction or auxiliary definitions to bypass the unification.
- Accept the rejected `--exact-split` warning and use overlapping patterns with explicit catch-alls.
- Replace the recursive structure of `encodeRich` with a less-dependent form (e.g. each case as a separate top-level function).

**State at end of session:** all changes reverted to clean compilable state.  The architectural insight (collapse Rec/RecP → R, RecP = R Z) is sound; the implementation requires a careful Agda restructuring of `encodeRich` (and likely related functions) before the main refactor proceeds.

Recommended order for next session:
1. First, refactor `encodeRich` (and any other functions with dependent pattern matching that touches Fun2) to use a less-fragile splitting strategy.  Verify the existing build still typechecks.
2. Then add `R` constructor + pattern synonym + axioms.
3. Then cascade.

---

## Implementation note 2 (2026-05-01) — second-pass attempt findings

Step 1 of the recommended order above was completed: `encodeRich` was rewritten without dot patterns.  Type signature changed from `(P : Formula) -> Deriv P -> ...` to `{P : Formula} -> Deriv P -> ...`; all 40 dot-pattern clauses (`encodeRich .(formula) (constructor args) = ...`) became plain pattern-match clauses (`encodeRich (constructor args) = ...`).  Three call sites in `BRA/StepT12.agda` updated.  All files green.

**However**, when we then re-attempted to add `R` to `Fun2` with the obstruction supposedly cleared, the SAME `SplitError.UnificationStuck` error reappeared.  The hypothesis "dot patterns cause the unification problem" was wrong.

**Actual root cause:** `ruleInst : (x : Nat) (t : Term) {P : Formula} -> Deriv P -> Deriv (substF x t P)` has a non-constructor-shaped return-type-index (`substF x t P`).  When Agda's coverage checker is asked whether `ruleInst` could produce a Deriv with a specific concrete index (e.g. `atomic (eqn (ap2 TreeEq O O) O)` for the `axTreeEqLL` clause), it has to solve `substF x t P ≟ atomic (eqn O x₁)` — which requires unification through the function `substF`.  Adding any constructor to `Fun2` enlarges the case space `substF2` covers, and at some threshold Agda's coverage checker gives up.

**This issue exists independently of dot patterns** — it's intrinsic to having a function-valued return-type index on a Deriv constructor.  The dot-pattern rewrite was a worthwhile cleanup (the codebase is now `--without-K`-style across the board) but does not address the index-unification problem.

**Genuine fix per the no-fancy-features principle:** make `Deriv` a non-indexed inductive type, with a separate `concl : Deriv -> Formula` function.  Then constructors don't carry type-level indices and case analysis on Deriv is plain non-dependent pattern matching.  Adding constructors to Fun1/Fun2 then has zero effect on Deriv-level coverage.  This is a multi-session refactor — every Deriv-using function changes signature.

**Alternative (smaller, less faithful to the principle):** make `ruleInst`'s return type explicit-formula:

```
ruleInst : (x : Nat) (t : Term) (P : Formula) ->
           Deriv P -> Deriv (substF x t P)
```

— so `P` is bound on the LHS at every call site, possibly avoiding the inference-driven unification.  Worth trying first; minor cascade cost (every `ruleInst` call needs the explicit P).  But this still has `substF` in the return type, so the unification problem may persist.

**State at end of session:** dot-pattern rewrite landed (durable cleanup).  R refactor reverted again.

---

## Implementation note 3 (corrected diagnosis, 2026-05-01)

The user clarified: `Deriv : Formula -> Set` being indexed is **correct** (it tracks the conclusion), and induction on Deriv is the right proof technique (it IS Guard's case analysis).  The `SplitError.UnificationStuck` is Agda's elaboration choosing a coverage-check strategy that doesn't correspond to applying the elimination rule.

> Mathematically, defining a function over `Deriv` by case analysis = applying the eliminator.  One continuation per constructor.  No unification, no overlap check, no `substF`-reasoning — the constructor is the data.

The previous diagnoses were wrong:
- "De-index Deriv" — wrong; the index is correct.
- "Drop `--exact-split`" — wrong; the strictness isn't what's failing.
- "Make ruleInst's P explicit" — possibly helpful but doesn't address the core issue.

The right framing: when Agda's pattern-match elaboration hits `SplitError.UnificationStuck`, that's Agda choosing a strategy other than the eliminator.  The fix is to redirect it — e.g. write `encodeRich` directly via a manually-constructed eliminator, or use a clause arrangement that elaborates to the eliminator without coverage-check unification.

**State for next session:** the R refactor is structurally simple (it's just adding a constructor + axioms + a pattern synonym).  The Agda surface needs to be written so the existing Deriv-case-analysis functions (just `encodeRich` in BRA) elaborate via the eliminator, not via coverage-check unification.  This is an Agda-engineering question, not a mathematical one.  The principle to keep:

> Treat `SplitError.UnificationStuck` as "Agda's elaboration is doing extra work that doesn't appear in Guard's argument".  Find the Agda surface that elaborates to the eliminator directly.  Never alter the mathematics.
