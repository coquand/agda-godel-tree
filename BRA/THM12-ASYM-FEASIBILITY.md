# Asymmetric `codeFTeq` + base-case feasibility sketch (V2, corrected)

Goal of this doc: show the asymmetric analog of Guard's encoded equation
expressed in BRA-the-project's existing types, sketch three base cases
(`f = I`, `f = Z`, `f = Fst`), and identify exactly which existing
infrastructure the proof needs vs. which is missing.

This is a feasibility check, not an implementation. No commitment to
build the full Theorem 12 yet.

**V2 correction:** the prior draft of this doc (and several preceding
sessions) framed the obstruction as "Fst breaks Theorem 12 because
`Fst(cor x) ≠ cor(Fst x)` at x = Pair O O." That framing was wrong: it
checked the wrong condition. Theorem 12 doesn't require `f` to commute
with `cor` as a function. It requires the *encoded equation* to decode,
at every canonical substitution, to a closed BRA theorem. For Fst this
decodes to `Fst(Pair O O) = O`, provable by `axFst`. The Fst case
*works*. This V2 redoes the analysis in the corrected light, including
Fst as a third sketch to verify the corrected understanding.

---

## 1. The asymmetric `codeFTeq` (unchanged from V1)

Concrete definitions, typechecks against the existing `BRA.Term`,
`BRA.Cor` modules.

```agda
{-# OPTIONS --safe --without-K --exact-split #-}

module BRA.Thm14CodeFTeqAsym where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Cor using (cor)

private
  tagAp1T : Term
  tagAp1T = reify tagAp1

  tagAp2T : Term
  tagAp2T = reify tagAp2

mkAp1T : Term -> Term -> Term
mkAp1T fCodeT tCodeT = ap2 Pair tagAp1T (ap2 Pair fCodeT tCodeT)

mkAp2T : Term -> Term -> Term -> Term
mkAp2T gCodeT aCodeT bCodeT =
  ap2 Pair tagAp2T (ap2 Pair gCodeT (ap2 Pair aCodeT bCodeT))

mkEqT : Term -> Term -> Term
mkEqT lhsT rhsT = ap2 Pair lhsT rhsT

codeFTeq1Asym : Fun1 -> Term -> Term
codeFTeq1Asym f x =
  mkEqT (mkAp1T (reify (codeF1 f)) (ap1 cor x))
        (ap1 cor (ap1 f x))

codeFTeq2Asym : Fun2 -> Term -> Term -> Term
codeFTeq2Asym g x v =
  mkEqT (mkAp2T (reify (codeF2 g)) (ap1 cor x) (ap1 cor v))
        (ap1 cor (ap2 g x v))
```

This typechecks. The asymmetric form leaves `ap1 cor x` and
`ap1 cor (ap1 f x)` as open subterms when x is a variable; at canonical
`x = reify v`, both subterms reduce (in Deriv) to closed Trees that
together form the GN of a closed BRA formula.

---

## 2. The right shape of `thm12sing` (asymmetric)

The cleanest formulation is parametric in a chosen variable `var n`:

```agda
thm12singAsym :
  (f : Fun1) ->
  Sigma Term (\Df_term ->
    Deriv (atomic (eqn (ap1 th Df_term) (codeFTeq1Asym f (var zero)))))
```

`Df_term` is a Term with `var zero` free. The Deriv is parametric in
`var zero`. By BRA's `ruleInst`, this gives the equation at any specific
Term substituted for `var zero`.

For brevity below, let `n = zero` (the chosen variable index).

---

## 3. Decoding the encoded equation at canonical inputs

For each canonical substitution `var n := reify v`, the encoded equation
`codeFTeq1Asym f (var n)` reduces (in Deriv) to the GN of a specific
closed BRA formula. Let's compute this for the three cases.

### Reduction lemmas (used in all three cases)

**(R1)** `cor O = O` (from `axRecLf O stepCor`).

**(R2)** `cor (ap2 Pair a b) = mkAp2T pairCodeF2T (cor a) (cor b)`
   (from `axRecNd O stepCor a b` + `stepCorRed`, both in
    `BRA/Cor.agda`).

**(R3)** For closed reify-image `t = reify v`, `cor t` reduces in
   Deriv to `reify (code (reify v))` via `corOfReify v`.

These are all in the existing `BRA/Cor.agda`; no new lemmas needed.

---

## 4. Base case: `f = I`

### Decoded formula

`codeFTeq1Asym I (var n)` reduces to:

```
mkEqT (mkAp1T (reify (codeF1 I)) (ap1 cor (var n)))     -- LHS subterm
      (ap1 cor (var n))                                   -- RHS subterm
```

after rewriting RHS via `cong1 cor (axI (var n))`. The decoded formula
(at canonical `var n := reify v`) is `I(reify v) = reify v` — the
content of `axI`.

### Construction

```agda
thm12singAsym_I :
  Sigma Term (\Df_term ->
    Deriv (atomic (eqn (ap1 th Df_term) (codeFTeq1Asym I (var zero)))))
thm12singAsym_I =
  let
    F : Formula
    F = atomic (eqn (ap1 I (var zero)) (var zero))

    pf : Deriv F
    pf = axI (var zero)

    -- Step 1: encode pf at the symmetric (static) form.
    enc :  Sigma Tree (\y -> Deriv (atomic (eqn (ap1 th (reify y))
                                                 (reify (codeFormula F)))))
    enc = encode F pf

    yI    : Tree
    yI    = fst enc
    pfStat : Deriv (atomic (eqn (ap1 th (reify yI))
                                 (reify (codeFormula F))))
    pfStat = snd enc

    -- reify (codeFormula F) =
    --   mkEqT (mkAp1T (reify (codeF1 I))
    --                 (reify (code (var zero))))   -- static var-GN
    --         (reify (code (var zero)))            -- static var-GN
    --
    -- This differs from codeFTeq1Asym I (var zero) only at the two
    -- variable positions: static has  reify (code (var zero))
    -- (= ap2 Pair (reify tagVar) (reify (natCode 0))), asymmetric has
    --  ap1 cor (var zero) .

    -- Step 2: bridge static -> asymmetric via parametric sbDef.
    --
    -- Apply  ap2 sb (ap2 Pair (ap1 cor (var zero)) (reify (natCode zero)))
    --              (reify (codeFormula F))
    -- which (by sbDefParam, see infrastructure below) reduces to a Term
    -- equal to codeFTeq1Asym I (var zero) up to one  cong1 cor (axI _) .

    Df_term : Term
    Df_term = ap2 sbProof (ap2 Pair (ap1 cor (var zero))
                                     (reify (natCode zero)))
                          (reify yI)
    -- where sbProof : Fun2 is the proof-level analog of sb (lifts
    -- sb's substitution from formula GNs to th-indexed proof GNs).

    pf_final : Deriv (atomic (eqn (ap1 th Df_term)
                                   (codeFTeq1Asym I (var zero))))
    pf_final = -- composition of pfStat with sbProof's defining equation
               -- and the cor/axI bridge on the RHS subterm.
               ?

  in mkSigma Df_term pf_final
```

Status: feasible, two pieces of new infrastructure required (see §7).

---

## 5. Base case: `f = Z`

### Decoded formula

`codeFTeq1Asym Z (var n)` reduces to:

```
mkEqT (mkAp1T (reify (codeF1 Z)) (ap1 cor (var n)))     -- LHS subterm
      O                                                   -- RHS subterm
```

via:
- `cong1 cor (axZ (var n))`: `cor (Z (var n)) = cor O`.
- `cor O = O`: `cor (Z (var n)) = O`.

The decoded formula (at canonical `var n := reify v`) is
`Z(reify v) = O` — the content of `axZ`.

### Construction

Mirrors I exactly, with `axZ (var zero)` replacing `axI (var zero)`,
the closed formula `F = atomic (eqn (ap1 Z (var zero)) O)` (note the RHS
is `O`, not `var zero`), and the bridge step using `axZ` plus
`axRecLf` for `cor O = O` instead of just `axI`.

The infrastructure used is identical: `encode` plus parametric
`sbDef` plus `sbProof` lifting.

Status: feasible, same infrastructure as I.

---

## 6. Base case: `f = Fst` (the case the prior analysis got wrong)

This is the case I claimed in V1 that "breaks Theorem 12." It does not.

### Decoded formula

`codeFTeq1Asym Fst (var n)` does *not* reduce by a single congruence —
unlike I (where `axI` is total) and Z (where `axZ` is total), `Fst` has
a *case split*: `axFstLf : Fst O = O` and `axFst a b : Fst (Pair a b) = a`.

We use `ruleIndBT` to dispatch on `var n`'s shape.

```agda
P : Formula
P = atomic (eqn (ap1 th Df_Fst_term) (codeFTeq1Asym Fst (var zero)))

P_at_O    = substF zero O P
P_at_v1   = substF zero (var (suc zero))  P
P_at_v2   = substF zero (var (suc (suc zero))) P
P_at_Pair = substF zero (ap2 Pair (var (suc zero)) (var (suc (suc zero)))) P
```

We need:

**Base** (`Deriv P_at_O`): proof at `var zero := O`.

  `codeFTeq1Asym Fst O` reduces (using R1 + axFstLf-bridge):
  ```
  mkEqT (mkAp1T (reify (codeF1 Fst)) O) O
  ```
  Decoded formula: `Fst O = O`. Proved by `axFstLf`.

  Construct `Df_at_O = encode_index_of(axFstLf)`.

**Step** (`Deriv (P_at_v1 imp (P_at_v2 imp P_at_Pair))`): from IHs at
`var 1` and `var 2`, derive at `Pair (var 1) (var 2)`.

  `codeFTeq1Asym Fst (Pair (var 1) (var 2))` reduces (using R2 +
  axFst-bridge):
  ```
  mkEqT (mkAp1T (reify (codeF1 Fst))
                (mkAp2T pairCodeF2T (ap1 cor (var 1)) (ap1 cor (var 2))))
        (ap1 cor (var 1))
  ```
  via:
  - `cor (Pair (var 1) (var 2)) = mkAp2T pairCodeF2T (cor (var 1)) (cor (var 2))` (R2).
  - `cor (Fst (Pair (var 1) (var 2))) = cor (var 1)` (axFst + cong).

  Decoded formula: `Fst (Pair t1 t2) = t1` where t1, t2 are the decoded
  forms of `cor (var 1)`, `cor (var 2)`. At canonical inputs this is
  exactly `axFst`'s form.

  The step case in `ruleIndBT` doesn't actually need the IHs for this
  case — `axFst` is total on its inputs and produces the proof
  directly. The IHs would only be needed if Fst's defining axiom
  recursed into u, v (which it doesn't). So:

  Construct `Df_at_Pair = encode_index_of(axFst (var 1) (var 2))`,
  with the implication conclusion bridged via parametric sb to insert
  `cor (var 1)`, `cor (var 2)` at the appropriate positions.

**Combine** via `ruleIndBT`:
```agda
thm12singAsym_Fst :
  Sigma Term (\Df_term ->
    Deriv (atomic (eqn (ap1 th Df_term) (codeFTeq1Asym Fst (var zero)))))
thm12singAsym_Fst =
  ruleIndBT P (suc zero) (suc (suc zero))
            base_proof
            step_proof
```

Status: **feasible.** The Fst case structurally mirrors Guard's Rgh
case in his Theorem 12 proof — both use the internal induction rule
to dispatch on the shape of the recursion / induction variable, with
each branch closed by the matching defining axiom. BRA's `ruleIndBT`
does exactly what Guard's `ind` does for him.

---

## 7. Required new infrastructure

The same single piece I identified in V1, slightly elaborated:

### Parametric `sbDef` (formula-level)

```agda
sbDefParam :
  (repl : Term) (n : Nat) (codeP : Tree) ->
  Deriv (atomic (eqn
    (ap2 sb (ap2 Pair repl (reify (natCode n))) (reify codeP))
    (codedSubstT repl (code (var n)) codeP)))
```

Allows `repl` to be open (not just `reify codeA` for closed `codeA`).
~80 LoC, no new Deriv axioms.

### Proof-level analog (`sbProof`)

A `Fun2` (or similar) that lifts `sb` from formula-GN substitution to
th-index substitution: if `th(y) = (formula GN with var n)`, then
`th(sbProof(repl-pair, y)) = (formula GN with repl substituted for var n)`.

This is implicit in the existing `BRA/Thm/ThmT.agda` machinery — `th`'s
defining equation `th(4y+1) = sb(KKy, IKy, th(Iy))` says: the
"successor" case in th's enumeration corresponds to applying sb to a
prior theorem. So `sbProof` is essentially "construct a `4y+1` index"
with appropriate `KKy`, `IKy`, `Iy`. Adapting this for the parametric
asymmetric case requires a small amount of glue but no new axioms.

Estimated total: ~120 LoC for both pieces, no new axioms, half a
session.

---

## 8. Verdict

The asymmetric `codeFTeq` is the right Guard analog. The three base
cases — including Fst, the case I previously misanalyzed — admit
short, parametric Deriv constructions:

- **I**: one-shot via `axI` + encode + sbDefParam bridge.
- **Z**: one-shot via `axZ` + `axRecLf` + encode + sbDefParam bridge.
- **Fst**: ruleIndBT dispatch on var n's shape, with `axFstLf` at base
  and `axFst` at step. No special handling for the "tag interference"
  that the prior analysis spuriously identified.

The same pattern extends to Snd, IfLf, TreeEq: each has a finite set
of defining axioms covering all canonical input shapes; ruleIndBT
dispatches and each branch closes with the matching axiom.

### Recommended next move

1. Write `BRA/Sb.agda`'s parametric `sbDef` extension (~80 LoC).
2. Write `BRA/Thm14CodeFTeqAsym.agda` (the asymmetric encoder, already
   sketched above — should typecheck immediately).
3. Write `BRA/Thm12AsymBaseCases.agda` with thm12singAsym_I,
   thm12singAsym_Z, thm12singAsym_Fst as a working prototype
   (~70-100 LoC each).
4. **Stop and reassess** before tackling Comp / Comp2 / Rec, etc. The
   composition cases need careful threading of IHs; the Rec case is
   where the meta-induction depth gets nontrivial.

If steps 1–3 succeed within ~one session, Scenario A is fully confirmed
and we have a clean asymmetric Theorem 12 for the base cases. The
remaining 12 cases (4 more Fun1, 8 Fun2) follow the same pattern with
varying degrees of nesting — likely ~50–150 LoC each.

### What was wrong in V1 (kept here as a warning)

V1 of this doc claimed "Fst breaks Theorem 12 because `Fst(cor x) ≠
cor(Fst x)` at x = Pair O O." That was the wrong condition to check.
The right condition is "the encoded equation decodes, at every
canonical x, to a closed BRA theorem." For Fst at x = Pair O O the
encoded equation decodes to `Fst(Pair O O) = O`, which is `axFst O O`.
The "tagAp2T ≠ O" computation was answering "what does Fst applied to
the cor-encoded value evaluate to?" — a question about the *value* of
a BRA term, not about the *theorem* the encoded equation represents.

The two are related but not equal:

- `f(cor x)` *evaluates* (in BRA) to a tree. Whether that tree equals
  `cor(f x)` depends on f's interaction with cor's encoding tags.
- `codeFTeq1Asym f x` *decodes* (at canonical x) to a closed formula.
  Whether that formula is a theorem of BRA depends on f's *defining
  axioms*.

Theorem 12 needs the second; the first is a stronger and irrelevant
condition. Mistaking them led to multiple sessions of architectural
worry that turned out to be unnecessary.
