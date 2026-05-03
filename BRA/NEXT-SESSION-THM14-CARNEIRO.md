# Next session prompt — Theorem 14 (Goedel II closure) via Carneiro Hilbert simulation

Read this whole file before starting.  Do not consult prior-conversation
memory; everything you need is here or in the named files.

## Goal — single success criterion

Deliver, **unconditionally**, the two Goedel II contracts that
`BRA/Thm14Abstract.agda` and `BRA/GoedelII.agda` currently take as
parameters:

```agda
constr5 : Fun1
step5   : (x : Term) ->
          Deriv ((atomic (eqn (ap1 thmT x) cG))
                  imp (atomic (eqn (ap1 thmT (ap1 constr5 x))
                                    (reify (codeFormula bot)))))
```

After this session, a closed term

```agda
godelII : Deriv Con -> Deriv bot
```

must live in a top-level Agda file (suggested: `BRA/Th14Constr5.agda`)
with **no** module parameters and **no** postulates.  It should be
producible as

```agda
module Final = BRA.GoedelII.Compose constr5 step5
godelII = Final.godelII
```

The only theorem-level inputs are:

* `r12_th  : Thm12_F1_Result thmT`  — concretely  `BRA.Thm12.thm12_F1 thmT`
  ... wait, `thmT` is not a `Fun1` in our sense (`thmT` is the th-encoder
  defined inside `BRA.Thm.ThmT`, exposed as a singular functor).  Pick
  whichever concrete provider for `r12_th` lives in the current `BRA/`
  tree (search for a top-level definition of type `Thm12_F1_Result thmT`
  or build it from `BRA.Thm12.thm12_F1` instantiated at the right
  Fun1).  Same for `r12_sub`.
* `r12_sub : Thm12_F2_Result sub`   — analogously.

Both `r12_th` and `r12_sub` must come from the existing
`BRA.Thm12.FromBridges` machinery (instantiated with the existing
`TreeEq_xeq1` / `IfLf_xeq1` closures, which `BRA/Thm12.agda` still
takes as parameters).  Where those closures live or get instantiated
is a question for `BRA/GoedelII.agda` — match the existing pattern.

**No other Theorem-12-level input** is allowed.  In particular, the
recursive `thm12_F1` / `thm12_F2` machinery enters ONLY through
`r12_th` / `r12_sub`, themselves consumed only via `thm13_F1` /
`thm13_F2`.

## The proof — Guard 1963 Theorem 14 (guard15.pdf p.16-17), faithful

Guard's argument is **five steps** under the meta-hypothesis
`H : th(x) = j`.  In our notation, `j = reify j_tree` and `cG = reify
(codeFormula G)`; Guard's `j` is our `i = reify j` (i.e. the numeral
form of the diagonal Tree).  Guard's `cor x` is our `ap1 cor x`.

```
Step 1.   H ⊢ th(D_thmT(x)) = code "th(cor x) = cG"        -- Th 13 on thmT
Step 2.        th(D_sub(i,i))    = code "sub(i,i) = cG"      -- Th 13 on sub
Step 3.   H ⊢ th(g(x))           = code "th(cor x) = sub(i,i)"
Step 4.   H ⊢ th(K(x))           = code "th(cor x) ≠ sub(i,i)"
Step 5.   H ⊢ th(constr5(x))     = code bot                  -- "0=1"
```

Step 3 is internal `axEqTrans` chained on Steps 1 + 2.
Step 4 is sb (encoded substitution) applied to the diagonal Tree `j`.
Step 5 is internal `axNeg`-style contradiction chained on Steps 3 + 4.

## Carneiro's method — the lifting strategy

`step5`'s type is an INTERNAL implication `PrAtX x imp ...`.  We will
build the meta-arrow form first (a function
`H : Deriv (PrAtX x) -> Deriv (... = code bot)`), then convert to the
internal form by **systematically lifting every step under the
hypothesis `H`** using the `S` and `K` axioms.

This is exactly Mario Carneiro's simulation of the Deduction Theorem
in Hilbert systems (see `ndw2.pdf` p.19-20 in the repo root):

> Replace the sequence ψ₁, …, ψₙ by φ → ψ₁, …, φ → ψₙ.  If ψ_k
> follows from ψ_i and ψ_j = ψ_i → ψ_k by mp, then φ → ψ_k follows
> from φ → ψ_i and φ → ψ_j = φ → (ψ_i → ψ_k) using Frege's axiom
> `(a → b → c) → (a → b) → a → c` (= our `axS`).

Concretely, every Deriv `D : Deriv Q` is replaced by its lifted form
`D' : Deriv (P imp Q)`, where `P = PrAtX x` is the Goedel-II
hypothesis.

* `liftAxiom P D` lifts a closed Deriv via `axK`.
* `liftedRuleTrans P u v w D₁ D₂` chains two lifted equality
  derivations using `axS`.
* `liftedCong1 P f u v D` lifts `cong1 f` similarly.

These are already in `BRA.Thm.EvalHelpers` (used in their doubly-lifted
form throughout `BasePair` for Theorem 12).  This session uses the
**singly-lifted** family — half the work of `BasePair` since there is
only one varying antecedent.

The meta-arrow → internal-implication conversion happens at every Deriv
in the chain.  The "underlying" hypothesis `H` is consumed exactly
once, at Step 1, by `thm13_F1 thmT r12_th x cG H` — but in the lifted
form, Step 1's image is

```agda
step1_lifted : Deriv (PrAtX x imp atomic
                 (eqn (ap1 thmT (ap1 D_thmT x))
                      (codeFTeq1Hyp thmT x cG)))
step1_lifted = ... (mp (axS _ _ _) (mp (axK _ _) (... thm13_F1 ...)))
                   ... or use a helper that abstracts the `H` slot.
```

The cleanest way: define a helper

```agda
liftThm13_F1 : (f : Fun1) (r12 : Thm12_F1_Result f)
               (x y : Term) (P : Formula) ->
   Deriv (P imp atomic (eqn (ap1 f x) y)) ->
   Deriv (P imp atomic (eqn (ap1 thmT (ap1 (Thm12_F1_Result.Df r12) x))
                            (codeFTeq1Hyp f x y)))
```

— a Carneiro-lifted version of `thm13_F1`, defined by pushing
`thm13_F1`'s body through `liftedRuleTrans` and `liftedCong1` chains
under `P`.  This is the cleanest abstraction for Step 1.

For Step 2 (closed in `H`), simply `liftAxiom (PrAtX x) step2_meta`.

## Building `constr5(x)` as a Fun1

`constr5(x)` is, by Guard's definition,

```
constr5(x) = mp_enc (K(x)) (mp_enc (g(x)) (h(x)))
```

where `mp_enc y₁ y₂ = ap2 Pair tagCode_mp (ap2 Pair y₁ y₂)`.

Each piece is itself an encoded mp / sb composition.  All sub-pieces
are **closed in x** except `D_thmT(x)` and the K(x) / g(x) outer
sb-of-x.  So as a Fun1 of x, `constr5` is built using:

* `KT t` — constant-emitting Fun1, where `t` is a closed Term.
* `Comp f g` / `Comp2 h f g` — composition.
* `cor` — the BRA-defined Fun1 that maps a Term to its numeral encoding.
* `D_thmT` — the IH Fun1 from `r12_th`.

Worked sketch (illustrative — actual builder may differ):

```agda
-- f_part : Fun1   such that  ap1 f_part x = f(x)
--                        = sb_enc (J(num_x, 1))                 -- substitute x_1 := num x
--                            (sb_enc (J(num_i, 1))              -- closed
--                              (sb_enc (J(num_j, 2)) t_term))    -- closed
--   ; where  num_x = ap1 cor x ,
--            num_i, num_j, t_term  are closed Terms.
private
  innermost_part : Term        -- closed: sb (J(num_j, 2)) t_term
  innermost_part = mkSb (mkJ num_j_T (natCode 2)) t_term

  middle_part : Term            -- closed: sb (J(num_i, 1)) innermost_part
  middle_part = mkSb (mkJ num_i_T (natCode 1)) innermost_part

  -- f_part : Fun1 such that ap1 f_part x = sb_enc (J(num x, 1)) middle_part
  f_part : Fun1
  f_part = Comp2 mkPair (KT tagCode_ruleInst)
                        (Comp2 mkPair (mkSb-J-num-of-x-builder)
                                      (KT middle_part))
```

…and similarly for `g_part`, `h_part`, `K_part`, finally
`constr5 = Comp2 mkPair (KT tagCode_mp)
              (Comp2 mkPair K_part
                            (Comp2 mkPair (KT tagCode_mp)
                                          (Comp2 mkPair g_part h_part)))`

(The exact `mkSb`, `mkJ`, `mkPair` Fun1-combinators may need to be
written; reuse existing emit_* patterns from
`BRA/Th12TreeRecInternal.agda` BasePair as a model — those build
Pair-headed Term emitters from Lift / KT / Fan / Comp2.)

## Carneiro lifting — the chain in full

Under `P = PrAtX x = atomic (eqn (ap1 thmT x) cG)`:

1. `step1_l : Deriv (P imp atomic (eqn (ap1 thmT (ap1 D_thmT x)) (codeFTeq1Hyp thmT x cG)))`
   via `liftThm13_F1 thmT r12_th x cG P (axImpRefl P)`.
   (`axImpRefl P` discharges the hypothesis "I have P" trivially under P.)

2. `step2_l : Deriv (P imp atomic (eqn (ap1 thmT (ap2 D_sub i i)) (codeFTeq2Hyp sub i i cG)))`
   via `liftAxiom P (thm13_F2 sub r12_sub i i cG subIIeqcG)`.

3. Encoded `axEqTrans` instance lifted under P:
   `t_lifted : Deriv (P imp atomic (eqn (ap1 thmT t_term) (... formula ...)))`
   built from `liftAxiom P (encode _ axEqTrans-derivation .snd)`.

4. Three sb-steps lifted under P (each using `thmTDispRuleInst_param`
   wrapped in `liftedRuleTrans` / `liftedCong1`):
   `f_step_l : Deriv (P imp atomic (eqn (ap1 thmT (ap1 f_part x)) "f-formula-of-x"))`.

5. Two mp-steps lifted under P (using `thmTDispMp` wrapped):
   `g_step_l : Deriv (P imp atomic (eqn (ap1 thmT (ap1 g_part x)) "g-formula-of-x"))`.
   The two `mp` instances chain in:
     * `step1_l` (provides "th(cor x) = cG")
     * `step2_l` (provides "sub(i,i) = cG")
     * `f_step_l` (provides the trans-axiom instance)
   to yield "th(cor x) = sub(i,i)".

6. K-step (Step 4): one sb-step on the diagonal Tree j.
   `K_step_l : Deriv (P imp atomic (eqn (ap1 thmT (ap1 K_part x)) "th(cor x) ≠ sub(i,i)"))`.

7. `t'_lifted` + h-steps + final two mp's:
   `step5 x : Deriv (P imp atomic (eqn (ap1 thmT (ap1 constr5 x)) (reify (codeFormula bot))))`.

`step5` is exactly this — a function in `(x : Term)` returning the
above Deriv.

## What's already built

* `BRA/Thm13.agda` — `thm13_F1`, `thm13_F2`, `codeFTeq1Hyp`, `codeFTeq2Hyp`.
* `BRA/Thm14Abstract.agda` — `cG`, `i`, `bot`, `Con`, `subIIeqcG`,
  `closureToG` (consumes `step5`), `godelII`.
* `BRA/GoedelII.agda` — `Compose constr5 step5` module.
* `BRA/Thm14.agda` — currently parametric in `r12_th`, `r12_sub`,
  `constr5`, `step5`; will be unchanged structurally.
* `BRA.Thm.ThmT.encode : (P : Formula) -> Deriv P -> Sigma Tree (...)`
  — produces a Tree-encoded proof-witness for any closed Deriv.  Use
  this to obtain `t_term` and `t'_term` from BRA-derivable
  rearrangements of `axEqTrans` / `axNeg`.
* `BRA.Thm.ThmT.thmTDispMp_param`, `thmTDispRuleInst_param`,
  `thmTDispAxEqTrans_param`, `thmTDispAxNeg_param` (search `BRA/Thm/ThmT.agda`
  for the exact parametric forms that take Term-level u₁/u₂ slots).
* `BRA.Thm.EvalHelpers.liftAxiom`, `liftedRuleTrans`, `liftedCong1`,
  `liftedCongL`, `liftedCongR` — singly-lifted Carneiro helpers.

## Step-by-step plan

### Step 0 — concrete `r12_th`, `r12_sub`

Locate or build `r12_th : Thm12_F1_Result thmT` and
`r12_sub : Thm12_F2_Result sub`.  `BRA.Thm12.thm12_F2 sub` should
yield `r12_sub` directly.  For `r12_th`: `thmT` is a Fun1 (defined
in `BRA.Thm.ThmT`), so `BRA.Thm12.thm12_F1 thmT` produces it — but
verify that `thmT` is actually a constructor pattern that
`thm12_F1` matches on (it might be `Comp` of something).  If `thmT`
is a *composite* Fun1, walk the composition tree applying `thm12_F1`
recursively at each layer.

These two values are the only Theorem-12-level inputs.

### Step 1 — `t_term` and `t'_term`

Build:

```agda
t_deriv : Deriv (atomic (eqn (var zero) (var (suc (suc zero))))
                   imp (atomic (eqn (var (suc zero)) (var (suc (suc zero))))
                          imp atomic (eqn (var zero) (var (suc zero)))))
t_deriv = ... (using axEqTrans / axEqSym / axImpRefl chains)

t_pack : Sigma Tree (\ y -> Deriv (atomic (eqn (ap1 thmT (reify y))
                                               (reify (codeFormula t_formula)))))
t_pack = encode t_formula t_deriv
  where t_formula = ... (the formula above)

t_term : Term
t_term = reify (fst t_pack)

t_witness : Deriv (atomic (eqn (ap1 thmT t_term) (reify (codeFormula t_formula))))
t_witness = snd t_pack
```

Same for `t'`:

```agda
t'_deriv : Deriv (atomic (eqn (var zero) (var (suc zero)))
                   imp (not (atomic (eqn (var zero) (var (suc zero))))
                          imp atomic (eqn O (reify-codeBot ... "0=1"))))
t'_deriv = ... (using axNeg / axExFalso)
```

### Step 2 — `liftThm13_F1` helper

Carneiro-lifted Theorem 13 on singular functors:

```agda
liftThm13_F1 : (f : Fun1) (r12 : Thm12_F1_Result f) (x y : Term)
               (P : Formula) ->
   Deriv (P imp atomic (eqn (ap1 f x) y)) ->
   Deriv (P imp atomic (eqn (ap1 thmT (ap1 (Thm12_F1_Result.Df r12) x))
                            (codeFTeq1Hyp f x y)))
liftThm13_F1 f r12 x y P lifted_hyp = ...
   -- thm13_F1's body is:
   --   ruleTrans (proof_f x) (congR Pair lhs_part (cong1 cor hyp))
   -- Lift each step under P:
   --   liftAxiom P (proof_f x)                           (closed in P)
   --   liftedCong1 P cor (... lifted_hyp ...)
   --   liftedCongR P Pair lhs_part (...)
   --   liftedRuleTrans P (...)  (...)
```

Pattern: each `ruleTrans / cong1 / congR` becomes a `liftedRuleTrans /
liftedCong1 / liftedCongR` under `P`, with the `hyp`-using leaf using
`lifted_hyp` directly.  ~30-50 LoC.

### Step 3 — Steps 1, 2, 3 of Guard (Step 3 is internal mp / sb)

Build `step1_l`, `step2_l`, `f_step_l`, `g_step_l` per the chain above.
Each is ~50-100 LoC.

### Step 4 — Step 4 of Guard (the diagonal sb)

Build `K_part : Fun1` such that `ap1 K_part x` is the encoded form of
`sb (J(num x, 1)) j` where `j` is the diagonal Tree.

The actual `j` Tree is `BRA.Thm11Diagonal.Diagonal.j` — a closed
Tree whose reify is `i`.  Convert to a Term via `reify j`.  Then
`K_part x = encoded sb step on (reify j)`.

Then `K_step_l : Deriv (P imp ...)` ~100 LoC.

### Step 5 — Step 5 of Guard

Build `t'_lifted`, `h_step_l` (two sb-steps), and the final two mp's
producing `constr5(x)` and `step5 x`.

`constr5 : Fun1` is the explicit Fun1 builder.

### Step 6 — wire up `godelII`

Final file:

```agda
module BRA.Th14Constr5 where

  -- ... imports ...

  r12_th  : Thm12_F1_Result thmT
  r12_th  = ... (Step 0)

  r12_sub : Thm12_F2_Result sub
  r12_sub = ... (Step 0)

  constr5 : Fun1
  constr5 = ... (Step 5)

  step5 : (x : Term) ->
          Deriv (PrAtX x imp atomic (eqn (ap1 thmT (ap1 constr5 x))
                                         (reify (codeFormula bot))))
  step5 = ... (Steps 1-5 lifted chain)

  module Final = BRA.GoedelII.Compose constr5 step5

  godelII : Deriv Con -> Deriv bot
  godelII = Final.godelII
```

## Verification targets

All five must stay green throughout.  Run via `~/.cabal/bin/agda-2.9.0`:

* `BRA/Thm12.agda`
* `BRA/Thm13.agda`
* `BRA/Thm14Abstract.agda`
* `BRA/GoedelII.agda`
* `BRA/Th14Constr5.agda` (new)

## Constraints

* ASCII only.  `{-# OPTIONS --safe --without-K --exact-split #-}` on
  every file.
* No postulates.  No holes.  No `with`-abstraction.  No dot patterns.
* Do not change `Thm12_F1_Result` / `Thm12_F2_Result` types.
* Do not change `Thm14Abstract.GodelII`'s contract types.
* Do not introduce new Deriv axioms.  Everything is built from
  existing `axS`, `axK`, `axEqTrans`, `axEqSym`, `axEqRefl`, `axNeg`,
  `axContrapos`, `mp`, `ruleInst`, `ruleTrans`, `cong1`, `congL`,
  `congR`.

## Pitfalls

* **`encode` is closed-Deriv-only.**  `t_deriv` and `t'_deriv` MUST
  not depend on free meta-Term arguments.  They are pure tautologies
  in the implicational fragment + equality.

* **`thmTDispMp_param`'s shape obligation.**  `thmTDispMp_param`
  requires a derivation that the Fst of the encoded mp body is a
  certain Pair-headed term.  This is `axFst` on the leading
  `tagCode_mp`.  Same pattern as Y1_shape, Y2_shape in BasePair.

* **Pair-encoding `mp_enc` and `sb_enc` distinctions.**  Be careful
  to use the right tag (`tagCode_mp`, `tagCode_ruleInst`,
  `tagCode_axEqTrans`, `tagCode_axNeg`) for each.  Search
  `BRA.Thm.ThmT` for the canonical name.

* **`reify (codeFormula bot)` vs `mkEqT ...`** — `bot` is `atomic
  (eqn O (... "1" ...))` (= "0 = 1"); make sure to compute `codeFormula`
  through the unfolding rather than fighting reify-on-an-equation
  walk.  See how `Thm14Abstract.subIIeqcG` handles this.

* **Singly-lifted dispatchers may not exist for every operator.**  If
  needed, define them in `BRA.Thm.EvalHelpers` by mirroring the
  doubly-lifted versions with `P` (one Formula) instead of `(P1, P2)`.
  Most basic ones (`liftAxiom`, `liftedRuleTrans`, `liftedCong1`,
  `liftedCongL`, `liftedCongR`) already exist.

* **The numeral `j`** (diagonal Tree) lives in
  `BRA.Thm11Diagonal.Diagonal`.  Reify with `reify j` to get a Term.
  Note `i = reify j` is already exposed by `BRA.Thm14Abstract`.

* **`num x` vs `cor x`.**  In Guard, `num x` is "the Gödel number of
  the numeral whose value is x".  In our setting `cor : Fun1` plays
  this role: `ap1 cor x` is a Term that, when x is a numeral, equals
  the encoded form of x.  Use `ap1 cor x` wherever Guard writes
  `num x`.

## Files to read first

1. **This file.**
2. `BRA/Thm14.agda` — current parametric Thm 14 setup.
3. `BRA/Thm14Abstract.agda` — closure logic; do not duplicate.
4. `BRA/Thm13.agda` — `thm13_F1`, `thm13_F2`, `codeFTeq1Hyp`, `codeFTeq2Hyp`.
5. `BRA/GoedelII.agda` — `Compose` module (the last layer).
6. `BRA/Thm/ThmT.agda` — search for `thmTDispMp_param`,
   `thmTDispRuleInst_param`, `thmTDispAxEqTrans_param`,
   `thmTDispAxNeg_param`, `encode`.
7. `BRA/Thm/EvalHelpers.agda` — `liftAxiom`, `liftedRuleTrans`,
   `liftedCong1`, `liftedCongL`, `liftedCongR`.
8. `guard15.pdf` p.16-17 — Guard's actual Theorem 14 proof.
9. `ndw2.pdf` p.19-20 — Carneiro's deduction-theorem simulation
   (the conceptual map for the lifting strategy).
10. `BRA/Th12TreeRecInternal.agda` `BasePair` module
    (lines ~1450-1780) — the doubly-lifted pattern; this session
    uses the singly-lifted analog, half the work.

## End-of-session deliverable

```bash
echo "=== godelII type check ==="
~/.cabal/bin/agda-2.9.0 BRA/Th14Constr5.agda; echo BUILD=$?
echo
echo "=== godelII signature ==="
grep -n "^  godelII " BRA/Th14Constr5.agda
echo
echo "=== no postulates / holes ==="
grep -E "postulate|\?\s*$" BRA/Th14Constr5.agda || echo "(none — clean!)"
echo
echo "=== full chain ==="
~/.cabal/bin/agda-2.9.0 BRA/Thm12.agda;        echo T12=$?
~/.cabal/bin/agda-2.9.0 BRA/Thm13.agda;        echo T13=$?
~/.cabal/bin/agda-2.9.0 BRA/Thm14Abstract.agda; echo T14A=$?
~/.cabal/bin/agda-2.9.0 BRA/GoedelII.agda;     echo G2=$?
~/.cabal/bin/agda-2.9.0 BRA/Th14Constr5.agda;  echo TC=$?
```

Expected: all builds exit 0, `godelII : Deriv Con -> Deriv bot` is a
closed term.  This closes Goedel II in BRA.

## Why Carneiro's method is the right choice

The five Theorem-14 steps form a sequence of equality / negation
derivations under the single hypothesis `H : th(x) = cG` (= Guard's
`th(x) = j`).  Carneiro's simulation tells us: rather than work in
natural-deduction style with a discharged assumption, we lift every
intermediate `Deriv Q` to `Deriv (PrAtX x imp Q)` and use `axS` (=
Frege's `(a→b→c)→(a→b)→a→c`) to push mp under the antecedent.

The Theorem 12 BasePair module already used the **doubly-lifted**
version (two varying antecedents `Pv1`, `Pv2`).  Theorem 14 is the
**singly-lifted** version (one antecedent `PrAtX x`) — half the
combinator boilerplate per step.  The two pre-existing lifted-helper
families in `BRA.Thm.EvalHelpers` (`liftAxiom`/`liftedRuleTrans`/
`liftedCong*` and their `*Two` doubled variants) make this entirely
mechanical once you have the meta-arrow chain.

The conversion meta-arrow → internal-implication is the only
non-mechanical part: at the leaf `step1_meta_at`, we have a function
of type `Deriv (eqn (th x) cG) -> Deriv (...)`.  Carneiro's recipe is
to provide that function with `axImpRefl P` (= "the assumption proves
itself") and then lift.  This is what `liftThm13_F1` in Step 2 above
encapsulates.
