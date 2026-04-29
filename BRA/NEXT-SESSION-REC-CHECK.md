# Next session: verify the Rec case of asymmetric Theorem 12

## Goal

Build a concrete, typechecking, postulate-free Agda proof of the asymmetric
Theorem 12 at `f = Rec z s` for a CONCRETE `z` and `s`, parametric in
`x : Term`.  The output is one new file, e.g. `BRA/Thm12RecCheck.agda`.

The point is **architectural validation**: prove (or refute) that the
"`D_Rec_zs = Rec z' s'`" construction actually carries through end-to-end.
Mathematical analysis in the previous session said it should, but the
detailed `s'` Fun2 expression and the chain composition were never written.

If this typechecks, the Rec case for Theorem 12 is settled (modulo
generalisation to opaque `z, s`).  If it fails, identify the exact
obstruction.

## Settled architectural conclusions (do not re-litigate)

These were worked out in the prior session; trust them, don't redebate:

1. **Asymmetric formulation is required.**  Symmetric Theorem 12 collapses
   to `encode(axRefl)` and is vacuous for Gödel II.  See
   `feedback_no_symmetric_thm12.md`.

2. **Theorem 12 must be parametric in `x : Term` (not just at closed
   Trees).**  Theorem 14 step 1 (`th(x) = j ⊃ th(Dth(x)) = '...'`)
   needs Theorem 12 at `f = th` parametrically in `x`.  Tree-input
   formulation is insufficient downstream.  See guard15.pdf p.17.

3. **`axInstReplace : Deriv (P imp substF n t P)` is UNSOUND.**  Concrete
   counterexample: `P = atomic (eqn O (var 0))`, `t = Pair O O`.  Don't
   add it.  See comment block in `BRA/Thm12/TreeEqNN.agda` lines 159–195.

4. **Primitive `ruleIndBT` is sound as stated, no freshness side
   condition needed.**  When `v1` or `v2` is free in `P`, the premises
   themselves filter out unsound cases via BRA's consistency.  No
   `FreshIn` predicate, no `ruleIndBT'` derived rule.

5. **Cross-IH structural circularity for Rec is resolved by
   `D_Rec_zs = Rec z' s'`.**  The recursive sub-applications
   `D_Rec_zs a` and `D_Rec_zs b` appear automatically in the second
   argument to `s'` via `axRecNd`.  `s'` itself is a closed Fun2 with
   no `D_Rec_zs` self-reference.  This is what we want to verify.

6. **The step Deriv for `ruleIndBT` is built via Mendelson-style SKI
   internalisation** (axK + axS + mp) of a meta-arrow
   `(d_v1 d_v2 → chain ...)`.  Sound iff the meta-arrow doesn't
   `ruleInst` on `v1` or `v2` internally; for our chain (which uses
   only dispatchers like `parDispRuleTrans`, `parDispCong*`,
   `parDispAxRecNd`), this side condition is satisfied.  Conservativity
   of derived rules: if it typechecks, it's sound.

7. **TreeEq remains a separate open problem** (its diagonal recursion
   on two arguments isn't directly expressible via Rec/RecP combinators).
   IGNORE TreeEq this session — focus on Rec only.

## What to build

**File**: `BRA/Thm12RecCheck.agda`.

**Concrete instance**: pick `z = O` and a simple closed `s : Fun2`.
Recommended: `s = Snd`, giving `Rec O Snd`:
- `(Rec O Snd) O = O` (by axRecLf).
- `(Rec O Snd) (Pair a b) = Snd (Pair a b) (Pair (Rec O Snd a) (Rec O Snd b)) = Pair (Rec O Snd a) (Rec O Snd b)` (by axRecNd + axSnd).

This is the simplest non-trivial recursive functor.  All closures are
definitional (no opaque parameters).

**Targets in the file**:

```agda
D_Rec_OS : Fun1
D_Rec_OS = Rec z' s'    -- where z', s' are CONCRETE expressions to design

codeFTeq1_RecOS : Term -> Term
codeFTeq1_RecOS x = codeFTeq1Asym (Rec O Snd) x

D_correct_RecOS_O :
  Deriv (atomic (eqn (ap1 thmT (ap1 D_Rec_OS O)) (codeFTeq1_RecOS O)))

D_correct_RecOS_Nd : (a b : Term) ->
  Deriv (atomic (eqn (ap1 thmT (ap1 D_Rec_OS a)) (codeFTeq1_RecOS a))) ->
  Deriv (atomic (eqn (ap1 thmT (ap1 D_Rec_OS b)) (codeFTeq1_RecOS b))) ->
  Deriv (atomic (eqn (ap1 thmT (ap1 D_Rec_OS (ap2 Pair a b)))
                     (codeFTeq1_RecOS (ap2 Pair a b))))

D_correct_RecOS : (x : Term) ->
  Deriv (atomic (eqn (ap1 thmT (ap1 D_Rec_OS x)) (codeFTeq1_RecOS x)))
-- Built via ruleIndBT + axK / axS / mp internalisation of D_correct_RecOS_Nd.
```

**Constraints**:
- No `postulate`.
- No new Deriv axioms.
- No `axInstReplace`, no `ruleIndBT'`, no `FreshIn` predicate.
- Use existing infrastructure: `BRA.Deriv`, `BRA.Cor`, `BRA.Thm.ThmT`,
  `BRA.Thm14CodeFTeqAsym`, `BRA.Thm12.Param.AxRecLf`,
  `BRA.Thm12.Param.AxRecNd`, `BRA.Thm12.Param.RuleTrans`,
  `BRA.Thm12.Param.Cong1` etc.

## The hard part: the encoded chain at Pair case

This section spells out the chain `D_correct_RecOS_Nd` must produce.

### Load-bearing reduction lemma (from BRA/Cor.agda)

`cor (Pair a b)` does NOT reduce to `Pair (cor a) (cor b)`.  It reduces
to the encoded form:

```
cor (Pair a b)  =  mkAp2T pairCodeF2T (cor a) (cor b)
                =  Pair tagAp2T (Pair pairCodeF2T (Pair (cor a) (cor b)))
```

via `axRecNd O stepCor a b` + `stepCorRed (Pair a b) (Pair (cor a) (cor b))`,
both already in `BRA/Cor.agda`.  This is THE bridge that translates between
the BRA-value-level recursion (Rec applied to a Pair) and the encoded-level
substitution (Rec-encoded applied at the encoded Pair).

### Chain endpoints

Goal at `x = Pair a b`:

```
LHS_target = mkAp1T (codeF1 (Rec O Snd)) (cor (Pair a b))
RHS_target = cor (ap1 (Rec O Snd) (Pair a b))
codeFTeq1_RecOS (Pair a b) = mkEqT LHS_target RHS_target
```

Need a Term `Y` such that `thmT(Y) = mkEqT LHS_target RHS_target`.

### Chain steps (sketch — verify each in Agda)

For the Pair-case chain, six steps roughly.  Let `cf_RecOS = codeF1 (Rec O Snd)`.

**Step 1**: `parDispAxRecNd O (codeF2 Snd) (cor a) (cor b)` gives
encoded `axRecNd` at substituents `(cor a, cor b)`:

```
y1_lhs = mkAp1T cf_RecOS (mkAp2T pairCodeF2T (cor a) (cor b))
       = mkAp1T cf_RecOS (cor (Pair a b))     -- by cor reduction above
y1_rhs = mkAp2T (codeF2 Snd) (mkAp2T pairCodeF2T (cor a) (cor b))
                              (mkAp2T pairCodeF2T y1_pf_a y1_pf_b)
  where
    y1_pf_a = mkAp1T cf_RecOS (cor a)         -- encoded "Rec O Snd at cor a"
    y1_pf_b = mkAp1T cf_RecOS (cor b)         -- encoded "Rec O Snd at cor b"
```

So step 1 encodes "Rec O Snd applied at encoded-Pair = Snd of (encoded-Pair)
and (Pair of encoded-Rec-applications)".  This is `axRecNd` at the encoded
level — it produces the recursive sub-applications as ENCODED FORMS, not as
cor-of-recursion.

**Step 2**: cross-IH at `a` bridges `y1_pf_a → cor (Rec O Snd a)`.  This is
literally the codeFTeq1Asym at `a` — i.e., `D_correct_RecOS a` (the Deriv
input from ruleIndBT's IH at `v1`).  Use `parDispCong*` to lift this bridge
into the chain's ambient context (lifted through Snd at a's position).

**Step 3**: cross-IH at `b`, similarly via the other ruleIndBT IH.

After steps 2-3, the encoded RHS becomes:
```
mkAp2T (codeF2 Snd) (cor (Pair a b)) (mkAp2T pairCodeF2T (cor (Rec O Snd a))
                                                          (cor (Rec O Snd b)))
```
(LHS subterm of the Snd application bridged via cor reduction, sub-args
bridged via cross-IHs.)

**Step 4 — the `s = Snd` Theorem 12 instance** (NEW gotcha — see below):
The chain still has `Snd` applied to encoded-form arguments, not in cor form.
We need to fold Snd application into a cor.  Specifically, we need an
encoded equation
```
mkAp2T (codeF2 Snd) (cor X) (cor Y)  =  cor (ap2 Snd X Y)
```
at appropriate `X, Y`.  This IS Theorem 12 at `f = Snd` (binary).
**Use `thm12_Snd_pair_shape` from `BRA/Thm12AsymCases.agda`** at
`X = Pair a b`, `Y = Pair (Rec O Snd a) (Rec O Snd b)`.  Note: that
file's `thm12_Snd_pair_shape` takes parameters `v1 v2 : Nat` and
provides Theorem 12 at the shape `Snd (Pair v1 v2)` — singulary form.
You may need the binary form (`thm12_Snd_pair_shape` doesn't directly
match; CHECK whether the singulary case applied at a packed Pair
arguments suffices, or whether a separate `Snd`-on-Pair-Pair instance
is required).

**Step 5**: cong on cor — bridges
```
cor (ap2 Snd (Pair a b) (Pair (Rec O Snd a) (Rec O Snd b)))
   = cor (Pair (Rec O Snd a) (Rec O Snd b))            -- by axSnd + cong1 cor
```
Direct Deriv composition at the BRA level (not encoded).

**Step 6 — the final external bridge**:  apply `cong1 cor (ruleSym (axRecNd))`
to bridge from `cor (Snd ...)` to `cor (ap1 (Rec O Snd) (Pair a b))`.

The whole chain composes via `parDispRuleTrans` repeatedly to thread
through the encoded equations.

### s' construction

`s' : Fun2` takes `(Pair a b, Pair pf_a pf_b)` and produces the chain
Term `Y`.  Build `s'` as a `Fan`-of-`KT`-tagged-combinator tree that:
1. Extracts `a, b` from first arg via `Lift (Comp Fst Fst)`, `Lift (Comp Snd Fst)` etc.
2. Extracts `pf_a, pf_b` from second arg similarly.
3. Stamps in the various `tagCode_*` constants via `KT`.
4. Assembles them into the chain Term via nested `Fan`/`Pair` combinators.

This is mechanical but tedious; pattern from `BRA/Thm12/Parts/Lift.agda`'s
`D2_Lift_f` construction (its `lift_part` Fun2 is a worked example).
Estimated 80–120 LoC for `s'` itself + 50–80 LoC for `D_Rec_OS_reduce_Nd`
showing combinator reduction matches the chain Term.

### Gotcha — Theorem 12 at the inner `s = Snd`

The chain at step 4 invokes Theorem 12 at the SUB-FUNCTOR `s` (here `Snd`).
This is a sibling case, not a sub-case of Rec's induction.  It must be
imported as an EXTERNAL parameter / lemma.  For this concrete instance with
`s = Snd`, look in `BRA/Thm12AsymCases.agda` (which has Snd, Pair, etc. at
various shapes) or build it directly using `thmTDispAxSnd_param`.

In the general case (opaque `s`), Theorem 12 at `s` would be supplied via
mutual recursion with the outer `D2 : Fun2 → Fun2` function.  For this
session's concrete instance, just use the existing `Snd`-specific lemma.

## The universal proof via ruleIndBT

```agda
P : Formula
P = atomic (eqn (ap1 thmT (ap1 D_Rec_OS (var zero)))
                (codeFTeq1_RecOS (var zero)))
```

**Crucial check before proceeding**: confirm `substF` reduces definitionally
on `P`.  Verify in the Agda repl or by typechecking that
`substF zero O P` reduces to `atomic (eqn (ap1 thmT (ap1 D_Rec_OS O))
(codeFTeq1_RecOS O))` and similarly for `var v1`, `var v2`,
`ap2 Pair (var v1) (var v2)`.  This depends on:
- `thmT` being substitution-closed in `var 0` definitionally.  It's
  `Rec O stepProto`, and `stepProto` is closed in BRA — should be
  definitional.  If not, use `thClosed` + `eqSubst`.
- `D_Rec_OS = Rec z' s'` being substitution-closed.  Definitional iff
  `z'` (a Term) and `s'` (a Fun2) are closed (no free `var 0`).
- `codeFTeq1_RecOS` being defined to put `var 0` only in the
  `cor` and `ap1 (Rec O Snd) _` positions, both substitutable directly.

If any closure fails to reduce, you'll need `eqSubst`-bridge through the
formula (pattern: `BRA/Thm14Abstract.agda`'s `closureToG` for `thClosed`).

### Building `base`

```agda
base : Deriv (substF zero O P)
base = D_correct_RecOS_O
  -- Direct, no IHs needed.  Already exists in spirit in
  -- BRA/Thm12/Parts/Rec.agda; replicate at concrete (z=O, s=Snd).
```

### Building `step` (the Deriv of the implication)

This is where SKI-style construction applies.  Two viable approaches:

**Approach A — direct construction.**  Express `step` as a single closed
Deriv expression using `axK`, `axS`, `mp` applied to a closed Deriv that
"already accepts cross-IH inputs."  Specifically:

The Pair-case lemma `D_correct_RecOS_Nd a b d_a d_b` is an Agda function
of two Deriv inputs.  At `a = var v1, b = var v2`, view this as a closed
expression where `d_a, d_b` are open variables of types `A, B`
(the IH formulas).  Internalise by treating `D_correct_RecOS_Nd v1 v2`
as a Hilbert proof tree with `d_a, d_b` as hypotheses; apply the deduction
theorem twice.

For a chain of dispatcher calls like
```agda
D_correct_RecOS_Nd v1 v2 d_a d_b =
  ruleTrans step1
    (ruleTrans (parDispRuleTrans ... d_a (...)) -- d_a used here
               (parDispRuleTrans ... (parDispCong* ... d_b) ...))  -- d_b here
```
each `mp`-style step in the chain becomes an `axS`+`mp` after
internalisation.  Tedious but direct.  Estimated 30–80 LoC for `step`
construction.

**Approach B — manual SKI for one specific shape.**  If
`D_correct_RecOS_Nd v1 v2 d_a d_b` happens to use `d_a, d_b` exactly once
each in straightforward positions, the internalisation simplifies.  For
example, if the chain is
```
fn d_a d_b = composeRT_d_a_d_b (some closed parts)
```
where `composeRT_d_a_d_b` is one of a few standard composition shapes,
write the corresponding Hilbert combinator directly.

Worst case fall-back: write a small generic SKI translator as an Agda
helper that takes the Deriv expression with `d_a, d_b` open and produces
the closed implication.  ~50–100 LoC, mechanical.

### Final assembly

```agda
D_correct_RecOS : (x : Term) ->
  Deriv (atomic (eqn (ap1 thmT (ap1 D_Rec_OS x)) (codeFTeq1_RecOS x)))
D_correct_RecOS x =
  let univ : Deriv P
      univ = ruleIndBT P v1 v2 base step
        -- v1, v2 chosen as concrete fresh Nats, e.g., suc zero, suc (suc zero).
  in ruleInst zero x univ    -- modulo eqSubst transport for substF reduction.
```

If `P` doesn't reduce definitionally under `substF zero x P`, add an
`eqSubst` bridge.

## Closure obligations — checklist

Verify each of these reduces definitionally before relying on it:

1. `substF1 zero (var v1) D_Rec_OS`:  `D_Rec_OS = Rec z' s'` with `z'` a
   closed Term, `s'` a closed Fun2 (built from primitives only).  Should
   be definitional.  If not: use `thClosed`-style `eqSubst`.

2. `substF1 zero (var v1) thmT`:  per `BRA.Thm.ThmT`, `thmT = Rec O stepProto`
   with `stepProto` closed.  This is `thClosed` (Eq lemma, not definitional).
   Will likely need `eqSubst` to bridge.  See `BRA/Thm14Abstract.agda`
   `closureToG` for the pattern (uses `thClosed` repeatedly).

3. `subst zero (var v1) (cor X)` for various `X`:  `cor` is `Rec O stepCor`,
   so similar to thmT — propositional (not definitional) closure.  May
   need `eqSubst` with a `corClosed` lemma (define if not already in `Cor.agda`).

4. `subst zero (var v1) (reify (codeF1 (Rec O Snd)))`:  `reify` produces
   closed Terms (no `var 0`), so substitution is identity definitionally.

5. `subst zero (var v1) (ap1 (Rec O Snd) (var zero))`:  this is the
   tricky case.  `ap1 (Rec O Snd) (var zero)` substituted at `var v1`
   becomes `ap1 (substF1 zero (var v1) (Rec O Snd)) (var v1)`.  We need
   `substF1 zero (var v1) (Rec O Snd) = Rec O Snd`; since `O` is closed
   and `Snd` is closed, the `Rec` branch of `substF1` reduces it to
   `Rec O Snd` definitionally.  ✓

The most likely friction points are (2) and (3) — `thmT` and `cor` both
go through `Rec`-of-closed-stepfun, which Agda may not reduce
definitionally.  Plan to use `eqSubst` bridges from the start.

## Success criteria

- `BRA/Thm12RecCheck.agda` typechecks (`agda --safe --without-K
  --exact-split BRA/Thm12RecCheck.agda` exit 0).
- No `postulate`, no holes (`?`).
- Final theorem `D_correct_RecOS : (x : Term) → Deriv (...)` exported
  with the asymmetric Theorem 12 conclusion at concrete `Rec O Snd`.
- LoC reported.

## If it fails

Report the precise obstruction:
- Closure obligation that doesn't reduce (and which substF1 step blocks).
- Dispatcher whose intermediate shape doesn't match (with the actual vs
  expected types from Agda's error).
- SKI internalisation fails to typecheck (and at which lambda).

Don't commit a half-baked file with postulate placeholders.  If the
construction breaks down, the diagnostic is the deliverable.

## Files to consult

- `BRA/Thm14CodeFTeqAsym.agda` — the asymmetric encoder.
- `BRA/Thm12LiftI.agda` (80 code LoC) and `BRA/Thm12LiftComp.agda`
  (235 code LoC) — composition patterns at single / double IH.
- `BRA/Thm12/Parts/Rec.agda` — the existing `IfLf`-dispatch
  Construction (different design, but reusable for the leaf-case
  proof and bridge).
- `BRA/Thm12/Param/AxRecLf.agda`, `BRA/Thm12/Param/AxRecNd.agda` —
  parametric Term-level encoders + dispatchers for `axRecLf` and
  `axRecNd`.
- `BRA/Thm12/Param/RuleTrans.agda`, `Cong1.agda` — chain combiners.
- `BRA/Cor.agda` — `cor`, `stepCor`, `stepCorRed`, `corOfReify`.
- `BRA/Thm.ThmT.agda` — `thmT`, all `thmTDisp*_param` dispatchers.

## What this session does NOT need to do

- Generalise to opaque `z, s` (do at concrete first; opaque is downstream).
- Handle TreeEq (separate open problem).
- Touch `BRA/Thm12.agda`'s FromBridges architecture.
- Build a full universal `thm12_F1 : (f : Fun1) (x : Term) → ...`.

The deliverable is one specific file proving Rec at one specific concrete
instance.  If that works, we know the architecture for Rec is sound
and the rest is generalisation engineering.
