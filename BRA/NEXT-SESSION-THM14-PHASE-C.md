# Next session — Theorem 14 Phase C (lifted step3..step5 chain)

## Status from previous session (2026-05-02)

Phase A and Phase B of `BRA/NEXT-SESSION-THM14-CONSTR5.md` are
landed and typecheck:

  * **Phase A** — `BRA/Thm14Numerals.agda` (170 LoC, 0.33s).
    Closed encoded witnesses:
      * `t_formula`, `t_deriv`, `t_term`, `t_witness` — Guard's
        transitivity tautology `(x_0=x_2) ⊃ ((x_1=x_2) ⊃ (x_0=x_1))` .
      * `t'_formula`, `t'_deriv`, `t'_term`, `t'_witness` — Guard's
        ex-falso tautology `(x_0=x_1) ⊃ ((¬(x_0=x_1)) ⊃ (0=1))`  via
        `axExFalso` .

  * **Phase B** — `BRA/Thm14Constr5Final.agda` (266 LoC, 0.61s).
    Closed Fun1 definitions parametric in `r12_th` , `r12_sub` :
      * `f_part`, `g_part`, `K_part`, `h_part`, `constr5` — Guard's
        sb-chain numerals built from `Comp2 / KT / I / cor / D_thmT /
        D_sub_at_ii` .

These are NO-PROOF structural definitions of the encoded sb-chain;
each `ap1 F x` BRA-equationally reduces to the Term form of Guard's
encoded sb-chain layer.  The Fun1 algebra used is the standard
`pairF1 = Comp2 Pair` , `constTermF1 = KT` , `constApp2F1 g a b =
Comp2 g (KT a) (KT b)` for closed-but-non-canonical constants.

## Phase C: the lifted step3..step5 chain (THIS SESSION)

Goal: produce
```agda
step5_l : (x : Term) ->
          Deriv (PrAtX x imp
                  atomic (eqn (ap1 thmT (ap1 constr5 x))
                              (reify (codeFormula bot))))
```
inside `module Th14Constr5Final (r12_th : Thm12_F1_Result thmT)
(r12_sub : Thm12_F2_Result sub) where ...` (the existing module in
`BRA/Thm14Constr5Final.agda` ).  Then Phase D plugs `(constr5,
step5_l)` into `BRA.GoedelII.Compose` for the headline `godelII :
Deriv Con -> Deriv bot` .

### Pre-flight (mandatory; ~30 min)

1. Re-read `guard15.pdf` p.16-17 (Theorems 11-14) and `BRA/COR-AT-SB-LOAD-BEARING.md` .
2. Verify the substitution sequence in Guard's `f, g, h, K, constr5`
   matches the structural definitions in `BRA/Thm14Constr5Final.agda`
   (Phase B comments document the intended encoding).  Do NOT re-derive
   this from scratch; just check.
3. Re-read `BRA/Thm14Step4Test.agda` — it exercises
   `body_ruleInst_eval_param` with a single sb-step at var 1 + cor x
   substituent.  This is the same pattern used by `K_part` 's
   correctness proof (= step 4 of Guard).

### Layout

Add a new file `BRA/Thm14Phase_C.agda` (or extend `Thm14Constr5Final.agda` —
the latter starts to typecheck slowly under the Thm12-result import,
so a new file is likely cleaner).  Skeleton:

```agda
module BRA.Thm14Phase_C
  (r12_th  : Thm12_F1_Result thmT)
  (r12_sub : Thm12_F2_Result sub)
  where

open BRA.Thm14Constr5Final.Th14Constr5Final r12_th r12_sub
  using ( D_thmT ; D_sub ; D_sub_at_ii
        ; f_part ; g_part ; K_part ; h_part ; constr5
        ; sub_ii_subst )

open import BRA.Th14Constr5
open Th14Constr5 r12_th r12_sub
  using (step1_l ; step2_l)

-- Step 3 ...  ~150-200 LoC
step3_l : (x : Term) -> ...

-- Step 4 ...  ~80-120 LoC
step4_l : (x : Term) -> ...

-- Step 5 inner (encMp on h_part / g_part) ...  ~120-180 LoC
step5_inner : (x : Term) -> ...

-- Step 5 (encMp on inner / K_part) ...  ~30 LoC
step5_l : (x : Term) -> ...
```

### Per-step recipe

Each `step_K_l x` is a `liftedRuleTrans P (...) (...) (...)` chain
over already-lifted pieces (helpers from `BRA.Thm.EvalHelpers` ).
Where  P = PrAtX x .  Internally each chain node uses one of:

  * `thmTDispMp_param` — for an encMp dispatch (need the inner and
    outer `thmT` images of the two halves).
  * `thmTDispRuleInst_param` — for an encRuleInst dispatch (need the
    `Fst-shape` proof for the proof-index `xT` and the `thmT(xT)`
    image).
  * `subTDef` + `codeCommutesFormula` — to reduce `subT(...)
    (codeFP)` to `reify (codeFormula (substF n t P))` .  Already done
    inside `thmTDispRuleInst_param` 's body, but Phase C composes a
    chain of these so the bridge appears at every layer.
  * `corOfReify` ( `BRA/Cor.agda` ) — to identify `cor (reify v)` with
    `reify (code (reify v))` at sb substituent positions.  Used at the
    "depends on x" leaves where the substituent is `ap1 cor x` and
    `code (ap1 cor x)` for an arbitrary  x  is a stuck term — the
    bridge is what makes  cor x = num x  parametric in  x  match
    Guard's encoding.

### The cor-bridge gotcha

The hardest part of Phase C is the cor-bridge derivation at sb-leaves
where the substituent is `ap1 cor x` for a runtime  x .  The result
of `thmTDispRuleInst_param 0 (ap1 cor x) (reify t_term) ...` is

```
ap1 thmT (Pair tagCode_ruleInst (Pair varCode0T (Pair (reify t_term) (ap1 cor x))))
  =  ap2 subT (Pair varCode0T (ap1 cor x)) (ap1 thmT (reify t_term))
```

Then by `t_witness` (lifted under  P ): `ap1 thmT (reify t_term) =
reify (codeFormula t_formula)` — closed.

Then we need to identify `subT (Pair varCode0T (ap1 cor x)) (reify
(codeFormula t_formula))` with `reify (codeFormula (substF 0 (ap1 cor
x) t_formula))` .  This is `subTDef` + `codeCommutesFormula` , the
SAME pattern thmTDispRuleInst_param 's body uses internally.  But
`code (ap1 cor x)` for arbitrary  x  is stuck, so the
`codedSubst (code (ap1 cor x)) (code (var 0)) (codeFormula t_formula)`
form also is stuck.

The cor-bridge says: for canonical inputs, `cor (reify v) = reify
(code (reify v))` .  When step5 is later instantiated at `x := var 1`
in the closure, `cor (var 1)` does NOT reduce — it stays as
`ap1 cor (var 1)` .  However, the closure ruleInst-s at `(var 1)` and
inserts the canonical witness later via `subIIeqcG` , so the cor-bridge
is invoked at the closed-instance level.

**Recommended approach**: parameterise the chain over a
substituent-handling lemma `corBridge : (x : Term) -> Deriv (...)`
which is supplied at the call site (where  x  is canonical OR known to
be `var k` with a Pair-shape proof from `MaxVar.pickFresh` ).  See
`BRA/MaxVar.agda` for fresh-variable pickers.

### Files / commits to expect

  * `BRA/Thm14Phase_C.agda` — main file, ~600-800 LoC.  Commit per
    sub-step (step3_l, step4_l, step5_inner, step5_l).
  * Possibly a small helper file `BRA/Thm14CorBridge.agda` if the
    cor-bridge layer ends up >100 LoC.
  * `BRA/GoedelIIFinal.agda` — Phase D headline (~30 LoC).

### Recommended attack order

1. **(2 hr) step3_l** .  This is the most complex step (3-deep
   ruleInst chain inside f_part + 2 mp wraps).  If you can get this
   to typecheck, the rest follow the same pattern.  Commit on
   completion.

2. **(1 hr) step4_l** .  Single ruleInst at K_part .  The
   `Thm14Step4Test.agda` work is directly applicable.  Commit.

3. **(2-3 hr) step5_inner + step5_l** .  Two outer mp's combining
   step3_l, step4_l, and the lifted t'-witness chain.  Commit.

4. **(15 min) Phase D** .  Open `BRA/GoedelIIFinal.agda` and write
   one module instantiation:
   ```agda
   module Final = BRA.GoedelII.Compose constr5 step5_l
   godelII : Deriv Con -> Deriv bot
   godelII = Final.godelII
   ```

### Stopping criteria

If a sub-step >2 hours of stuck shape obligations, write a
sub-step prompt and stop.  The Phase C chain has many small obligations,
and grinding through unsuccessfully for >2 hours is the explicit
warning in NEXT-SESSION-THM14-CONSTR5.md .

### What to update on success

  * `MEMORY.md` add  `project_godelII_unconditional.md` .
  * `BRA/THM14-OBSTRUCTIONS.md` mark all PINNED items as RESOLVED.
  * Delete this file (now superseded).
  * `BRA/Thm14Final.agda` (or `BRA/GoedelIIFinal.agda` ) becomes the
    canonical Goedel II chain entry point.

## Constraints

  * ASCII only.
  * `{-# OPTIONS --safe --without-K --exact-split #-}` .
  * No postulates, no holes, no with-abstraction, no dot patterns.
  * No new `Deriv` constructors, no new tagged dispatchers in
    `BRA/Thm/ThmT.agda` .
  * Do not weaken any other theorem.

## See also

  * `BRA/NEXT-SESSION-THM14-CONSTR5.md` — the parent prompt; Phase C
    instructions section (~lines 130-180) is the canonical recipe.
  * `BRA/Thm14Step4Test.agda` — proven prototype for the K_part step.
  * `BRA/Thm.ThmT.agda:8838` — `thmTDispRuleInst_param` (parametric
    Term substituent).
  * `BRA/Thm.ThmT.agda:5575` — `thmTDispMp` (closed-form mp dispatch);
    parametric variant `thmTDispMp_param` lives at the same module
    layer if needed.
  * `BRA/Thm.EvalHelpers.agda` — `liftAxiom / liftedRuleTrans /
    liftedCong1 / liftedCongL / liftedCongR` and their two-layer
    variants used at every chain node.
  * `BRA/COR-AT-SB-LOAD-BEARING.md` — the cor-bridge analysis;
    identifies the 6 sb-substituent positions in Guard's chain that
    need num's specification.
