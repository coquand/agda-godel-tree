# Next session — Exercise 24 and Gödel II

This is the bootstrap document for the fresh session that continues
the unify-5c Gödel II work after session G (2026-04-23).

## TL;DR

Gödel II in our Agda formalisation needs Guard's Exercise 24 BRA
functors (`num` total, `mp`, `ax`, `ind`) as actual `Fun1`/`Fun2`
values with DerivF defining-equation axioms.  Without them the Thm
14 chain cannot close: our per-primitive-case lemmas cover only
specific input shapes and don't handle variables, which the chain
needs.

This is the genuine Guard path.  Scale: ~1500-2000 lines.  Large
but unavoidable.

## Required reading (in order)

1. `guard15.pdf` pages 13-14 — Def 9, Def 10, Def 11, Exercise 24.
   Study Ex 24's eight functors closely; these are the specifications
   to implement.
2. `guard15.pdf` pages 16-17 — Thm 12, Thm 13, Thm 14.  Understand
   what the chain actually uses.
3. `Guard/UNIFIED-DESIGN-REV2-5C.md` §"Session G discovery" — why
   the superficial approach fails and why Path A (Ex 24) is the only
   route.
4. `~/.claude/projects/-Users-coquand-CHWISTEK/memory/project_session_g_discovery.md` — concise summary.
5. `Guard/Thm13.agda` — existing 19 per-primitive-case D1/D2 lemmas.
   These are useful as BASE CASES for primitive functors but do not
   by themselves suffice — they handle specific input shapes
   (O, Pair a b) and not variables.

## What is already shipped and on the critical path

| Commit | Content | Status |
|--------|---------|--------|
| `[unify-5c-enc-eq-axioms]` (06f4756) | n34 tag + `encAxEqTrans` encoder | ✓ use as-is |
| `[unify-5c-enc-t]`         (cf7913f) | encoded axiom `t`                | ✓ use as-is |
| `[unify-5c-enc-exfalso]`   (8d35976) | n35 tag + `encAxExFalso` encoder | ✓ use as-is |
| `[unify-5c-enc-tprime]`    (591aa58) | `axExFalso` DerivF + encoded `t'`| ✓ use as-is |

Plus the base infrastructure: DerivF, thmT, Thm13.agda (per-primitive
D1/D2), Prov combinators, encAxK/S/Neg/Mp, diagFTargetCR, etc.  All
untouched by Path A work.

## What is shipped but NOT on the critical path

`[unify-5c-thm12-thm13-uniform]` (ed4727d) introduced `Guard/Thm12Uniform.agda`
and `Guard/Thm13Uniform.agda` with a superficial `D_f x := encAxRefl
(ap1 cor (ap1 f x))` construction.  These compile but produce targets
at the term level (Pair of cor-applications) instead of the
codeFormula-of-equation level.  They do NOT compose with `encMp`'s
case33 dispatch, which expects `reify(codeFormula ...)` shapes.

**Recommended action in the fresh session:** once Path A's `D_thmT`
reaches feature-parity with what these files were trying to provide,
delete both files (`Guard/Thm12Uniform.agda`, `Guard/Thm13Uniform.agda`).
Until then, keep them in-tree as a reference for the failed approach,
so future debugging doesn't re-derive the same confusion.

## Path A in concrete steps

### Step 1 — extend cor to be total on Terms

Guard's `num` is defined on all BRA terms (variables included).  Our
`cor : Fun1 = Rec falseT stepCor` only reduces on reified trees.
Two options:

**Option 1a** — redefine cor as a more general Fun1 that handles
variables via dispatch.  Tricky: variables aren't a Rec-dispatchable
shape.  May require a new primitive or external Agda meta-definition.

**Option 1b** — add DerivF axioms matching Guard's Def 10 rules 2-4:
```agda
axCorVar : (n : Nat) -> Deriv (atomic (eqn (ap1 cor (var n))
                                            (reify (code (var n)))))
axCorAp1 : (f : Fun1) (t : Term) ->
           Deriv (atomic (eqn (ap1 cor (ap1 f t))
                              (reify (code (ap1 f t)))))
axCorAp2 : (g : Fun2) (a b : Term) ->
           Deriv (atomic (eqn (ap1 cor (ap2 g a b))
                              (reify (code (ap2 g a b)))))
```
These are Guard's Def 10 rules 2, 3, 4 at the Deriv level.  In
Guard's BRA they would be derived from `num`'s primitive recursive
definition; here they are stipulated axiomatically per Def 10.

Recommended: **Option 1b**.  Minimal change, matches Guard's Def 10
directly, and keeps cor's existing reduction on reified trees intact.

### Step 2 — define `mp : Fun2`

Specification (Ex 24 [1]): `mp("P", "P ⊃ Q") = "Q"`.

Implementation sketch:
```agda
mp : Fun2
mp = <Fun2 expression that on (pCode, pImpQCode) extracts qCode>
```
where pImpQCode has shape `Pair tagImpT (Pair pCode qCode)` per
codeFormula's IMP rule.  Extraction via `Snd (Snd pImpQCode)`.

Plus the defining-equation axiom:
```agda
axMp : (P Q : Formula) ->
       Deriv (atomic (eqn (ap2 mp (reify (codeFormula P))
                                  (reify (codeFormula (P imp Q))))
                          (reify (codeFormula Q))))
```

### Step 3 — define `ax : Fun1`

Specification (Ex 24 [6]): `ax(i) = "<i-th BRA axiom>"`.  In our
system, axiom indices correspond to thmT's dispatch tags (n0..n32
for the 33 axioms).

Implementation: use Rec or IfLf-based dispatch on the input index
to select the right axiom's codeFormula.  Each branch emits a
specific reified tree.

Plus defining-equation axioms per index:
```agda
axAx0 : Deriv (atomic (eqn (ap1 ax O)                         -- index 0
                           (reify (codeFormula <axiom 0>))))
axAx1 : Deriv (atomic (eqn (ap1 ax (reify (natCode 1)))       -- index 1
                           (reify (codeFormula <axiom 1>))))
-- ... per axiom
```

### Step 4 — define `ind : Fun2`

Specification (Ex 24 [5]): `ind("P(0)", "P(x) ⊃ P(sx)") = "P(x)"`.

Implementation + defining axiom similar to mp.

### Step 5 — build D_thmT via meta-induction

`thmT = Rec O thmTStep`.  Guard's Thm 12 for f = Rec z s:
    D_{Rec z s}(x)  :=  <some functor expression involving D_z, D_s, mp, ind>

Inductively unfold until primitive functors.  `thmTStep` itself is
`Fan dataIsLfV3 (Fan lfDispatchV3 ndDispatchV3 Pair) IfLf`; each
sub-expression needs its own D.  Terminate on primitive constructors
(I, Fst, Snd, Pair, KT, IfLf, TreeEq, Rec-base, etc.) using our
existing Thm13.agda per-primitive lemmas as base cases.

Outcome: a specific Fun1 `D_thmT : Fun1` and a correctness theorem
```agda
thm12ThmT : (x : Term) ->
  Deriv (atomic (eqn (ap1 thmT (ap1 D_thmT (reify (code x))))
                     (reify (codeFormula
                       (atomic (eqn (ap1 cor (ap1 thmT (reify (code x))))
                                    (ap1 cor (ap1 thmT (reify (code x))))))))))
```
(Or adjust the RHS to match whatever "fx_ = fx" becomes in our
framework; see Guard's Def 10/12 for the precise target.)

### Step 6 — D_substOp (binary analog)

`substOp = RecP stepSubstP`.  Same idea, with D_{RecP s} + Ex 24
functors.

### Step 7 — Thm 13 (conditional corollary)

Given Thm 12 output and a hypothesis `H : ap1 f x = y`, transport
the RHS via `axEqCong1 cor + mp` (or `cong1 cor H`) to replace
cor(f x) with cor(y).  ~50 lines on top of each Thm 12.

### Step 8 — Thm 14 chain + godelI + godelII

Once Thm 12 and Thm 13 exist for thmT and substOp, the chain (steps
1-5 per guard15 p.17) is encoder composition using the already-shipped
`t`, `t'`, `encMp`, `encRuleInst`, etc.  ~300-500 lines.

Close godelI: `ruleInst 0 e_G` on the chain + `mp` with `provCorr
pG` + `corOfReify` bridges to match `reify(codeFormula botEq)` as
the Prov target.

Close godelII: compose chainConToGs (uses diagFTargetCR + Thm 13 at
substOp) with godelI.

## Final type signatures

```agda
godelI    : Prov gsCR     -> Prov botEq
godelIIHF : Prov conHFEq  -> Prov botEq
godelIIHF = godelI ∘ chainConToGs
```

## Estimated session count

Session H: Ex 24 functors (cor extension + mp + ax + ind + their
axioms).  Medium file size; expect 500-800 lines.

Session I: D_thmT via meta-induction.  Probably the hardest single
session; expect 400-700 lines and typecheck-time sensitivity.

Session J: D_substOp + Thm 13.  Similar size to session I but with
working template from session I to follow.

Session K: Thm 14 chain + godelI + godelII.  Mostly mechanical if
preceding sessions are solid.

## Hard constraints (inherited from project conventions)

- `~/.cabal/bin/agda-2.9.0 --safe --without-K --exact-split`.
- No postulates, no holes.
- Per-file typecheck < 10 seconds (see feedback_guard_fast_typecheck).
- One named top-level lemma per paper step (see
  feedback_one_lemma_per_paper_step).
- Avoid with-abstraction (see feedback_no_with_agda).
- No new Deriv constructors for things derivable (see
  feedback_no_new_deriv_axioms).  The Ex 24 defining-equation
  axioms ARE acceptable under the "ground defining equations ok"
  precedent (see feedback_ground_axioms_ok) — they're not
  universally-quantified reflection rules, just specific
  primitive-recursive defining equations per Guard's Def 10.

## Open question for session H

Whether `ax`'s defining equations can all be ground (one per
specific axiom index) or whether a universally-quantified version
is acceptable.  Guard implicitly uses universal quantification
over indices; we may need to stick with per-index ground axioms
to respect `feedback_no_new_deriv_axioms`.  Prototype early and
check with user if unclear.
