# [unify-5c] Gödel II chain on the hyp-free stack

Detailed design for the [unify-5c] step of the Option G / REV2
unification plan.  See UNIFIED-DESIGN-REV2.md for background and
[unify-5a], [unify-5b] commit messages for the preceding work.

## Prerequisites (all shipped as of commit 9298b61)

- `Guard.DerivF`                   — hyp-free Deriv over Formula.
- `Guard.ThFunTForHF`              — hyp-free `thmT : Fun1` with
                                     `codeTrueT` sentinel.
- `Guard.ThFunTForV3DefsUnify`     — reduction machinery on HF.
- `Guard.ThFunTForV3PassUnify`     — HF passthrough chains.
- `Guard.ProofEncUnify`            — all axiom/rule encoders without
                                     hCode, except `encRuleHyp`
                                     (removed).
- `Guard.ProofEncFormula`          — formula-level encoders
                                     (encAxK/S/Neg/Mp) without hCode.
- `Guard.SubstTForPrecompClassicalUnify` — gsCR, cGSCR, templateCodeCR,
                                     crTCCR ready to use.  Note:
                                     `diagFTargetCR` is NOT yet ported
                                     to the hyp-free Unify stack; see
                                     STEP 1 of the current handoff.

## Goal

Prove Gödel II constructively as

```agda
godelIIHF : Prov conHFEq -> Prov botEq
```

where

```agda
Prov : Formula -> Set
Prov P = Sigma (e : Term) (Deriv (atomic (eqn (ap1 thmT e)
                                             (reify (codeFormula P)))))

conHFEq : Formula
conHFEq = atomic (eqn (ap2 TreeEq (ap1 thmT (var v1)) codeBotT) falseT)
-- internal consistency: for all var 1, thmT(var 1) != codeBotT
-- (uses var 1 to keep out of gsCR's proof slot at var 0)

botEq : Formula
botEq = atomic (eqn O falseT)   -- "0 = 1"
```

The proof factorizes via Guard's Theorem 11 (Gödel I) as:

```
godelIIHF = godelI ∘ chainConToGs
chainConToGs : Prov conHFEq -> Prov gsCR
godelI       : Prov gsCR    -> Prov botEq
```

No `Consistent` assumption, no `Empty` conclusion; the classical form
falls out as contrapositive at the consumer site.

## Architecture invariants

Carried over from REV2:

- `thmT` stays a VALIDATOR (malformed input -> `codeTrueT`, not O).
- No hyp, no hCode, no ruleHyp, no case26, no thm14EV3 recursor.
- Everything stays in equation-level form (`atomic (eqn …)`); Guard's
  formula-level `~` is avoided — equational manipulation via
  `treeEqSelfReify` closes the self-application directly.
- All encoders compose; encoded proofs built **in parallel** with
  Deriv proofs, never extracted by a Deriv-generic recursor.

## Variable correspondence with guard15.pdf

| guard15 | ours (SubstTForPrecompClassicalUnify) |
|---------|---------------------------------------|
| `x₀`    | `var 1` (diagonalized away by `substEq v1 (reify templateCodeCR)`) |
| `x₁`    | `var zero` — the remaining free variable, the **proof slot** |
| `i`     | `reify (codeEqn templateCR)` (roughly — more precisely the `templateCodeCR` combined with `cor`) |
| `j`     | `reify cGSCR` |
| `th`    | `thmT : Fun1` |
| `sub`   | `substOp : Fun2` |
| `Df`    | `D1 f : Fun1` (to define in Guard.Thm13) |
| `Dg`    | `D2 g : Fun2` (to define in Guard.Thm13) |

## Components

### (1) Guard.Thm13  [~800 lines]

Mutually-recursive encoder functors for arbitrary Fun1/Fun2, and
their correctness lemmas.

#### Signatures

```agda
D1 : Fun1 -> Fun1
D2 : Fun2 -> Fun2

thm13Fun1 : (f : Fun1) (xC yC : Term) ->
  Deriv (imp (atomic (eqn (ap1 f xC) yC))
             (atomic (eqn (ap1 thmT (ap1 (D1 f) xC))
                          (reify (codeFormula (atomic (eqn (ap1 f xC) yC)))))))

thm13Fun2 : (g : Fun2) (x1C x2C yC : Term) ->
  Deriv (imp (atomic (eqn (ap2 g x1C x2C) yC))
             (atomic (eqn (ap1 thmT (ap2 (D2 g) x1C x2C))
                          (reify (codeFormula (atomic (eqn (ap2 g x1C x2C) yC)))))))
```

#### Cases

**Fun1 constructors to handle:**
- `I`      — base case, Deriv reduces `I(x) = x` via axI; encoder emits `encAxI`.
- `Fst`    — axFst; `encAxFst`.
- `Snd`    — axSnd; `encAxSnd`.
- `KT t`   — axKT; `encAxKT`.
- `Comp f g`   — inductive: combine `D1 f` and `D1 g`.
- `Comp2 h f g` — inductive: combine `D2 h`, `D1 f`, `D1 g`.
- `Rec z s`    — axRecLf + axRecNd base cases + inductive.
- `RecP s`     — axRecPLf + axRecPNd.

**Fun2 constructors to handle:**
- `Pair`   — base; `encAxPair`? (axiom for Pair is… identity-like; needs encoder).
- `Const`  — axConst; `encAxConst`.
- `Lift f` — axLift; combines with `D1 f`.
- `Post f h` — axPost; combines with `D1 f` and `D2 h`.
- `Fan h1 h2 h` — axFan; combines with `D2 h1, D2 h2, D2 h`.
- `IfLf`   — axIfLfL + axIfLfN base cases.
- `TreeEq` — axTreeEqLL + axTreeEqLN + axTreeEqNL + axTreeEqNN base cases.

**Inductive step pattern** (sketch for `Comp f g`):

```
D1 (Comp f g) = (Fun1 built from D1 f, D1 g, and encoded axComp and encMp)
```

The implementation of `D1 (Comp f g)` is a Fun1 expression that, when
applied to xC, produces a Term that encodes the proof
```
  Comp f g (x) = f (g x)                    [axComp]
  g(x) = y1                                  [subproof]
  f(y1) = y                                  [subproof]
  ---------------------                      [transitivity]
  Comp f g (x) = y
```
This is encRuleTrans composed with encoded axComp and the sub-proofs
from `D1 g` (for `g x = y1`) and `D1 f` (for `f y1 = y`), with
appropriate instantiations.

**Mutual recursion:** `D1 (Comp2 h f g)` uses `D2 h` and `D1 f`, `D1 g`.
`D2 (Post f h)` uses `D1 f` and `D2 h`.  Etc.  The mutual structure
matches Guard's Thm 12 meta-induction on functor length.

#### Scope discipline

- `Guard.Thm13` imports `Guard.ProofEncUnify` and `Guard.ProofEncFormula`.
- No new Deriv axioms.  All work done via existing encoders +
  `Guard.DerivF` rules.
- Correctness lemmas use `encRuleTransCorr`, `encMpCorr`, etc.

### (2) Prov predicate + combinators  [~200 lines]

New module `Guard.Prov`.

```agda
Prov : Formula -> Set
Prov P = Sigma (e : Term) (Deriv (atomic (eqn (ap1 thmT e)
                                             (reify (codeFormula P)))))

provMp    : Prov (imp P Q) -> Prov P -> Prov Q
provInst  : (x : Nat) (t : Term) (P : Formula) ->
            Prov P -> Prov (substForm x t P)
provTrans : Prov (atomic (eqn a b)) -> Prov (atomic (eqn b c)) ->
            Prov (atomic (eqn a c))
provSym   : Prov (atomic (eqn a b)) -> Prov (atomic (eqn b a))
provCongL : (g : Fun2) (x : Term) ->
            Prov (atomic (eqn t u)) ->
            Prov (atomic (eqn (ap2 g t x) (ap2 g u x)))
provCongR : (g : Fun2) (x : Term) ->
            Prov (atomic (eqn t u)) ->
            Prov (atomic (eqn (ap2 g x t) (ap2 g x u)))
-- and similar wrappers around existing encoder lemmas
```

Implementations use `encMp`, `encRuleInst`, `encRuleTrans`,
`encRuleSym`, `encCongL`, `encCongR` from ProofEncUnify.  Each
combinator bundles the Term-level encoder output with the
Deriv-level correctness witness.

### (3) Guard.GodelI  [~150 lines]

```agda
godelI : Prov gsCR -> Prov botEq
```

Construction:
1. Let `(e_G, d_G) : Prov gsCR`.  So
   `d_G : Deriv (atomic (eqn (ap1 thmT e_G) (reify cGSCR)))`.
2. `provInst zero e_G (atomicForm gsCR) (e_G, d_G)` — instantiate the
   proof slot at e_G itself.  Result:
   `(e_inst, d_inst) : Prov (substForm zero e_G (atomicForm gsCR))`.
   After substitution, the atomic form becomes:
   ```
   atomic (eqn (ap2 TreeEq (ap1 thmT e_G) (reify cGSCR)) falseT)
   ```
3. Build `Prov (atomic (eqn (ap2 TreeEq (ap1 thmT e_G) (reify cGSCR)) O))`
   via `provCongL TreeEq (reify cGSCR) (e_G, d_G)` composed with
   encoded-treeEqSelfReify applied to cGSCR.
4. `provTrans` of step 3 (symmetric) and step 2:
   `Prov (atomic (eqn O falseT))` = `Prov botEq`.

Key subtlety: `treeEqSelfReify` needs to be available in
encoded/Prov form.  Either:
- Wrap it as `provTreeEqSelfReify : (t : Tree) -> Prov (atomic (eqn (ap2 TreeEq (reify t) (reify t)) O))`.
- Implementation: induction on `t` using encAxTreeEqLL /
  encAxTreeEqNN + encCong + encRuleTrans — mirroring the existing
  `treeEqSelfReify` proof.  ~50 lines.

### (4) Guard.GodelII  [~300 lines]

```agda
chainConToGs : Prov conHFEq -> Prov gsCR
godelIIHF    : Prov conHFEq -> Prov botEq
godelIIHF conPf = godelI (chainConToGs conPf)
```

Implementation of `chainConToGs`:

Steps 1-5 from guard15.pdf p.17, each producing a Prov.

**Step 1** (Thm13Fun1 at `f = thmT`, `yC = reify cGSCR`):
```
step1Prov : Prov (imp (atomic (eqn (ap1 thmT (var 0)) (reify cGSCR)))
                      (atomic (eqn (ap1 thmT (ap1 (D1 thmT) (var 0)))
                                   (reify (codeFormula (atomic (...step1RHS...)))))))
```
Obtained by wrapping `thm13Fun1 thmT (var 0) (reify cGSCR)` with Prov.

**Step 2** (Thm13Fun2 at `g = substOp`, closed args):
Requires discharging the Thm13Fun2 LHS hypothesis via `diagFTargetCR`:
```
step2Deriv : Deriv (atomic (eqn (ap2 substOp argL argR) (reify cGSCR)))
step2Deriv = diagFTargetCR    -- already shipped

step2Prov : Prov (atomic (eqn (ap1 thmT (ap2 (D2 substOp) argL argR))
                              (reify (codeFormula ...step2RHS...))))
step2Prov = provMp (thm13Fun2 substOp argL argR (reify cGSCR)) (diagFTargetCRProv)
```
where `argL = reify crTCCR` and `argR = reify templateCodeCR`.

**Step 3** (combine via encoded ax(4) + encMp):
```
step3Prov : Prov (imp (atomic (eqn thmT_x cGSCR))
                      (atomic (eqn (ap1 thmT gx)
                                   (reify (codeFormula "thmT x = substOp(argL, argR)")))))
```
`gx` is a specific Term: `encMp (encMp encTrans4 step1-hx) step2-hx`
or similar, where encTrans4 = encoded axiom `x₀ = x₂ ⊃ x₁ = x₂ ⊃ x₀ = x₁`.

Note: axiom ax(4) (Guard's transitivity) is derivable in our DerivF
from ruleTrans + propositional encoders.  Need to establish
`encTrans4` as a specific encoded proof term, ~30 lines.

**Step 4** (rewrite RHS by definition of cGSCR):
```
step4Prov : Prov (imp (atomic (eqn thmT_x cGSCR))
                      (atomic (eqn (ap1 thmT hx)
                                   (reify (codeEqn gsCR)))))
```
Since `reify cGSCR = reify (codeEqn gsCR)` by definition (cGSCR
literally IS codeEqn gsCR), step 4 is essentially step 3 with a
rewrite.  May be a no-op in our equational formulation.

Wait — cGSCR IS `codeEqn gsCR`, not `codeFormula (atomic gsCR)`.
These differ by a tag for `atomic`.  So step 4 needs a small bridge
`codeEqn e = codeFormulaUnderAtomic e` or similar.  TBD once we
look at the actual `codeFormula` vs `codeEqn` relationship.

**Step 5** (combine step 3 and step 4 via encoded ax(t') + encMp):
Axiom t' = `x₀ = x₁ ⊃ x₀ ≠ x₁ ⊃ 0 = 1`.  In equational form we
don't need this as a separate axiom — from `thmT(hx) = codeOf(gsCR)`
and from `thmT(var 0) = cGSCR`, combined with `treeEqSelfReify` on
cGSCR, we get `codeOf(TreeEq (thmT hx) cGSCR = falseT)` via the
gsCR-instantiation argument.

Actually — step 5 in equational form is:
```
step5Prov : Prov (imp (atomic (eqn (ap1 thmT (var 0)) (reify cGSCR)))
                      (atomic (eqn (ap1 thmT φx) codeBotT)))
```
where φx combines step 3's hx, step 4's continuation, and encoded
treeEqSelfReify + encoded TreeEq-falseT axiom.  Roughly:
```
φx = (specific composition of encMp applied to encoded transitivity,
      step 3/4 encoded sub-proofs, and encoded treeEq-self)
```

**Final step — chainConToGs**:

Assume `(e_conH, d_conH) : Prov conHFEq`.

- From conHFEq: provInst at var 1 := φx gives a Prov of
  `atomic (eqn (TreeEq (ap1 thmT φx) codeBotT) falseT)`.
- From step5Prov: under hypothesis `thmT(var 0) = cGSCR`, we have
  `thmT(φx) = codeBotT`.
- Combined via encMp and equational transitivity:
  `Prov (atomic (eqn (TreeEq (ap1 thmT (var 0)) (reify cGSCR)) falseT))`
  = Prov gsCR (the equational form).

This IS Prov gsCR.  Return it.

### (5) Compose

```agda
godelIIHF : Prov conHFEq -> Prov botEq
godelIIHF conPf = godelI (chainConToGs conPf)
```

## Ordering and commits

Suggested commit sequence:

1. `[unify-5c-thm13-fun1]` — D1 and thm13Fun1 for Fun1.  Base cases
   first (I, Fst, Snd, KT), then inductive (Comp, Rec, RecP,
   Comp2 — the last depends on D2 so may need stub).
2. `[unify-5c-thm13-fun2]` — D2 and thm13Fun2 for Fun2.  Mirrors
   above.
3. `[unify-5c-thm13-mutual]` — close the mutual recursion between
   Comp2, Post, Fan, etc.  Final typecheck of Guard.Thm13.
4. `[unify-5c-prov]` — Prov predicate + combinators.
5. `[unify-5c-prov-treeeqself]` — encoded treeEqSelfReify in Prov form.
6. `[unify-5c-godel1]` — Prov gsCR -> Prov botEq.
7. `[unify-5c-chain-step1to3]` — chain steps 1-3.
8. `[unify-5c-chain-step4to5]` — chain steps 4-5.
9. `[unify-5c-chainContoGs]` — final assembly.
10. `[unify-5c-godel2]` — godelIIHF by composition.

Each step typechecks independently.  No postulates, no holes.

## Scope NOT in [unify-5c]

- Deleting legacy modules (Step, Provable, BRA, GodelIIBRAv2, the
  non-Unify ThFunTForV3 chain, old ProofEnc) → that's [unify-5d].
- Renaming -Unify → final names → also [unify-5d].
- Classical Gödel I (`Consistent -> Deriv gsCR -> Empty`) → out of
  scope; requires thm14EV3-style recursor.  Consumers who want the
  classical form compose `godelIIHF` with their own Consistent
  hypothesis: `Consistent = ~Prov botEq`, so the contrapositive
  `Consistent -> ~Prov conHFEq` follows directly.

## Revised Gödel II plan (session F re-read of guard15 pages 15-17)

The original §(1)-§(4) plan above envisioned a Prov-level reconstruction
of the entire Gödel II chain, including a Prov-encoded `diagFTargetCR`
and a Prov bridge from Deriv-level `thmT e_G = reify cGSCR` to a Prov.
A closer reading of guard15 Theorems 11-14 shows this is not what Guard
does and it is not necessary for our target either.

### What Guard actually does

- **Theorem 12** (page 16, unconditional):
  `th(D_f(x)) = "f(num x) = f(x)"` as a BRA theorem schema.
- **Theorem 13** (corollary, conditional):
  `f(x) = y ⊃ th(D_f(x)) = "f(num x) = y"`, derived from Thm 12 by
  the congruence of `num` (`a = b ⊢ num(a) = num(b)`).
- **Theorem 14** (Gödel II, pages 16-17): a Deriv-level chain
  (steps 1-5) that builds a BRA-provable implication
    `th(x) = j ⊃ th(<bigExpr>(x)) = "0 = 1"`
  using Thm 13 at several functors, encoded propositional axioms
  (ax(4)-style transitivity `t`, a negation axiom `t'`), and
  p.r. term-builders (`f(x)`, `g(x)`, `h(x)`) that paste encoded
  proofs together via encoded MP.

At the meta level, Guard then argues:  if `th(y) ≠ "0 = 1"` were
provable, substitute into step 5 to derive `th(x) ≠ sub(i,i)` provable,
contradicting Thm 11.

### What this means for our Agda port

Our strict-form `thm13Fun1*` / `thm13Fun2*` in `Guard.Thm13` correspond
to **Guard's Thm 12**, not Thm 13.  The naming is inherited from the
original spec and should be understood accordingly.

The Gödel II chain is a Deriv-level construction; it does not need
Prov-level encodings of `cor` or `diagFTargetCR`.  The Prov level only
appears at the input (unwrap `Prov gsCR`) and output (wrap as
`Prov botEq`).  Pipeline:

```
godelI : Prov (atomic gsCR) -> Prov (atomic botEq)
godelI pG =
  let e_G = provTerm pG
      d_G = provCorr pG                       -- Deriv (thmT e_G = reify cGSCR)
      chain : Deriv ((atomic (eqn (ap1 thmT (var 0)) (reify cGSCR))) imp
                     (atomic (eqn (ap1 thmT <bigExpr (var 0)>) (reify codeBotT))))
      chain = ...                             -- Thm 14 steps 1-5
      inst  = ruleInst 0 e_G chain
      out   : Deriv (atomic (eqn (ap1 thmT <bigExpr e_G>) (reify codeBotT)))
      out   = mp inst d_G
  in mkProv <prov1 of bigExpr e_G> <prov2 ...> out <pass>
```

### Gaps before godelI can be built

1. **Thm 13 IMP form** — corollary of Thm 12 that accepts an arbitrary
   `y` on the RHS.  Requires an object-level analog of Guard's
   `num`-congruence (`a = b ⊃ num(a) = num(b)`).  Our `cor : Fun1` does
   this for reified trees; for general Terms we need either (a) a new
   total functor that computes `reify ∘ code` for arbitrary inputs,
   or (b) restriction to inputs already in reified form.  Open.

2. **Encoded propositional axioms** — Guard's `t` and `t'`.  We have
   `axEqTrans` / `axEqCong1` / `axEqCongL` / `axEqCongR` as
   `Guard.DerivF` primitives, and `axK` / `axS` / `axNeg` for K/S/Neg.
   But we **do not** have matching encoder lemmas
   `encAxEqTrans` / `encAxEqCong*`.  These must be added to
   `Guard.ProofEncUnify` (each ~30 lines mirroring `encAxK`).

3. **Term-builders `f(x)`, `g(x)`, `h(x)`** — specific Fun1 expressions
   that paste encoded proofs via `encMp` and sub-encodings.
   Mechanical once Thm 13 and the encoded axioms are in hand.

4. **Chain assembly** — transcribe guard15 p.17 steps 1-5 at Deriv
   level using ruleInst + mp.

### What can be retired from the original plan

- Prov-encoded `diagFTargetCR` — not needed (use Deriv-level
  `diagFTargetCR` directly inside the chain's Thm 13 step for `substOp`).
- `provTreeEqSelfReify` — the Gödel II chain closes via the encoded
  negation axiom `t'` and ax(4)-style transitivity, not via
  TreeEq-self-reflexivity.  Shipped in [unify-5c-prov-treeeqself]
  but unused by the chain.
- `provCong1` — may still be useful for future Prov-level reasoning
  but not required for godelI in this revised plan.

### Estimated cost

- Thm 13 IMP form (once the num-analog is chosen): ~50-100 lines.
- encAxEqTrans / encAxEqCong* (4 encoders): ~120 lines.
- Term-builders: ~80 lines.
- Chain + assembly: ~100-200 lines.
- **Total**: ~400 lines, significantly less than the 300-500 I flagged
  in session E.

## Open questions to resolve during implementation

1. **codeEqn vs codeFormula:** our `cGSCR = codeEqn gsCR` codes an
   Equation; `codeFormula (atomic gsCR)` codes the wrapped Formula.
   These differ by the `atomic` tag.  Need a small equational bridge
   or restatement — easiest to establish early.

2. **Prov instantiation boilerplate:** for each `provInst` call we
   need `substForm` to produce the right Term.  Establish
   `provInstAtomic : (x : Nat) (t : Term) (a b : Term) -> Prov (atomic (eqn a b)) -> Prov (atomic (eqn (subst x t a) (subst x t b)))` as a convenience wrapper.

3. **`D1 thmT` explicit form:** `thmT` is itself `Rec O thmTStep`.
   `D1 (Rec z s)` needs special handling since the recursion-structure
   case is non-trivial.  May need to treat `D1 thmT` as a primitive
   abbreviation with its own correctness lemma, rather than deriving
   it from the generic Rec case.

4. **Axioms ax(4) and ax(t') in encoded form:** these are classical
   propositional axioms in guard15 but in our DerivF formulation
   they may be either (a) primitive Deriv rules or (b) derivable from
   encAxK/S/Neg + existing constants.  Sketch the derivations before
   committing to a module structure.

## Fresh-session bootstrap

If this work is resumed in a fresh session:

1. Read this document.
2. Read `UNIFIED-DESIGN-REV2.md`.
3. Read `~/.claude/projects/-Users-coquand-CHWISTEK/memory/project_unified_hypfree.md`.
4. Skim `Guard.ThFunTForHF`, `Guard.ProofEncUnify`,
   `Guard.SubstTForPrecompClassicalUnify` for type signatures.
5. Check recent commits: `git log --oneline -20` should show
   [unify-5b-substprecomp] as the most recent Option-G commit
   (commit 9298b61).
6. Start on Guard.Thm13 base cases (I, Fst, Snd, KT) first — these
   are simplest, exercise the encoder machinery, and surface any
   codeEqn/codeFormula bridging issues early.
7. Typecheck with `~/.cabal/bin/agda-2.9.0 --safe --without-K --exact-split Guard/Thm13.agda`.

## Session G discovery (2026-04-23) — Exercise 24 functors and the real structure of Thm 12

After session G's struggle to reconcile Guard's Thm 12 / Thm 13 with our
Agda formalization, the actual structural issue became clear by
re-reading guard15 pages 13-14 (Def 9, Def 10, Def 11, Exercise 24).

### Guard's eight BRA-level functors (Exercise 24)

Guard defines eight primitive-recursive BRA functors that mirror the
syntactic operations of BRA at the Gödel-number level:

- `num(n) = "s^n(0)"`                        — numeral-to-Gödel-numeral
- `sub(J("A", n), "P") = "S^{x_n}_A P|"`     — substitution
- `sbt`, `sbf`                                — term / formula substitution
- `mp("P", "P ⊃ Q") = "Q"`                    — modus ponens
- `ind("P(0)", "P(x_0) ⊃ P(sx_0)") = "P(x_0)"` — induction
- `ax(i) = "<i-th BRA axiom>"`                — axiom indexer

These are BRA FUNCTORS, not meta-level constructs.  Guard's Thm 12
proof (by meta-induction on the length of the definition of a functor)
builds Df(x) as a BRA-level term using `ax`, `mp`, `ind`, `num`, `sub`
applied to specific Gödel numbers of sub-components.  For compound
f = Cgh, D_{Cgh} is built from Dg, Dh inductively.

### What we have vs. what is missing

| Guard Ex 24 | Our Agda | Status |
|-------------|----------|--------|
| `num`       | `cor : Fun1`     | ✓ |
| `sub`, `sbt`, `sbf` | `substOp : Fun2` | ✓ (mostly) |
| `mp`        | `encMp` (meta-level Term builder) + thmT case33 dispatch | **only meta-level; no Fun2** |
| `ind`       | `ruleIndBT` (Deriv primitive) + thmT case28 | **only Deriv + dispatch; no Fun2** |
| `ax`        | `encAxI`, `encAxFst`, ... (meta-level Term builders) + thmT case0..case32 dispatch | **only meta-level; no Fun1 indexed by axiom number** |

The missing five — `mp`, `sbt`, `sbf`, `ind`, `ax` — exist in our
formalization only as META-LEVEL Agda encoders (per-case Term builders
like encAxI, encMp), not as object-level BRA Fun1/Fun2 functors.

### Implication for Thm 12

Guard's Thm 12 proof is a meta-induction that BUILDS Df(x) at the
BRA object level using the Exercise 24 functors — `mp`, `ax`, `ind`,
`num`, `sub` applied to Gödel numbers of sub-components.  Key
property exploited throughout: these functors are TOTAL on BRA
terms, including free variables.  `num(x_i)` is a meaningful
functor application, and `axEqCong1 num` gives num-congruence
internally.

### The only viable path: actually do Exercise 24 (Path A)

A superficial Agda construction
    D_f x := encAxRefl (ap1 cor (ap1 f x))
compiles but has the wrong target (term-level Pair instead of
`reify(codeFormula ...)`) and does not compose with encMp's case33
dispatch.

A meta-level alternative — composing our existing per-primitive-case
`D1I, D1Fst, ..., D1RecLf, D1RecNd` at the Agda level — was
considered and REJECTED: those lemmas each cover a specific input
shape (`D1RecLf` at `x = O`, `D1RecNd` at `x = Pair a b`, etc.).
The Thm 14 chain needs Thm 12 at `x = var 0`, and no per-primitive
lemma covers variables.  Variables aren't a Rec-dispatchable shape,
so there's no way to extend the per-primitive lemmas to cover the
case that matters.

Guard avoids this because `num` is a total BRA functor that handles
variables uniformly via its primitive-recursive definition, and
`axEqCong1 num` extends to all BRA terms.  We inherit none of this
unless we actually introduce BRA analogs of `num`, `mp`, `ax`, `ind`
at the Fun1/Fun2 level.

**The only viable path** is Path A: do Exercise 24 properly.  Until
we have the BRA-level Exercise 24 functors, Thm 12 in our system
cannot be proved in a form usable for the Thm 14 chain.

### Exercise 24 in concrete Agda terms

1. **num as a TOTAL Fun1**.  Our current `cor : Fun1 = Rec falseT
   stepCor` only reduces on reified-tree inputs.  Either extend it
   or add DerivF axioms so that:
       ap1 cor (var n) = reify (code (var n))       -- variable case
       ap1 cor (ap1 f t) = reify (code (ap1 f t))   -- Fun1-app case
       ap1 cor (ap2 g a b) = reify (code (ap2 g a b)) -- Fun2-app case
   These are primitive-recursive defining equations matching Guard's
   Def 10 rules 2-4.  For BRA, they're axioms; for us, axioms in
   DerivF.  Once present, `cong1 cor` + `axEqCong1 cor + mp` give
   num-congruence uniformly.

2. **ax as a Fun1**.  Takes an axiom index (a Nat-code) and produces
   the Gödel number of the axiom.  Can be implemented by Rec-style
   dispatch on the index; each branch emits a specific axiom's code.
   Equivalent to what thmT case0..case32 dispatch already does on
   encoded axioms, but factored out as a separate Fun1 operating on
   indices.

3. **mp as a Fun2**.  Takes `"P"` and `"P ⊃ Q"` (two Gödel numbers)
   and emits `"Q"`.  Decompose the second argument's code to extract
   Q's code and check P-prefix matches.  Equivalent to thmT case33's
   logic, but exposed as a Fun2 so it's callable inside other
   encoded proofs.

4. **ind as a Fun2**.  Takes `"P(0)"` and `"P(x) ⊃ P(sx)"` and emits
   `"P(x)"` (the induction conclusion's code).  Analog of ruleIndBT
   + thmT case28.

5. **sb / sbt / sbf** — substitution functors.  Our existing
   `substOp : Fun2` already covers the basic case (substitution of a
   numeral for x_0 in a formula code).  Generalizations may be
   needed for Thm 14's multiple-variable instantiation steps.

Each functor's definition needs a DerivF axiom (or derived lemma)
asserting its defining equation.  The axioms follow directly from
Exercise 24's specifications [1]-[8].

### Building D_f using Exercise 24 functors

With the BRA functors in hand, Guard's meta-induction on functor
structure becomes constructive Agda code.  For f = Cgh:
    D_{Cgh}(x)  :=  mp (D_h(x)) (... composition involving D_g ...)
Each step is a Fun1/Fun2 application (not a Term-level encoder
composition).  The inductive construction terminates on primitive
functors (s, u, v, θ in Guard; our analogs) whose Df is a closed
numeral — which we CAN construct using encAxRefl at a specific
reified tree.

For our target functor `thmT = Rec O thmTStep`:
- Build D_thmT by meta-induction on thmT's structure.
- Base cases: thmTStep decomposes into specific Fan / IfLf / kF2
  expressions.  Each sub-component has a Df.
- Inductive case (Rec): D_{Rec z s} combines D_z and D_s.
- Final D_thmT is a specific Fun1 built from the above.

Similarly for substOp = RecP stepSubstP.

### Scale estimate

Exercise 24 functors + their correctness axioms: ~500-800 lines
(5 new Fun1/Fun2 definitions + their DerivF axiomatizations +
sanity-check lemmas).

D_thmT + D_substOp via meta-induction using Ex 24 functors:
~500-800 lines (recursive construction following Guard's proof
structure).

Thm 13 (conditional corollary) given D_f: ~50 lines.

Thm 14 chain + godelI + godelII: ~300-500 lines (encoder composition
once Thm 12/13 are in hand).

Total: ~1500-2000 lines.  This is genuinely the size of Guard's
Exercise 24 + Theorems 11-14.  Large but unavoidable for a faithful
formalisation.

### What was shipped in session G (retained, on critical path)

- `[unify-5c-enc-eq-axioms]`  n34 tag + encAxEqTrans encoder
- `[unify-5c-enc-t]`          encoded axiom  t
- `[unify-5c-enc-exfalso]`    n35 tag + encAxExFalso encoder
- `[unify-5c-enc-tprime]`     axExFalso DerivF primitive + encoded t'

All useful — `t` and `t'` will be used inside Thm 14 step 4/5 chain
once D_thmT / D_substOp exist.

### What was shipped in session G (NOT on critical path; retained for reference)

- `[unify-5c-thm12-thm13-uniform]`  superficial Thm 12/13 (commit ed4727d).
  Files `Guard/Thm12Uniform.agda` and `Guard/Thm13Uniform.agda`.
  Compiles but trivializes Thm 12 at the wrong level.  Does not
  compose with the chain.  Kept as a reference for "what went wrong"
  during session G's back-and-forth.  A fresh session should replace
  these with the Exercise 24 / Path A approach and can safely delete
  these files once Path A reaches parity.

### Recommended next-session handoff

A fresh session should:

1. Re-read guard15 pp. 13-17 (Def 9-11, Ex 24, Thm 11-14).  These
   pages give the exact specifications needed.
2. Read this "Session G discovery" section for context on why the
   previous superficial approach failed and why Exercise 24 is the
   only viable path.
3. Read `Guard/Thm13.agda` — understand the 19 per-primitive D1/D2
   lemmas already present.  These are useful as BASE CASES for Df
   construction at primitive functors, but do not by themselves
   suffice for compound functors like thmT / substOp.
4. Start by implementing Exercise 24 functors:
    a. Extend `cor` (or add DerivF axioms) so that it's total on
       Terms — covering `var n`, `ap1 f t`, `ap2 g a b` shapes.
       Match Guard's Def 10 rules 2-4 exactly.
    b. Define `mp : Fun2` per Ex 24 [1] + its defining-equation
       axiom.
    c. Define `ax : Fun1` per Ex 24 [6] + its defining-equation
       axioms (one per axiom index).
    d. Define `ind : Fun2` per Ex 24 [5] + defining equation.
5. Build D_thmT and D_substOp via meta-induction using these
   functors, following Guard's proof of Thm 12.
6. Thm 13 (conditional) as a ~50 line wrapper.
7. Thm 14 chain + godelI + godelII — mostly mechanical encoder
   composition once Thm 12/13 are done.
